#!/usr/bin/env python3
"""Measure the unified machine with certified or native execution policy."""
import argparse
import csv
import datetime
import hashlib
import json
import platform
import statistics
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HEAP = ['allocate', 'allocate-read', 'linked', 'read-early', 'read-middle', 'read-late', 'control']
DEPTH = ['blocks', 'calls', 'tail-calls', 'handlers', 'unwind']
FIELDS = ['policy', 'workload', 'iterations', 'depth', 'fuel', 'execution_ns',
          'input_conversion_ns', 'output_conversion_ns', 'heap_size']


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sizes', nargs='+', type=int, default=[1000, 4000, 16000])
    parser.add_argument('--depths', nargs='+', type=int, default=[0, 4, 16, 64, 256])
    parser.add_argument('--iterations', type=int, default=1000, help='iterations for depth cases')
    parser.add_argument('--repeat', type=int, default=7)
    parser.add_argument('--policies', nargs='+', choices=['certified', 'native'],
                        default=['certified', 'native'])
    parser.add_argument('--workloads', nargs='+', choices=HEAP + DEPTH, default=HEAP + DEPTH)
    parser.add_argument('--output', type=Path, default=ROOT / '.cache/benchmarks')
    parser.add_argument('--hardware', default=platform.machine())
    args = parser.parse_args()
    if args.repeat < 1 or any(n < 1 or n > 1000000 for n in args.sizes + [args.iterations]):
        parser.error('repeat must be positive; iteration counts must be in 1..1000000')
    if any(d < 0 or d > 512 for d in args.depths):
        parser.error('depths must be in 0..512')
    subprocess.run(['lake', 'build', 'wasm-bench'], cwd=ROOT, check=True)
    cases = [(kind, n, 0) for kind in args.workloads if kind in HEAP for n in args.sizes]
    cases += [(kind, args.iterations, d) for kind in args.workloads if kind in DEPTH
              for d in args.depths]
    args.output.mkdir(parents=True, exist_ok=True)
    sources = [ROOT / 'BenchMain.lean', ROOT / 'lakefile.toml', Path(__file__).resolve(),
               ROOT / 'Wasm/Configuration.lean', ROOT / 'Wasm/ConfigurationSemantics.lean',
               ROOT / 'Wasm/NativeExecution.lean', *sorted((ROOT / 'Wasm/Fast').glob('*.lean'))]
    metadata = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    revision=command('git', 'rev-parse', 'HEAD'),
                    working_tree=command('git', 'status', '--porcelain'),
                    toolchain=command('lake', 'env', 'lean', '--version'),
                    hardware=args.hardware, platform=platform.platform(), repeat=args.repeat,
                    cases=cases, policies=args.policies, warmups_per_policy_case=1,
                    fresh_process_per_sample=True,
                    source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sources})
    (args.output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    binary = str(ROOT / '.lake/build/bin/wasm-bench')
    rows = []
    with (args.output / 'samples.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['repeat'] + FIELDS, lineterminator='\n')
        writer.writeheader()
        for kind, n, depth in cases:
            for policy in args.policies:
                command(binary, policy, kind, str(n), str(depth))
            for repetition in range(args.repeat):
                order = args.policies if repetition % 2 == 0 else list(reversed(args.policies))
                for policy in order:
                    fields = command(binary, policy, kind, str(n), str(depth)).split(',')
                    if len(fields) != len(FIELDS):
                        raise RuntimeError(fields)
                    row = dict(zip(FIELDS, fields), repeat=repetition)
                    for key in FIELDS[2:]:
                        row[key] = int(row[key])
                    rows.append(row)
                    writer.writerow(row)
                    stream.flush()
            print(f'measured {kind}/{n}/{depth}', flush=True)
    summary = ['# Unified executor benchmark', '', f'Hardware: {args.hardware}.',
               f'Toolchain: {metadata["toolchain"]}.', '',
               'Both policies use the same explicit machine and fuel loop. Native policy adds',
               'float/host extensions and call-depth limits; these workloads need no native ops.',
               'Cells report fresh-process medians after one discarded warm-up per case/policy.',
               'Execution excludes setup and boundary conversions; total includes both conversions.', '',
               '| Policy | Workload | Iterations | Depth | Execution ms | Total ms | Execution range ms |',
               '| --- | --- | ---: | ---: | ---: | ---: | ---: |']
    for kind, n, depth in cases:
        for policy in args.policies:
            samples = [r for r in rows if (r['policy'], r['workload'], r['iterations'], r['depth'])
                       == (policy, kind, n, depth)]
            median = statistics.median(r['execution_ns'] for r in samples) / 1e6
            total = statistics.median(sum(r[k] for k in
                    ['execution_ns', 'input_conversion_ns', 'output_conversion_ns'])
                    for r in samples) / 1e6
            spread = [r['execution_ns'] / 1e6 for r in samples]
            summary.append(f'| {policy} | {kind} | {n} | {depth} | {median:.3f} | {total:.3f} | '
                           f'{min(spread):.3f}–{max(spread):.3f} |')
    (args.output / 'summary.md').write_text('\n'.join(summary) + '\n')
    print(f'Results: {args.output / "summary.md"}')


if __name__ == '__main__':
    main()
