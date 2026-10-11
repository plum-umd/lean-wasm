#!/usr/bin/env python3
"""Measure specification, array heap, and explicit stack in fresh processes."""
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
BACKENDS = ['spec', 'heap', 'machine']
FIELDS = ['backend', 'workload', 'iterations', 'depth', 'fuel', 'execution_ns',
          'input_conversion_ns', 'output_conversion_ns', 'heap_size']


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repeat', type=int, default=7)
    parser.add_argument('--hardware', default=platform.machine())
    parser.add_argument('--output', type=Path, default=ROOT / 'benchmarks/explicit-stack')
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error('repeat must be positive')
    subprocess.run(['lake', 'build', 'wasm-stack-bench'], cwd=ROOT, check=True)
    cases = [(kind, n, 0) for kind in
             ['allocate', 'allocate-read', 'linked', 'read-early', 'read-middle',
              'read-late', 'control'] for n in [1000, 4000, 16000]]
    cases += [(kind, 1000, depth) for kind in
              ['blocks', 'calls', 'tail-calls', 'handlers', 'unwind']
              for depth in [0, 4, 16, 64, 256]]
    args.output.mkdir(parents=True, exist_ok=True)
    sources = [ROOT / 'StackBenchMain.lean', ROOT / 'lakefile.toml', Path(__file__).resolve(),
               *sorted((ROOT / 'Wasm/Fast').glob('*.lean'))]
    metadata = dict(timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                    revision=command('git', 'rev-parse', 'HEAD'),
                    working_tree=command('git', 'status', '--porcelain'),
                    toolchain=command('lake', 'env', 'lean', '--version'),
                    hardware=args.hardware, platform=platform.platform(), repeat=args.repeat,
                    cases=cases, warmups_per_backend_case=1, fresh_process_per_sample=True,
                    source_sha256={str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                                   for p in sources})
    (args.output / 'metadata.json').write_text(json.dumps(metadata, indent=2) + '\n')
    binary = str(ROOT / '.lake/build/bin/wasm-stack-bench')
    rows = []
    with (args.output / 'samples.csv').open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=['repeat'] + FIELDS, lineterminator='\n')
        writer.writeheader()
        for kind, n, depth in cases:
            for backend in BACKENDS:
                command(binary, backend, kind, str(n), str(depth))
            for repetition in range(args.repeat):
                order = BACKENDS[repetition % 3:] + BACKENDS[:repetition % 3]
                if repetition % 2:
                    order = list(reversed(order))
                for backend in order:
                    fields = command(binary, backend, kind, str(n), str(depth)).split(',')
                    if len(fields) != len(FIELDS):
                        raise RuntimeError(fields)
                    row = dict(zip(FIELDS, fields), repeat=repetition)
                    for key in FIELDS[2:]:
                        row[key] = int(row[key])
                    rows.append(row)
                    writer.writerow(row)
                    stream.flush()
            print(f'measured {kind}/{n}/{depth}', flush=True)
    summary = ['# Explicit stack benchmark', '', f'Hardware: {args.hardware}.',
               f'Toolchain: {metadata["toolchain"]}.', '',
               'Each cell is the median of fresh-process samples, with one discarded warm-up.',
               'Backend order rotates and reverses. Execution excludes preparation, parsing,',
               'validation and boundary conversions. Total includes both conversions.', '',
               '| Workload | Iterations | Depth | Spec ms | Heap ms | Machine ms | Heap/machine | Spec/machine total | Machine range ms |',
               '| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |']
    for kind, n, depth in cases:
        samples = {b: [r for r in rows if (r['backend'], r['workload'], r['iterations'], r['depth'])
                       == (b, kind, n, depth)] for b in BACKENDS}
        med = {b: statistics.median(r['execution_ns'] for r in samples[b]) for b in BACKENDS}
        total = {b: statistics.median(sum(r[k] for k in
                 ['execution_ns', 'input_conversion_ns', 'output_conversion_ns'])
                 for r in samples[b]) for b in BACKENDS}
        spread = [r['execution_ns'] / 1e6 for r in samples['machine']]
        summary.append(f'| {kind} | {n} | {depth} | {med["spec"]/1e6:.3f} | '
                       f'{med["heap"]/1e6:.3f} | {med["machine"]/1e6:.3f} | '
                       f'{med["heap"]/med["machine"]:.2f}× | '
                       f'{total["spec"]/total["machine"]:.2f}× | '
                       f'{min(spread):.3f}–{max(spread):.3f} |')
    (args.output / 'summary.md').write_text('\n'.join(summary) + '\n')


if __name__ == '__main__':
    main()
