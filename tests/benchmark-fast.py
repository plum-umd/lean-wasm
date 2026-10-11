#!/usr/bin/env python3
"""Compare compiled executors with fresh state, alternating order, and separate conversions."""
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
WORKLOADS = ["heap-allocate", "heap-read-early", "heap-read-middle", "heap-read-late",
             "allocate", "allocate-read", "linked", "read-early", "read-middle", "read-late",
             "control"]
FIELDS = ["backend", "workload", "size", "fuel", "execution_ns", "input_conversion_ns",
          "output_conversion_ns", "heap_size"]


def command(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sizes", nargs="+", type=int, default=[1000, 2000, 4000, 8000, 16000])
    parser.add_argument("--repeat", type=int, default=7)
    parser.add_argument("--workloads", nargs="+", choices=WORKLOADS, default=WORKLOADS)
    parser.add_argument("--output", type=Path, default=ROOT / ".cache" / "benchmarks")
    parser.add_argument("--hardware", help="CPU model override when system queries are restricted")
    args = parser.parse_args()
    if args.repeat < 1 or any(n < 1 or n > 1000000 for n in args.sizes):
        parser.error("repeat must be positive and sizes must be in 1..1000000")
    subprocess.run(["lake", "build", "wasm-bench"], cwd=ROOT, check=True)
    args.output.mkdir(parents=True, exist_ok=True)
    metadata = {
        "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "revision": command("git", "rev-parse", "HEAD"),
        "branch": command("git", "branch", "--show-current"),
        "working_tree": command("git", "status", "--porcelain"),
        "toolchain": command("lake", "env", "lean", "--version"),
        "platform": platform.platform(), "machine": platform.machine(),
        "processor": platform.processor(), "sizes": args.sizes, "repeat": args.repeat,
        "workloads": args.workloads, "warmups_per_backend_case": 1,
        "timing": "monotonic nanoseconds inside compiled executable; IO evaluation barriers",
        "fresh_process_per_sample": True,
    }
    sources = [ROOT / "BenchMain.lean", ROOT / "lakefile.toml", Path(__file__).resolve(),
               *sorted((ROOT / "Wasm" / "Fast").glob("*.lean"))]
    metadata["source_sha256"] = {
        str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sources
    }
    if args.hardware:
        metadata["hardware"] = args.hardware
    elif platform.system() == "Darwin":
        try:
            metadata["hardware"] = command("sysctl", "-n", "machdep.cpu.brand_string")
        except (OSError, subprocess.CalledProcessError):
            metadata["hardware"] = "CPU model unavailable; see platform and machine"
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    binary = str(ROOT / ".lake" / "build" / "bin" / "wasm-bench")
    rows = []
    with (args.output / "samples.csv").open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=["repeat"] + FIELDS)
        writer.writeheader()
        for kind in args.workloads:
            for size in args.sizes:
                for backend in ("spec", "fast"):
                    command(binary, backend, kind, str(size))  # discarded warm-up
                for repetition in range(args.repeat):
                    order = ("spec", "fast") if repetition % 2 == 0 else ("fast", "spec")
                    for backend in order:
                        fields = command(binary, backend, kind, str(size)).split(",")
                        if len(fields) != len(FIELDS):
                            raise RuntimeError(f"unexpected benchmark output: {fields}")
                        row = dict(zip(FIELDS, fields), repeat=repetition)
                        for key in FIELDS[2:]:
                            row[key] = int(row[key])
                        rows.append(row)
                        writer.writerow(row)
                        stream.flush()
                print(f"measured {kind}/{size}", flush=True)
    summary = ["# Array heap benchmark", "", f"Machine: {metadata.get('hardware', metadata['platform'])}",
               f"Toolchain: {metadata['toolchain']}",
               f"Source: `{metadata['revision']}` on `{metadata['branch']}` plus the recorded working tree.",
               "", "Times exclude setup, parsing, validation, and correctness checks. End-to-end includes",
               "execution and both explicit representation conversions. Samples run in fresh processes,",
               "with alternating backend order, one discarded warm-up and seven repetitions by default.",
               "Spread is the minimum–maximum execution time. Speedup is spec median / fast median.",
               "", "| Workload | Size | Spec ms | Fast ms | Speedup | End-to-end speedup | Fast spread ms |",
               "| --- | ---: | ---: | ---: | ---: | ---: | ---: |"]
    for kind in args.workloads:
        for size in args.sizes:
            samples = {b: [r for r in rows if r["backend"] == b and r["workload"] == kind and
                           r["size"] == size] for b in ("spec", "fast")}
            med = {b: statistics.median(r["execution_ns"] for r in samples[b]) for b in samples}
            total = {b: statistics.median(r["execution_ns"] + r["input_conversion_ns"] +
                                         r["output_conversion_ns"] for r in samples[b]) for b in samples}
            spread = [r["execution_ns"] / 1e6 for r in samples["fast"]]
            summary.append(f"| {kind} | {size} | {med['spec']/1e6:.3f} | {med['fast']/1e6:.3f} | "
                           f"{med['spec']/med['fast']:.2f}× | {total['spec']/total['fast']:.2f}× | "
                           f"{min(spread):.3f}–{max(spread):.3f} |")
    (args.output / "summary.md").write_text("\n".join(summary) + "\n")
    print(f"Results: {args.output / 'summary.md'}")


if __name__ == "__main__":
    main()
