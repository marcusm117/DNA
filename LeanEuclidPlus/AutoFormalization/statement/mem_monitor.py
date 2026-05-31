#!/usr/bin/env python
"""Standalone memory monitor for the autoformalization runs.

Passive observer: samples the RSS of a root process and its entire descendant
tree every N seconds and appends a row to a CSV. It does NOT touch the pipeline
or its results — it only reads /proc via psutil. Started/stopped by the run
script (reproduce_sonnet.sh); exits on its own when the root process is gone.

Usage:
    python mem_monitor.py --root-pid $$ --out result_dir/mem_usage.csv --interval 15
"""

import argparse
import csv
import os
import time

import psutil


def total_tree_rss(root: psutil.Process) -> tuple[float, int, float]:
    """Return (total_rss_gb, num_procs, top_single_proc_rss_gb) for root + descendants.

    Individual processes that vanish or deny access mid-sample are skipped, so a
    racing fork/exit never crashes the monitor.
    """
    procs = [root]
    try:
        procs.extend(root.children(recursive=True))
    except (psutil.NoSuchProcess, psutil.AccessDenied):
        pass

    total = 0
    top = 0
    counted = 0
    for p in procs:
        try:
            rss = p.memory_info().rss
        except (psutil.NoSuchProcess, psutil.AccessDenied, psutil.ZombieProcess):
            continue
        total += rss
        top = max(top, rss)
        counted += 1

    gb = 1024 ** 3
    return total / gb, counted, top / gb


def main() -> None:
    parser = argparse.ArgumentParser(description="Sample process-tree RSS to a CSV.")
    parser.add_argument("--root-pid", type=int, required=True, help="PID whose subtree is measured")
    parser.add_argument("--out", type=str, required=True, help="CSV output path")
    parser.add_argument("--interval", type=float, default=15.0, help="Seconds between samples")
    args = parser.parse_args()

    os.makedirs(os.path.dirname(os.path.abspath(args.out)), exist_ok=True)

    try:
        root = psutil.Process(args.root_pid)
    except psutil.NoSuchProcess:
        print(f"[mem_monitor] root pid {args.root_pid} not found; exiting.")
        return

    start = time.time()
    # Line-buffered so the CSV is tail-able live.
    with open(args.out, "w", encoding="utf-8", newline="", buffering=1) as f:
        writer = csv.writer(f)
        writer.writerow(["timestamp", "elapsed_sec", "total_rss_gb", "num_procs", "top_proc_rss_gb"])

        while True:
            if not root.is_running() or root.status() == psutil.STATUS_ZOMBIE:
                break
            try:
                total_gb, n, top_gb = total_tree_rss(root)
            except psutil.NoSuchProcess:
                break
            now = time.time()
            writer.writerow([
                time.strftime("%Y-%m-%dT%H:%M:%S"),
                round(now - start, 1),
                round(total_gb, 3),
                n,
                round(top_gb, 3),
            ])
            time.sleep(args.interval)

    print(f"[mem_monitor] root pid {args.root_pid} exited; monitor stopping.")


if __name__ == "__main__":
    main()
