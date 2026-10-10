#!/usr/bin/env python3
"""Build project modules in import order to bound concurrent compiler memory.

Lake still manages external dependencies and incremental build traces. Fetch the
Mathlib cache first (`lake exe cache get`) on a fresh checkout.
"""
from pathlib import Path
import argparse
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
seen: set[str] = set()
order: list[str] = []


def visit(module: str) -> None:
    if module in seen:
        return
    seen.add(module)
    source = (ROOT / (module.replace(".", "/") + ".lean")).read_text()
    for line in source.splitlines():
        match = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(.+)", line)
        if match:
            for dependency in match[1].split("--", 1)[0].split():
                if dependency == "LogSobolev" or dependency.startswith("LogSobolev."):
                    visit(dependency)
    order.append(module)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--from-module", help="Resume at this module in dependency order")
    args = parser.parse_args()
    visit("LogSobolev")
    if args.from_module is not None and args.from_module not in order:
        parser.error(f"Unknown project module: {args.from_module}")
    start = order.index(args.from_module) if args.from_module else 0
    for index, module in enumerate(order, 1):
        if index <= start:
            continue
        print(f"[{index}/{len(order)}] {module}", flush=True)
        subprocess.run(["lake", "build", module], cwd=ROOT, check=True)
