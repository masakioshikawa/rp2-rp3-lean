#!/usr/bin/env python3
"""Gate changes to the elaborated meanings of RP3 public statements.

Normal verification compares the observed inventory with the reviewed baseline.
Use --write-baseline explicitly only after reviewing an intended semantic change.
The separate dependency audit checks theorem proofs and their axiom policy.
"""
from __future__ import annotations

import argparse
import difflib
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]


def fingerprint(record):
    result = {k: record[k] for k in ("name", "kind", "level_parameters")}
    for key in ("type", "value"):
        value = record[key]
        result[key + "_sha256"] = (None if value is None else
            hashlib.sha256(value.encode("utf-8")).hexdigest())
    return result


def inventory(path):
    records = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        item = json.loads(line)
        declarations = sorted((fingerprint(d) for d in item["declarations"]),
                              key=lambda d: d["name"])
        if len({d["name"] for d in declarations}) != len(declarations):
            raise ValueError("Duplicate semantic declaration")
        records.append({"root": fingerprint(item["root"]),
                        "declarations": declarations})
    expected_roots = [s.strip() for s in
        (ROOT / "verification/rp3-semantic-roots.txt").read_text().splitlines()
        if s.strip() and not s.lstrip().startswith("#")]
    if [r["root"]["name"] for r in records] != expected_roots:
        raise ValueError("Semantic inventory roots differ from the reviewed root list")
    return {"format": 1, "roots": records}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("observed", type=Path)
    parser.add_argument("--baseline", type=Path,
                        default=ROOT / "verification/rp3-semantic-baseline.json")
    parser.add_argument("--write-baseline", action="store_true")
    args = parser.parse_args()
    actual = inventory(args.observed)
    rendered = json.dumps(actual, indent=2, ensure_ascii=False) + "\n"
    if args.write_baseline:
        args.baseline.write_text(rendered)
        print("Wrote the semantic baseline for explicit review.")
        return 0
    expected = json.loads(args.baseline.read_text())
    if actual != expected:
        old = json.dumps(expected, indent=2, ensure_ascii=False).splitlines()
        new = rendered.splitlines()
        print("Semantic definitions or statement types changed; review is required.",
              file=sys.stderr)
        print("\n".join(list(difflib.unified_diff(old, new,
            fromfile="reviewed baseline", tofile="observed semantics"))[:100]),
            file=sys.stderr)
        return 1
    print(f"SEMANTIC_GATE_SUCCESS: {len(actual['roots'])} public statement closures match.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
