#!/usr/bin/env python3
"""HISTORICAL LEAN 4.34.1 TOOL: use PALOMAR.md for this branch.

Compile the pinned project and check its public proof dependencies.

Run from any directory. No `lake update` is run. Each Lean process is serial
and single threaded. Fresh-source compilation is the default; --resume only
reuses successful commands when the complete input snapshot and any generated
object hashes match. The audit program is not part of the proof library.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(value, indent=2) + "\n")
    temporary.replace(path)


def modules_in_order() -> list[tuple[str, Path]]:
    result, visiting, visited = [], set(), set()

    def visit(name):
        if name in visiting:
            raise RuntimeError(f"Cyclic project import: {name}")
        if name in visited:
            return
        visiting.add(name)
        source = Path(name.replace(".", "/") + ".lean")
        for line in (ROOT / source).read_text().splitlines():
            if line.startswith("import "):
                for dependency in line.split()[1:]:
                    if dependency == "RP2" or dependency.startswith("RP2."):
                        visit(dependency)
        visiting.remove(name)
        visited.add(name)
        result.append((name, source))

    visit("RP2")
    expected = {p.relative_to(ROOT) for p in (ROOT / "RP2").rglob("*.lean")} | {Path("RP2.lean")}
    reached = {source for _, source in result}
    if reached != expected:
        raise RuntimeError("Project sources outside RP2's import closure: "
                           + ", ".join(map(str, sorted(expected - reached))))
    return result


def check_configuration():
    pins = json.loads((ROOT / "verification/dependency-pins.json").read_text())
    if (ROOT / "lean-toolchain").read_text().strip() != pins["lean_toolchain"]:
        raise RuntimeError("lean-toolchain differs from dependency-pins.json")
    if sha256(ROOT / "lake-manifest.json") != pins["manifest_sha256"]:
        raise RuntimeError("The pinned lake-manifest.json changed")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    actual = {p["name"]: p["rev"] for p in manifest["packages"]}
    if actual != pins["packages"]:
        raise RuntimeError("Manifest package revisions differ from the release pins")
    return pins


def snapshot() -> dict[str, str]:
    paths = [p for p in ROOT.rglob("*.lean") if ".lake" not in p.parts
             and "verification" not in p.relative_to(ROOT).parts]
    paths += [ROOT / p for p in (
        "verification/AuditEnvironment.lean", "verification/public-theorems.txt",
        "verification/dependency-pins.json", "lean-toolchain", "lakefile.toml",
        "lake-manifest.json", "bundle.py", "scripts/verify.py")]
    return {str(p.relative_to(ROOT)): sha256(p) for p in sorted(set(paths))}


class Runner:
    def __init__(self, args, source_hashes):
        self.directory = args.output.resolve()
        self.directory.mkdir(parents=True, exist_ok=True)
        self.env = dict(os.environ, LEAN_NUM_THREADS="1")
        self.timeout = args.timeout
        self.input_hash = hashlib.sha256(
            json.dumps(source_hashes, sort_keys=True).encode()).hexdigest()
        self.records = []
        self.previous = {}
        summary_path = self.directory / "summary.json"
        if args.resume and summary_path.exists():
            old = json.loads(summary_path.read_text())
            if old.get("input_snapshot_sha256") == self.input_hash:
                self.previous = {r["label"]: r for r in old.get("commands", [])}
        self.summary = {
            "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "input_snapshot_sha256": self.input_hash,
            "source_sha256": source_hashes,
            "environment": {"LEAN_NUM_THREADS": "1"},
            "commands": self.records,
            "result": "running",
        }
        self.save()

    def save(self):
        write_json(self.directory / "summary.json", self.summary)

    def run(self, label, command, outputs=(), *, env=None, resume=True):
        old = self.previous.get(label)
        if resume and old and old.get("exit_code") == 0 and old["command"] == command:
            expected = old.get("output_sha256", {})
            old_log = self.directory / old["log"]
            if old_log.is_file() and sha256(old_log) == old.get("log_sha256") and all(
                   (ROOT / p).is_file() and sha256(ROOT / p) == digest
                   for p, digest in expected.items()):
                if set(expected) == set(map(str, outputs)):
                    old["reused_same_snapshot"] = True
                    self.records.append(old)
                    self.save()
                    print(f"REUSE {label}", flush=True)
                    return old_log.read_text()
        print(f"RUN   {label}", flush=True)
        log_path = self.directory / f"{label}.log"
        started_utc = dt.datetime.now(dt.timezone.utc).isoformat()
        started = time.monotonic()
        timed_out = False
        with log_path.open("w") as log:
            try:
                process = subprocess.Popen(command, cwd=ROOT, env=env or self.env,
                    stdout=log, stderr=subprocess.STDOUT, start_new_session=(os.name == "posix"))
                try:
                    exit_code = process.wait(timeout=self.timeout)
                except subprocess.TimeoutExpired:
                    if os.name == "posix":
                        os.killpg(process.pid, signal.SIGKILL)
                    else:
                        process.kill()
                    process.wait()
                    timed_out, exit_code = True, 124
                    log.write(f"\nVerification timeout after {self.timeout} seconds.\n")
            except OSError as exc:
                exit_code = 127
                log.write(f"Unable to run command: {exc}\n")
        record = {
            "label": label, "command": command, "exit_code": exit_code,
            "started_utc": started_utc,
            "completed_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
            "elapsed_seconds": round(time.monotonic() - started, 3),
            "timed_out": timed_out, "log": log_path.name,
            "log_sha256": sha256(log_path),
            "output_sha256": {str(p): sha256(ROOT / p) for p in outputs
                              if (ROOT / p).is_file()},
        }
        self.records.append(record)
        self.save()
        if exit_code:
            raise RuntimeError(f"{label} failed (exit {exit_code}); see {log_path}")
        return log_path.read_text()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-cache", action="store_true",
                        help="Fetch cache using the existing pinned manifest")
    parser.add_argument("--standalone", action="store_true",
                        help="Also compile the complete standalone source")
    parser.add_argument("--replay", action="store_true",
                        help="Replay the public dependency closure into an empty kernel")
    parser.add_argument("--replay-standalone", action="store_true",
                        help="Also leanchecker-replay the newly compiled standalone object")
    parser.add_argument("--inventory", action="store_true",
                        help="Record every declaration in the public dependency closure")
    parser.add_argument("--resume", action="store_true",
                        help="Reuse successful checks only for the identical input snapshot")
    parser.add_argument("--output", type=Path, default=ROOT / "verification/latest")
    parser.add_argument("--timeout", type=int, default=1800,
                        help="Per-command timeout in seconds (default 1800)")
    args = parser.parse_args()
    pins = check_configuration()
    runner = Runner(args, snapshot())
    try:
        version = runner.run("lean-version", ["lean", "--version"], resume=False)
        requested = pins["lean_toolchain"].split(":v")[-1]
        if not re.search(r"\bversion " + re.escape(requested) + r"(?:,|\s)", version):
            raise RuntimeError(f"Wrong Lean binary for {pins['lean_toolchain']}: {version}")
        if args.fetch_cache:
            runner.run("dependency-cache", ["lake", "exe", "cache", "get"])
        check_configuration()
        for package, revision in pins["packages"].items():
            package_path = str(Path(".lake/packages") / package)
            actual = runner.run("revision-" + package,
                ["git", "-C", package_path, "rev-parse", "HEAD"], resume=False).strip()
            if actual != revision:
                raise RuntimeError(f"Incorrect dependency checkout: {package}")
            dirty = runner.run("clean-" + package,
                ["git", "-C", package_path, "status", "--porcelain", "--untracked-files=all"],
                resume=False).strip()
            if dirty:
                raise RuntimeError(f"Modified or untracked dependency files: {package}")
        runner.run("bundle-freshness", [sys.executable, "bundle.py", "--check"])
        ordered = modules_in_order()
        runner.summary["module_count"] = len(ordered)
        for name, source in ordered:
            output = Path(".lake/build/lib/lean") / source.with_suffix(".olean")
            (ROOT / output).parent.mkdir(parents=True, exist_ok=True)
            runner.run("module-" + name,
                ["lake", "env", "lean", "-j1",
                 "-o", str(output), str(source)], [output])
        runner.run("semantic-witnesses",
            ["lake", "env", "lean", "-j1", "SemanticWitnesses.lean"],
            resume=False)
        runner.run("readable-axioms",
            ["lake", "env", "lean", "-j1", "AxiomAudit.lean"], resume=False)
        audit = ["lake", "env", "lean", "-j1", "--run", "verification/AuditEnvironment.lean"]
        if args.replay:
            audit.append("--replay")
        if args.inventory:
            audit.append("--inventory")
        audit_log = runner.run("public-dependencies", audit, resume=False)
        if "DEPENDENCY_AUDIT_SUCCESS" not in audit_log:
            raise RuntimeError("Missing successful dependency-audit marker")
        if args.replay and "FRESH_REPLAY_SUCCESS" not in audit_log:
            raise RuntimeError("Missing successful empty-environment replay marker")
        if args.standalone or args.replay_standalone:
            object_dir = Path(".lake/verification/standalone")
            (ROOT / object_dir).mkdir(parents=True, exist_ok=True)
            output = object_dir / "RP2-Formalization.olean"
            runner.run("standalone-source",
                ["lake", "env", "lean", "-j1", "-o", str(output),
                 "RP2-Formalization.lean"], [output])
            if args.replay_standalone:
                # Put the newly compiled object first, ahead of every Lake path.
                lake_path = runner.run("lake-lean-path", ["lake", "env", "printenv", "LEAN_PATH"],
                                       resume=False).strip()
                env = dict(runner.env)
                env["LEAN_PATH"] = str(object_dir) + os.pathsep + lake_path
                runner.run("standalone-kernel-replay",
                    ["leanchecker", "-v", "«RP2-Formalization»"], env=env, resume=False)
        check_configuration()
        if snapshot() != runner.summary["source_sha256"]:
            raise RuntimeError("Source files changed during verification")
        runner.summary["result"] = "passed"
        runner.summary["completed_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        runner.save()
        print(f"PASS  Verification complete: {runner.directory / 'summary.json'}")
        return 0
    except Exception as exc:
        runner.summary["result"] = "failed"
        runner.summary["error"] = str(exc)
        runner.save()
        print(f"FAIL  {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
