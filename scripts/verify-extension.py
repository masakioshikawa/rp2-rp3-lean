#!/usr/bin/env python3
"""HISTORICAL LEAN 4.34.1 TOOL: use PALOMAR.md for this branch.

Validate v0.3 after building the immutable v0.2 baseline.

For a fresh checkout, scripts/verify.py is the full reproduction entry point.
This release-specific command records the baseline source comparison, freshly
compiles every changed/new module, audits and replays all public dependencies,
and freshly compiles and kernel-replays the complete standalone source.
"""
import argparse
import datetime as dt
import importlib.util
from pathlib import Path
import os
import sys

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("verification_runner", ROOT / "scripts/verify.py")
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base-project", type=Path, required=True)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    args.output = ROOT / "verification/latest"
    args.timeout = 1800
    base = args.base_project.resolve()
    pins = v.check_configuration()
    ordered = v.modules_in_order()
    changed, unchanged = [], {}
    for name, source in ordered:
        if (base / source).is_file() and v.sha256(base/source) == v.sha256(ROOT/source):
            unchanged[str(source)] = v.sha256(ROOT/source)
        else:
            changed.append((name, source))
        output = ROOT / ".lake/build/lib/lean" / source.with_suffix(".olean")
        if not output.is_file():
            raise RuntimeError(f"Missing baseline/extension module object: {output}")
    def current_snapshot():
        result = v.snapshot()
        for relative in ["scripts/verify-extension.py", "verification/AuditFinalUnion.lean"]:
            result[relative] = v.sha256(ROOT / relative)
        return result
    runner = v.Runner(args, current_snapshot())
    runner.summary["validation_mode"] = "extension plus fresh complete standalone"
    runner.summary["module_count"] = len(ordered)
    runner.summary["baseline_unchanged_source_sha256"] = unchanged
    runner.summary["baseline_archive_sha256"] = "712ae0f2fa7c310ca6b695f3eab64441e1e01111e3aac669f93ee28ebf8e5895"
    runner.summary["baseline_note"] = "All 61 v0.2 modules rebuilt serially before extension validation; logs retained in verification/baseline-rebuild."
    runner.save()
    try:
        runner.run("lean-version", ["lean", "--version"], resume=False)
        for package, revision in pins["packages"].items():
            directory = str(Path(".lake/packages")/package)
            actual = runner.run("revision-"+package,["git","-C",directory,"rev-parse","HEAD"],resume=False).strip()
            if actual != revision:
                raise RuntimeError(f"Wrong dependency revision: {package}")
            dirty = runner.run("clean-"+package,["git","-C",directory,"status","--porcelain","--untracked-files=all"],resume=False).strip()
            if dirty:
                raise RuntimeError(f"Dirty dependency: {package}")
        runner.run("bundle-freshness", [sys.executable,"bundle.py","--check"])
        for name, source in changed:
            output=Path(".lake/build/lib/lean")/source.with_suffix(".olean")
            runner.run("module-"+name,["lake","env","lean","-j1","-DElab.async=false","-o",str(output),str(source)],[output])
        runner.run("semantic-witnesses",["lake","env","lean","-j1","-DElab.async=false","SemanticWitnesses.lean"],resume=False)
        runner.run("readable-axioms",["lake","env","lean","-j1","-DElab.async=false","AxiomAudit.lean"],resume=False)
        audit=runner.run("public-dependencies",["lake","env","lean","-j1","--run","verification/AuditFinalUnion.lean"],resume=False)
        if "DEPENDENCY_AUDIT_SUCCESS" not in audit or "FRESH_REPLAY_SUCCESS" not in audit:
            raise RuntimeError("Missing dependency audit/replay success marker")
        object_dir=Path(".lake/verification/standalone")
        (ROOT/object_dir).mkdir(parents=True,exist_ok=True)
        output=object_dir/"RP2-Formalization.olean"
        runner.run("standalone-source",["lake","env","lean","-j1","-DElab.async=false","-o",str(output),"RP2-Formalization.lean"],[output])
        lake_path=runner.run("lake-lean-path",["lake","env","printenv","LEAN_PATH"],resume=False).strip()
        env=dict(runner.env,LEAN_PATH=str(object_dir)+os.pathsep+lake_path)
        runner.run("standalone-kernel-replay",["leanchecker","-v","«RP2-Formalization»"],env=env,resume=False)
        if current_snapshot()!=runner.summary["source_sha256"]:
            raise RuntimeError("Source changed during validation")
        runner.summary["result"]="passed"
        runner.summary["completed_utc"]=dt.datetime.now(dt.timezone.utc).isoformat()
        runner.save()
        print("EXTENSION_VALIDATION_SUCCESS",flush=True)
        return 0
    except Exception as exc:
        runner.summary["result"]="failed"
        runner.summary["error"]=str(exc)
        runner.save()
        print("FAIL",exc,flush=True)
        return 1

if __name__=="__main__":
    raise SystemExit(main())
