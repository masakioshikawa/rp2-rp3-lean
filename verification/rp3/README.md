# RP³ verification record — 12 October 2026

The RP³ public import closure and its generated standalone source compiled
successfully with Lean 4.34.1. The model witnesses and public dependency
audit also passed. These records concern the RP³ extension; the other
release directories retain the history of the supplied RP² development.

## Checks performed

1. All 73 modules reachable from `import RP3` were compiled from source,
   serially, with `lake env lean -j1`. The development driver reused a
   successful object only when its source and recursive project-dependency
   fingerprints matched. All final fingerprints were checked against the
   delivered source. `module-compilation.json` records each source and
   object hash, successful exit code, and compiler-log hash. `modules/`
   contains those logs.
2. `RP3SemanticWitnesses.lean` compiled. It checks the actual normalized
   spherical Gibbs integral, the expanded log-square endpoint, the same-site
   value 3/4, and a nonempty graph with admissible negative coupling.
3. `RP3AxiomAudit.lean` printed the axioms of the nine public roots listed in
   `../rp3-public-theorems.txt`. Each uses only `propext`, `Classical.choice`,
   and `Quot.sound`.
4. `RP3AuditEnvironment.lean` traversed the raw proof dependencies of those
   roots. The union contains 51,295 declarations. The audit rejects extra
   axioms, `sorryAx`, unsafe definitions, and partial definitions in that
   closure. It reported `DEPENDENCY_AUDIT_SUCCESS`.
5. The freshly generated `RP3-Formalization.lean` compiled separately to an
   object file, with no project-module imports. It contains the complete
   proof source, importing only Mathlib. Its compilation took approximately
   347 seconds in this environment. Its source hash is recorded below in
   `source-sha256.json`.

`checks.json` records checks 2–5, their commands, exit codes, timings, and log
hashes. The corresponding `.log` files include ordinary linter warnings;
none of these successful compilations contains an error or a `sorry` warning.
CLI-default asynchronous elaboration was retained. No unlimited-heartbeat
setting was used.

These checks include ordinary Lean kernel checking during source compilation.
The optional fresh-environment replay was **not** run for this release, and
no independent kernel implementation or remote CI run is claimed.

## Toolchain and provenance

`pinned-environment.json` records the SHA-256 of the official Lean Linux
distribution and the exact clean Git revisions of all nine dependencies.
The dependency manifest is unchanged from the supplied RP² project.

This container permits `/proc/self/exe` but restricts executable discovery
through the numeric current-process path. The small `app-path-compat.c` shim
redirected only that self-location request. Lean's binaries, kernel, source,
and dependencies were not modified. A standard local installation does not
need this shim.

`build-driver-used.py.txt` preserves the actual development compilation
driver. It contains environment-specific paths and is a record, not the
portable reproduction entry point. Use the following commands from the
project root for a fresh serial verification:

```sh
lake exe cache get
python3 scripts/verify_rp3.py --standalone
```

The portable script checks pins, compiles all modules afresh, checks witnesses
and proof dependencies, and compiles the standalone source. New records go to
`verification/rp3-latest/`. Add `--replay` for the optional fresh Lean kernel
environment replay.

`source-sha256.json` identifies the delivered proof and verification sources.
`original-rp2-preservation.json` records the byte comparison with the supplied
archive. The historical original release checksum list is preserved as
`../rp2-original-release.sha256`; the top-level `SHA256SUMS` identifies the
files in this combined RP²/RP³ archive.
