# Verified RP³ review revision — 12 October 2026 (UTC)

The complete portable verification script finished with exit code 0 and
`result: passed`. All **83 modules**, the semantic witness suite, the axiom
listing, the semantic inventory/gate, the raw dependency audit with fresh
kernel replay, and the generated standalone source passed.

## Actual execution

The release command, run in the environment described in `environment.json`,
was:

```sh
python3 scripts/verify_rp3.py --write-semantic-baseline --standalone --replay \
  --output verification/rp3-review
```

The baseline flag explicitly initialized the new semantic gate for this
reviewed revision. It is not used by CI. For ordinary reproduction, use:

```sh
lake exe cache get
python3 scripts/verify_rp3.py --standalone --replay
```

That checks the delivered baseline and writes fresh records to
`verification/rp3-latest/` without changing the archived release records.

`summary.json` contains every command, successful exit code, timing, log hash,
generated object hash, and initial/final source snapshot. Module compilation
was from source, with one Lean worker and CLI-default asynchronous elaboration.
All nine dependency revisions were checked against the unchanged manifest,
and their Git checkouts were clean. The standalone source was regenerated
from the same modules and compiled separately.

## Proof and semantic audits

The **20 public theorem roots** in `../rp3-public-theorems.txt` have a union
closure of **53,422 declarations**. The raw audit rejected extra axioms and
unsafe/partial dependencies and reported both:

```text
DEPENDENCY_AUDIT_SUCCESS
FRESH_REPLAY_SUCCESS
```

Only `propext`, `Classical.choice`, and `Quot.sound` occur as axioms in the
audited proofs. Replay rebuilt the selected dependency closure in a fresh
environment using Lean's kernel. No independently implemented checker or
hosted CI run is claimed.

The semantic inventory covers seven public statement closures. Their types
and project definition bodies are recorded with SHA-256 fingerprints in
`../rp3-semantic-baseline.json`. Project declarations are identified by their
defining modules, and traversal is not restricted to a namespace. The inventory
includes relevant structure fields and instance terms, but excludes theorem
proof bodies, which the separate raw audit checks.

`semantic-gate-negative-checks.json` records two controlled tests: changing a
definition body or a statement type in captured inventory data while retaining
the same declaration names and counts. Both were rejected with the expected
exit code 1. These tests exercise the comparison gate; they are not modifications
of the delivered Lean proofs.

## Reproducibility and provenance

- `environment.json` identifies the local Linux execution environment, exact
  Lean distribution checksum, and compatibility requirement.
- `app-path-compat.c` redirected only Lean's executable-discovery lookup from
  the current numeric PID path to `/proc/self/exe`. The compiler, kernel, and
  dependency sources were not modified. Ordinary installations need no shim.
- `targeted-import-memory.json` records an isolated compilation of the new
  Mathlib prerequisite module, with peak resident memory about 3.53 GiB. It is
  not a bound on all proof compilations or concurrent builds.
- `baseline-preservation.json` identifies the exact reviewed input and confirms
  that all 85 RP² modules, its entry point and standalone source, and the pinned
  toolchain/manifest remain byte-for-byte unchanged.
- The old combined release's checksum list is retained as
  `../rp3-original-release.sha256`. The top-level `SHA256SUMS` covers this
  revised package. Historical logs identify their own source snapshots and
  are not used as evidence for the new additions.

Some style/deprecation linter warnings remain in successful compiler logs.
There are no failed proof obligations, `sorry` declarations, or unlimited
heartbeat settings in the delivered RP³ source.
