# Version 0.4.0 compilation and proof-dependency validation

Completed: 2026-10-09T01:39:13.117980+00:00

## Formal theorem scope

The all-temperature log-square bound is fully formalized for actual finite
RP² Gibbs correlations with bounded signed couplings, together with the
same constants in the stated existing free-boundary local limits. The
ferromagnetic specializations are also included. The endpoint statements
contain no analytic response or kernel-comparison premise.

A direct exponential theorem is fully formalized for 0≤β<log(3/2), including
signed couplings, β=0, same-site correlations, and the stated local limits.
It has prefactor 8/9 and explicit positive mass
−log(max(1/2,3(1−exp(−β)))). The sharper FK thresholds in the analytical note
remain unformalized; no external random-cluster theorem is assumed.

## Completed checks

- 86 project modules including the public entry point.
- 21 new or changed modules relative to v0.3.1,
  including the entry-point import update. Individual default-elaboration
  compilation logs are retained in v0.4/module-compilation/.
- The complete 16493-line standalone source
  was freshly compiled with CLI-default asynchronous elaboration enabled,
  using one worker. It imports only the pinned Mathlib.
- Exact modular/standalone bundle synchronization passed.
- Permanent semantic witnesses and printed principal theorem statements passed.
- All nine pinned dependency revisions and clean checkout states were checked.
- All 69 selected public roots exist as theorems.
  Their raw type-and-body dependency union contains
  53300 declarations.
- The only axioms in that union are propext, Classical.choice and Quot.sound.
  No unsafe or partial declaration is in the public proof dependency union.
- No sorry or additional axiom was introduced in mathematical source.

The raw dependency checker includes both declaration types and values and
the required mutually inductive siblings. Its unsafe IO entry point only
loads the environment; the checker is not imported by RP2.

This release received compilation, trust-boundary checks and focused source
reviews while developing the proof. A separate full audit and an additional
empty-environment kernel replay of v0.4 have not been performed. Historical
v0.3.0 replay records remain associated with their original source hashes.

## Reproduction

Lean is 4.34.1; Mathlib is pinned at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Keep the supplied manifest.

```sh
python3 scripts/verify.py --fetch-cache --standalone
```

For an optional subsequent full dependency and standalone-object replay:

```sh
python3 scripts/verify.py --fetch-cache --standalone --replay --replay-standalone --inventory
```

The portable verifier now uses default asynchronous elaboration. The local
400,000-heartbeat budget for the twelve-rotation decomposition is retained.
Lean processes are serial and single-threaded for memory control. The
development container uses the documented proc-self compatibility shim for
executable resource discovery; it does not alter proof checking.

## Artifact identities

- Standalone source SHA-256: `843e4759583ab05a60e0b5d25cd36fe7a3df432f0411447bdb44a15ebc26b5ad`
- Standalone compiled-object SHA-256: `ad5140a9c663c138b39f354de97d8ccd807be8589178d9fabfe77f71cb60d66a`
- Prior v0.3.1 archive SHA-256: `9131bf5589e158621e47df273aef0367f6b355f2fbc1d2cb139a308c0b99a32b`

The full source snapshot and command records are in v0.4/summary.json.
Earlier evidence remains in v0.3.0/, heartbeat-fix/, v0.2/, and baseline/.
