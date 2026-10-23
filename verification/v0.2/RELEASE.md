# Release verification — RP² version 0.2.0

Completed on 2026-10-08T21:22:57.620932+00:00.

All required local release checks passed. The exact source hashes, commands,
UTC timestamps, timings, and return codes are in `latest/summary.json`.
This is fresh verification of the improved release, separate from the earlier
full audit of version 0.1.0.

| Check | Result |
| --- | --- |
| Pinned Lean and nine dependency revisions | Passed |
| Dependency source cleanliness | Passed, including untracked source files |
| Modular compilation | All 61 modules compiled freshly, sequentially |
| Standalone synchronization | Matches the complete modular import closure |
| Permanent semantic witnesses | Compiled successfully |
| Mandatory public theorems | 37 names present; raw types and proof bodies inspected |
| Allowed axioms | `Classical.choice`, `Quot.sound`, `propext` |
| Unsafe or partial public proof dependencies | None |
| Empty-environment kernel replay | Passed for the union of 52,367 reachable declarations |
| Fresh standalone compilation | Passed in 410.562 seconds |
| Replay of the newly produced standalone object | Passed in 43.108 seconds |
| Independent incremental source review | No substantive mathematical or semantic blocker found |

Standalone source SHA-256:

```
f45feefc4e464fcf1554370f91f4dcb68b19104b274c0454a39d7de689717ffa
```

The reviewer examined the changed signed-coupling chain, exact limit envelopes,
outside fillings, response conventions, tensor cancellation, remainder identity,
and Fourier-series regularity. `SOURCE-REVIEW.md` records the findings;
`reviewed-source-hashes.json` records the reviewed mathematical files.
The original three finite-volume endpoint types also passed the source-level
compatibility comparison in `original-api-compatibility.json`. Permanent Lean
witnesses restate both the signed and original actual Gibbs-integral endpoints.

## Trust and reproducibility

The axiom gate inspects raw declaration types and values and fails on a missing
public theorem, an unapproved axiom, or an unsafe/partial proof dependency.
Every requested public dependency is then replayed into an empty kernel
environment, including imported mathematical declarations. The audit program
itself uses runtime metaprogramming and is not imported into the proof library.

Both replay passes use the same Lean 4.34.1 kernel implementation as compilation.
No independently implemented proof checker or human referee is claimed. Lean's
kernel/distribution, serialization/import implementation, runtime/OS/hardware,
and the listed standard axioms remain trusted. The replay covers the public
closure, not unrelated declarations elsewhere in Mathlib.

The local environment used one Lean worker and a small executable-path
compatibility shim through LD_PRELOAD. Its source is included at
`runtime/proc-self-compat.c`: it redirects only the current process's
`/proc/<pid>/exe` readlink request to `/proc/self/exe`. It changes no proof term
or kernel rule and is unnecessary on ordinary installations where executable
path discovery works. The pinned GitHub workflow uses the ordinary distribution
without this shim.

The GitHub Actions workflow is supplied but has not been executed remotely.
The successful records are from the local invocation of its verification runner:

```
python3 scripts/verify.py --standalone --replay --replay-standalone --inventory
```

On a fresh installation add `--fetch-cache` to obtain the pinned dependencies.
Generated objects and installed dependencies are omitted from the release
archive. Rebuilding reconstructs them. Existing style/deprecation warnings are
retained in the compiler logs; all accepted commands completed with exit zero.
