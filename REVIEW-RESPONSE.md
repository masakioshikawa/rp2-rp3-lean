> Historical document for the Lean 4.34.1 archived release. For the current
> Palomar port, toolchain, and verification commands, see [PALOMAR.md](PALOMAR.md).
> Statements of source identity and audit success below refer to the original
> release preserved at tag `zenodo-2026-10-21`.

# Response to the supplied RP³ review

Historical review response from the 12 October 2026 combined release.
Its references to included analytical notes describe that original release;
those notes are omitted from the 21 October software-only archive. The
original review remains in `review/` as code provenance. See `PACKAGING.md`.

The review is supplied as `RP3-Improvement-Suggestions.lean`, dated 11 October
2026. Its original text is preserved in `review/` for provenance. Its proposed
unproved targets are not imported or assumed by the proof library.

The mathematical statement of the existing all-temperature log-square bound
is unchanged. The revision adds the supplied proved results, a direct
high-temperature extension, and stronger reproducibility checks.

| Suggestion | Resolution |
| --- | --- |
| Distinct-site nontriviality | Added `RP3.ModelWitnesses.G1_correlation_pos` and `exists_distinct_sites_positive_correlation`, with the supplied 24-isometry moment computation. Every positive one-bond coupling has strictly positive endpoint correlation. The semantic witness suite now checks this. |
| Existence of local limits | Added compactness/subsequence extraction for any exhausting sequence of admissible finite models, full-box witnesses for both signed and ferromagnetic classes, and a nonvacuous log-square endpoint. An explicit unit spin removes the need for a caller-supplied filling in the public existence results. |
| Semantic closure CI gate | Added a separate inventory program and a checked-in baseline. It records statement types and definition bodies, with SHA-256 fingerprints, including structure fields and instances. It traverses all namespaces and identifies project declarations by defining module. A declaration-name list alone would not detect a changed definition with the same name. CI fails on a changed baseline comparison. |
| SO(3) matrix form | Added the rotation matrix, orthogonality, determinant, multiplicativity, trace identity, actual Gibbs-integral identity, and log-square restatement. These integrals still use the sphere reference measure. |
| Arbitrary pinned boundaries | Remains a distinct mathematical extension. The unconditional endpoints in this release have free finite-volume boundaries and free-boundary local limits. No arbitrary-boundary order theorem is claimed. |
| High-temperature exponential decay | Ported the existing positive active-edge expansion and nonbacktracking path argument to RP³. For `0 ≤ β < log(3/2)`, the prefactor is 1 and the mass is `-log(max(1/2, 3*(1-exp(-β))))`. Signed/ferromagnetic and finite-volume/local-limit versions are included. |
| Haar pushforward | Integrated the supplied conditional invariance proof. Surjectivity onto SO(3) remains an explicit hypothesis of that auxiliary lemma; a full unconditional Haar identification is not claimed. No main RP³ theorem depends on it. |
| Explicit all-temperature β dependence | Remains a quantitative extension. The log-square constants are existential, as before. The new high-temperature mass is explicit. |
| Narrow Mathlib imports | Replaced the six full-Mathlib imports by a shared set of 21 prerequisite modules, extracted from the elaborated proof and supplemented with the tactic frontend. The isolated import check used about 3.53 GiB peak resident memory here. This is a shared sufficient set, not a per-module minimum. |
| Shared RP²/RP³ abstraction | Deferred as a larger refactor. In particular, the suggested condition `a² = -κ·1` is not satisfied by the RP² coordinate generators: their squares have the form `diag(0,-1,-1)`. A common interface must encode the appropriate mixed identities instead. All RP² proof sources are retained unchanged. |
| Mathlib quaternion API | A reasonable future refactor. The existing finite action and matrix identities remain fully proved; replacing their representation would affect a large part of the verified proof and public names. This revision addresses the larger full-Mathlib import cost first. |
| Compatibility and linter cleanup | Updated deprecated conditional, finite-sum integral, and set-membership lemma spellings. Some unused-variable/simp warnings and the three scoped transparency compatibility options remain. They do not weaken kernel checking. |
| Spin type aliases | `RP3.Spin` and `RP3.Rotation.Spin 4` are already definitionally equal sphere types. Their existing names are retained; no conversion axiom or unproved identification is used. |
| Release replay and environment disclosure | The release verification workflow includes fresh Lean-kernel replay, records the execution environment, and explains the self-executable-path compatibility shim. This is Lean's own kernel, not an independently implemented checker. Exact successful commands and outcomes are archived. |
| Missing analytical note | Included the original RP³ PDF and TeX under `analytical-rp3/`, unchanged, together with a status note explaining which claims are now formalized. |
| Path-graph formula at every distance | Remains an optional stronger witness. The new strict one-bond positivity result already supplies the requested distinct-site check. |

## Attribution and audit separation

The supplied moment, positivity, compactness, and SO(3) proofs are integrated
with attribution in `RP3/ModelWitnesses.lean`, `RP3/LocalLimitExistence.lean`,
and `RP3/SO3.lean`. The high-temperature proof is adapted from the original
RP² v0.4.0 source, with quaternion cancellation and the RP³ normalization.

The semantic inventory concerns the *meaning of statements*: it omits theorem
proof bodies, and an intentional definition change requires explicit baseline
regeneration and review. The separate dependency audit checks raw proof
bodies, rejects additional axioms and unsafe/partial dependencies, and replays
the public dependency closure. Neither program is imported by the proof library.

The executable-path shim only redirects the current process's numeric
`/proc/<pid>/exe` lookup to `/proc/self/exe` in this container. No Lean binary,
kernel code, or dependency source is modified. Standard installations do not
need it. See `verification/rp3-review/environment.json` and the reproduction
instructions in `README-RP3.md`.
