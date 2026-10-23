# RP³ review revision — 12 October 2026 (UTC)

- Integrated the supplied Claude Opus proofs of distinct-site strict positivity,
  free-boundary local-limit existence, and the SO(3) matrix identities and
  sphere-integral restatement. The full Haar identification remains separate.
- Ported the elementary high-temperature exponential bound to RP³, with
  threshold `β < log(3/2)`, prefactor 1, and an explicit mass.
- Added a CI gate for elaborated statement types and model definitions,
  supplementing the axiom/proof dependency audit.
- Replaced full Mathlib imports with 21 shared prerequisite modules and
  updated deprecated lemma spellings.
- Included the original analytical RP³ note and a response to each review
  suggestion. The RP² sources are unchanged.

# RP³ companion extension — 12 October 2026

- Added a separate `RP3` namespace for the squared-inner-product model on
  the unit sphere in real four-space, with quadrupolar observable
  `(q_x · q_y)² − 1/4` and proved independent sign invariance.
- Proved the uniform all-temperature log-square bound for bounded signed
  nearest-neighbor couplings on finite square-lattice subgraphs, and its
  free-boundary local-limit transfer.
- Implemented the quaternion half-generators, their fourth-order identities,
  quaternion-unit averaging, and the required 4π-periodic rotation paths.
- Compiled all 73 RP³ modules and the generated standalone file with the
  pinned Lean 4.34.1 toolchain; checked expanded model witnesses and audited
  the public proof dependencies. Records are in `verification/rp3/`.
- Retained the RP² proof sources without modification. The RP³ entry point
  does not include a high-temperature exponential theorem or the analytical
  note's separate SO(3) and anisotropic-model extensions.

# Version 0.4.0 — 9 October 2026

- Fully formalized the all-temperature log-square bound for bounded signed
  couplings, with uniform constants and exact free-boundary local-limit
  transfers; included ferromagnetic specializations.
- Proved balanced thin profiles, truncated Fourier estimates with spatial
  support retained in column bounds, actual pinned Gibbs response estimates,
  arbitrary-width annular kernel comparisons, and linear shell packing.
- Proved a direct exponential bound for `0≤β<log(3/2)` using the exact
  positive edge expansion and nonbacktracking simple-path prefixes.
  The prefactor is 8/9 and the positive mass is explicit; signed couplings,
  β=0, same-site correlations, and local limits are included.
- The sharper analytical FK thresholds remain unformalized; they are not
  assumed as axioms or hidden premises of the included theorems.
- Retained the v0.3.1 scoped heartbeat fix and moved the portable verifier
  to CLI-default asynchronous elaboration. Dependency pins are unchanged.

# Version 0.3.1 — 9 October 2026

- Following an external audit reported by the user, raised `maxHeartbeats` to
  400,000 locally for `RP2.Rotation.tetraLinearIsometry_eq_three_rotations`.
  This addresses a reproduced 200,000-heartbeat timeout with default
  asynchronous elaboration; the existing verification scripts disable it.
- Regenerated the standalone source. Mathematical statements, proof scripts,
  dependencies, and trust assumptions are unchanged.
- Maintenance-check evidence is in `verification/heartbeat-fix/`; the earlier
  complete v0.3.0 audit remains identified with its original source hashes.

# Version 0.3.0 — 9 October 2026

- Adjacent dyadic annuli may share their pinned boundary.
- Two endpoint families give the squared-factorial bound and leading coefficient 2/log 2.
- Eight exact local-limit transfers cover signed and ferromagnetic variants.
- Positive active-edge expansion proves disconnected-cut cancellation and the actual-correlation/connected-mass bound for signed couplings.
- New analytical addendum proves a log-square envelope and high-temperature FK exponential regime; these analytical extensions are explicitly NOT fully formalized in this release.
- Existing v0.2 declarations and pinned dependencies remain unchanged.

# Changes in version 0.2.0

This revision starts from the exact RP² formalization delivered and audited
on 8 October 2026. The original source had SHA-256
`9ddd73a461e8880a042fdfcf3f4989c6fbcaf7007c5a6eb53267d5635462f64f`.

## New mathematical results

1. **Bounded signed couplings.** The finite-volume power, factorial, and
   logarithmic bounds now hold under `|b(e)|≤β`. The existing analytic and
   pinned-kernel estimates already had this hypothesis. The final assembly
   now uses it directly; positivity comes from the exponential weight and
   does not require nonnegative couplings.
2. **Quantitative local-limit bounds.** The factorial and logarithmic estimates
   pass to actual local limits with the same constants and thresholds. Signed
   power decay and every weighted absolute moment are also formalized. A
   generic envelope-transfer theorem supplies the common argument.
3. **Arbitrary outside fillings.** The full-configuration weak-limit bridge
   permits prescribed outside spins depending on volume and site. Two-spin
   marginals for any two such fillings are eventually identical along an
   exhaustion, and their convergence is equivalent. No uniqueness of the
   full limiting measure is asserted.
4. **Smooth correlation Fourier series.** All polynomial absolute moments imply
   joint C∞ smoothness in the two real momentum coordinates, absolute
   convergence of every differentiated series, and termwise differentiation
   of every order. These theorems are specialized to the actual signed and
   ferromagnetic local-limit correlations. The fixed-base-point definition
   uses `exp(i k·(y−x))`; no translation-invariance assumption is hidden.
5. **Exact finite-group tensor cancellation.** The full quadrupole tensor,
   not only its scalar contraction, has zero average under the twelve
   tetrahedral rotations.
6. **Reusable simultaneous partition identity.** For finite families of
   kernels satisfying the declared averaging invariances, replacing all
   kernels by their remainders preserves the unnormalized partition integral.

## Public interfaces and compatibility

- `Paper.R`, `Paper.T`, and `Paper.q` match the note's notation. Theorems state
  conjugation, Hermitian symmetry, the realness of `R(h,conjugate h)`, the
  purely imaginary nature of q, and the family inequality.
- The original three ferromagnetic finite-volume theorem signatures are
  unchanged. The original local-limit power and summability theorems also
  remain available and are specializations of their signed counterparts.
- `IsFreeBoundaryLocalLimit` is factored through `HasLocalPairLimit`; unfolding
  the latter yields the same original condition. A separate
  `IsSignedFreeBoundaryLocalLimit` avoids silently broadening the old name.
- The constant-fill definitions and bridge remain available.
- The dyadic and finite-tetrahedral proof route is retained. General all-radius,
  all-SO(3) comparisons and every derivative packaging used in the prose note
  are still not separate exported theorems.

## Reproducibility and documentation

- Added a serial verification runner with immutable dependency pins, source
  hashes, successful-command records, finite timeouts, and controlled resume.
- Added enforced raw-body axiom/safety checks and optional empty-environment
  dependency replay. These use the same Lean kernel implementation.
- Promoted semantic audit witnesses to permanent regression checks, including
  the literal Gibbs-integral statement and an actual negative coupling.
- Added a pinned GitHub Actions workflow invoking the same runner.
- Added read-only `bundle.py --check` and cycle detection in import traversal.
- Updated the README, public theorem correspondence, and the historical
  “missing analytic estimate” comment. No changes to the separate PDF draft
  are included in this code revision.

See `verification/RELEASE.md` and `verification/latest/summary.json` for this
revision's actual verification result; the earlier audit applies to its own
identified snapshot.
