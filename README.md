# RP² and RP³ correlation-decay formalizations

**Software-only archive prepared for Zenodo, 21 October 2026.**
This is a packaging revision of the combined release checked on 12 October
2026. All original Lean files, bundle generators, proof-verification scripts,
dependency pins, and build configuration are byte-identical to that release.
The Lake package version remains 0.4.0; this packaging date does not designate
a new theorem or a new Lean verification run.

Analytical notes, their PDF/TeX sources, and their auxiliary threshold
calculations are omitted. Software documentation, licenses, provenance, and
verification records are retained. The separate 9 October RP² audit evidence
has also been included under `verification/rp2-audit-2026-10-09/`.
See [PACKAGING.md](PACKAGING.md) for the exact changes and packaging checks.

The public imports are `import RP2` and `import RP3`. For full verification
with the pinned Lean toolchain, Git, Python 3, and enough memory installed,
run these two commands sequentially from this directory:

```sh
python3 scripts/verify.py --fetch-cache --standalone --replay --replay-standalone --inventory
python3 scripts/verify_rp3.py --fetch-cache --standalone --replay
```

Both commands write new records separately from the archived audit evidence.
They download the pinned dependencies/cache when needed. Toolchain binaries,
dependency checkouts, and compiled objects are not bundled. A standard build
of both public libraries is `lake build`.

This project now also contains the RP³ extension in the `RP3` namespace.
See [README-RP3.md](README-RP3.md) for its model, proof route, and verification
instructions. The original RP² proof modules below are unchanged.
The RP³ review revision adds distinct-site positivity, local-limit existence,
SO(3) matrix identities, and the elementary high-temperature exponential bound.
See `REVIEW-RESPONSE.md` for the treatment of each suggestion and
`verification/rp3-review/` for current verification records. The initial RP³
records remain in `verification/rp3/`.
The RP² version number and release history below refer to the supplied base
project. This archive adds the RP³ companion development.

---

# Log-square quadrupolar decay in the planar RP² model

Version **0.4.0** fully formalizes the all-temperature log-square decay
bound and a direct high-temperature exponential bound for the actual RP²
Gibbs model. It retains every v0.3.1 theorem and the scoped heartbeat fix.
The public entry point is `import RP2`.

## Model and scope

Spins are unit vectors in ℝ³ with normalized spherical probability measure.
The actual Gibbs weight is

```
exp (∑e b(e) (n_left(e) · n_right(e))²)
```

and the observable is `(n_x · n_y)² − 1/3 = Tr(Q(n_x) Q(n_y))`.
The interaction and observable are invariant under independent spin sign
changes, giving the S² realization of the RP² director model.

Finite graphs may have arbitrary deleted vertices and nearest-neighbor edges.
The new theorems assume `|b(e)| ≤ β`, where `β ≥ 0`. Neither translation
invariance nor a coupling-sign condition is required. Constants are selected
before the graph, couplings, and observation sites. The distance `r` is the
integer lattice ℓ∞ distance.

The analytic inequality and actual annular comparison are proved, not
hypotheses of any headline decay theorem. Positivity of the Gibbs weight
holds for every real coupling; the proof does not use a ferromagnetic
correlation inequality. See `CHANGELOG.md` for the changes and exact scope.

## New v0.4 results

`log_square_quadrupolar_decay_signed` proves, for every β≥0,

```
∃ C>0, ∃ c>0, ∀ G b x y, (∀ e, |b(e)|≤β) →
  |C_G,b(x,y)| ≤ C exp[-c (log(2+r))²].
```

Here `r` is the integer lattice ℓ∞ distance. Constants precede the graph,
couplings, and sites. The theorem concerns the actual normalized Gibbs
integral. The analytic response, arbitrary-width pinned-kernel comparison,
edge allocation, and shell packing are all proved inside the development.
No analytic estimate or decay hypothesis is left in the endpoint statement.
The same bound, with the same constants, holds in
`log_square_quadrupolar_decay_local_limit_signed`.
Dropping `_signed` gives the ferromagnetic specialization.

`elementary_exponential_quadrupolar_decay_signed` proves exponential decay
when `0≤β<log(3/2)`. Its explicit mass is

```
mβ = -log(max(1/2, 3*(1-exp(-β)))) > 0,
|C_G,b(x,y)| ≤ (8/9) exp(-mβ*r).
```

The proof uses the actual positive edge expansion and counts simple-path
prefixes. It assumes no percolation or random-cluster theorem. It covers
signed couplings and β=0. Ferromagnetic and free-boundary local-limit
variants are also provided. The stronger direct finite-distance estimate
`nonbacktracking_quadrupolar_bound_signed` is
`|C|≤(8/9)[3(1-exp(-β))]^r`; its statement is valid for every β≥0,
although it gives decay only in the specified high-temperature regime.

The **optimized FK thresholds discussed in the historical analytical notes
are not formalized**. They rely on the Beffara–Duminil-Copin random-cluster
theorem, which is not in the pinned dependencies. The present exponential
theorem uses a smaller, explicitly stated regime. No all-temperature
exponential decay is claimed. The historical analytical notes are omitted
from this software-only archive.

The v0.3 adjacent-annulus and two-endpoint factorial/logarithmic bounds,
the positive active-edge expansion, and all earlier APIs remain available.

## Public results

All names in the following table are in namespace `RP2`.

| Declaration | Meaning |
| --- | --- |
| `superpolynomial_quadrupolar_decay_signed` | For every real p, one A>0 bounds `|C(x,y)| ≤ A(1+r)^(-p)` for all finite models with `|b(e)|≤β`. |
| `factorial_quadrupolar_decay_signed` | Uniform factorial bound `(2/3)(D/2)^k/k!`, with `N₀=2^a≥4` and `k=#{j≥0 : 2N₀4^j<r}`. |
| `logarithmic_quadrupolar_decay_signed` | Uniform large-distance bound `exp(-log r log(log r)/log 4 + Cβ log r)`. |
| `superpolynomial_quadrupolar_decay_local_limit_signed` | The same finite-volume constants work for signed-coupling free-boundary local limits. |
| `factorial_quadrupolar_decay_local_limit_signed` | The same factorial constants and radius convention pass to those limits. |
| `logarithmic_quadrupolar_decay_local_limit_signed` | The same logarithmic envelope and distance threshold pass to those limits. |
| `weighted_summability_local_limit_signed` | Every polynomially weighted absolute two-point series over ℤ² is summable. |
| `contDiff_quadrupolarStructureFactor_local_limit_signed` | The correlation Fourier series is jointly C∞ in its two real momentum coordinates. |
| `summable_quadrupolarStructureFactor_local_limit_signed` | The Fourier series is absolutely convergent at every momentum. |
| `iteratedFDeriv_quadrupolarStructureFactor_local_limit_signed` | Every order of Fréchet differentiation commutes with the lattice sum. |

The three original finite-volume declarations, the original local-limit
power bound, and `weighted_summability_local_limit` retain their names and
types for `0 ≤ b(e) ≤ β`. New ferromagnetic factorial/logarithmic local-limit
bounds and a smoothness theorem are also provided without the `_signed` suffix.

### Infinite-volume interface

`HasLocalPairLimit` expresses convergence of the actual two-spin marginals
along one common sequence of finite models. `IsFreeBoundaryLocalLimit` and
`IsSignedFreeBoundaryLocalLimit` add their respective coupling bounds.
Pair-dependent initial prefixes may be discarded so both sites are present.
`HasLocalPairLimit.correlation_bound` transfers any common spatial envelope,
including its distance restrictions, without enlarging constants.

`extendedFreeGibbsWith` embeds finite configurations using arbitrary prescribed
spins outside the volume. The fillings may vary with both volume and lattice
site. The `*_of_weak_limit_with` theorems connect weak convergence of these
actual full-configuration measures to the intrinsic local-limit predicates.
Eventual equality and convergence equivalence of pair marginals under different
fillings are proved. The original constant-fill API remains available.

### Fourier convention

For a fixed site x, `quadrupolarStructureFactor μ x k` is exactly

```
∑' y∈ℤ², C_μ(x,y) exp(i [k₁(y₁−x₁) + k₂(y₂−x₂)])
```

with k in `ℝ × ℝ`; there is no factor of 2π in the exponent.
`quadrupolarStructureFactor_eq_tsum` states this literal formula.
The definition is a fixed-base-point correlation Fourier series, so its
smoothness needs no translation-invariance assumption. For translation-invariant
correlations it is the usual base-point-independent structure factor.

`Fourier.HasSummableMoments`, `Fourier.contDiff_latticeFourierSeries`, and
`Fourier.iteratedFDeriv_latticeFourierSeries` give reusable Fourier-analysis
results independent of the spin model. The derivative majorant is
`2^(n+1) (1+r)^n |C(x,y)|`; every differentiated series is absolutely summable.
Smoothness is not a claim of analyticity or exponential clustering.

## Mathematical interfaces and historical correspondence

The finite-volume and local-limit conclusions of the 7 October 2026 note are
proved without its former analytic-input hypothesis. The verified construction
uses dyadic Fourier families and twelve tetrahedral rotations. It does not
need the note's stronger all-integer-radius/all-SO(3) comparison as a standalone
intermediate proposition. The historical prose note is not included in this software-only archive.

| Paper concept | Lean interface |
| --- | --- |
| Complex-bilinear second response R | `Paper.R`, `Paper.R_ofReal` |
| Real evaluation R(h, conjugate h) | `Paper.hermitianR`, `Paper.R_hermitian_eq`, `Paper.R_hermitian_symm` |
| Gram kernel T and commutator sum q | `Paper.T`, `Paper.q`, `Paper.T_conjugate`, `Paper.q_conjugate` |
| Fourth-order family inequality | `Paper.family_bound` (signed couplings; pair coefficient 4β) |
| Exact twelve-rotation tensor cancellation | `tetraAction_average_Q_zero` |
| Simultaneous unnormalized partition preservation | `AveragingSystem.partition_replace_all` |
| Abstract positive-remainder correlation estimate | `AveragingSystem.correlation_bound` |
| Actual pinned annular comparison | `Fourier.LatticeGraph.dyadic_kernel_comparison_signed` |
| Exact-envelope passage to limits | `HasLocalPairLimit.correlation_bound` |

The remainder-normalization interface works for an arbitrary finite family of
kernels with the specified invariances. It assumes neither independence of
annuli nor that an individual annular kernel is a normalized probability.

## Reproduction and automated checks

Pinned dependencies are Lean **4.34.1** and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The archive includes the full
Lake manifest and an independent release pin record. Keep those files intact;
there is no need to run `lake update`.

With the exact Lean toolchain, Git, and Python 3 installed, run from this
project directory:

```sh
python3 scripts/verify.py --fetch-cache
```

This verifies dependency pins and cleanliness, compiles every reachable
project module serially, checks the standalone source matches the modules,
compiles the permanent semantic witnesses, and rejects unexpected axioms or
unsafe/partial dependencies of every listed public theorem. Missing audit
roots are errors. The axiom allowlist is exactly `propext`, `Classical.choice`,
and `Quot.sound`; simply printing an axiom list is not accepted as the gate.

For release verification including fresh standalone compilation and replay:

```sh
python3 scripts/verify.py --fetch-cache --standalone --replay --replay-standalone --inventory
```

The raw dependency walk examines declaration types and proof/definition
bodies. `--replay` checks the public dependency closure, including its imported
mathematical dependencies, from an empty kernel environment. Replay uses the
same Lean kernel implementation, not an independently implemented verifier.
The audit executable is not imported by the proof library.

Lean jobs run sequentially and single-threaded because importing this pinned
Mathlib build needs substantial memory (roughly 6–6.5 GiB for a Lean process
in the development environment). Allow additional memory for the operating
system. `--resume` is available for interrupted verification with unchanged
inputs; dependency auditing and requested replays still run anew.

`.github/workflows/lean.yml` invokes the same checks and preserves their logs.
Its optional manually selected replay mode enables the release checks. The
workflow is supplied for use in a GitHub repository; the included local release
records do not imply that a remote GitHub Actions run has already occurred.

### Standalone file

`RP2-Formalization.lean` contains the complete public proof source and imports
only Mathlib. It is generated from the modular source, including all new
results:

```sh
python3 bundle.py
python3 bundle.py --check
lake env lean -j1 RP2-Formalization.lean
```

Edit the modules, then regenerate the standalone file. `--check` is read-only
and fails if the checked-in bundle is stale. The semantic witnesses spell out
the actual integral quotient and test normalization, the nonzero same-site
correlation, and admissibility of an explicit negative-coupling graph.

## Verification records and boundaries

`verification/v0.4/` records the original RP² compilation and proof-dependency
checks; `verification/RELEASE.md` describes that earlier record. The subsequent
9 October audit, including fresh dependency and standalone-object replay, is
in `verification/rp2-audit-2026-10-09/`. These dated records retain their original
source snapshots and should be read separately.
The standalone file is freshly compiled with default asynchronous
elaboration. `scripts/verify.py` also now uses default elaboration, with
one worker to control memory. The scoped 400,000-heartbeat budget for the
tetrahedral decomposition is retained.

Historical evidence remains separately identified: v0.3.0 records in
`verification/v0.3.0/`, v0.3.1 default-elaboration checks in
`verification/heartbeat-fix/`, and v0.2 records in `verification/v0.2/`.
Earlier snapshots and their hashes do not purport to validate new source.

These results concern free-boundary finite models and the stated existing
local limits. They do not prove existence or uniqueness of an infinite-volume
limit, a DLR characterization, all-temperature exponential decay, or a
continuum mass gap. Correlations of arbitrary bond observables are not covered.

## Attribution

The starting mathematical source is *Superpolynomial quadrupolar decay in the
planar RP² model*, research note dated 7 October 2026.

This project adapts portions of OpenAI's ClassicalON development at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, under Apache-2.0:

https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ClassicalON

Source comments, `NOTICE`, and `LICENSE` retain provenance. The squared
interaction and signed-coupling endpoints are proved for the actual RP²
integrals; the upstream O(n) decay theorem is not imported as an assumption.
