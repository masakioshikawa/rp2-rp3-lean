> Historical document for the Lean 4.34.1 archived release. For the current
> Palomar port, toolchain, and verification commands, see [PALOMAR.md](PALOMAR.md).
> Statements of source identity and audit success below refer to the original
> release preserved at tag `zenodo-2026-10-21`.

# Log-square quadrupolar decay for the planar RP³ model

Status: **Lean-verified**, with Lean 4.34.1 and the pinned dependencies below.
All 83 modules and the 15,635-line standalone source compiled successfully.
The model witnesses, semantic gate, raw dependency audit, and fresh-kernel
replay passed. The original release records are under `verification/rp3/`;
the current checks are in [verification/rp3-review/README.md](verification/rp3-review/README.md).
See [REVIEW-RESPONSE.md](REVIEW-RESPONSE.md) for the changes following review.

This extends the RP² version 0.4.0 project with a separate `RP3` namespace.
The original `RP2` proof modules are unchanged. The public entry point is
`import RP3`.

## The actual model

`RP3.Spin` is the unit sphere in `EuclideanSpace ℝ (Fin 4)`. Its reference
law is normalized spherical measure, and finite configurations use its
product probability. The Gibbs weight is

```text
exp (∑ e, b(e) * (q_left(e) · q_right(e))²)
```

The observable is `(q_x · q_y)² − 1/4 = Tr(Q(q_x) Q(q_y))`, with
`Q(q) = q qᵀ − I₄/4`. Independent sign invariance of the interaction and
observable is proved. This is the sphere realization of the RP³ director
model, without choosing a global lift of projective configurations.

`RP3.correlation` is the actual normalized Gibbs integral, not an abstract
function assumed to satisfy a response or annular bound. The semantic
witness file expands this integral quotient in the final theorem and checks
that the same-site correlation is exactly 3/4. It also checks a nonempty
nearest-neighbor graph and admissible negative couplings. New moment identities
prove that the correlation on a single bond between two **distinct** sites is
strictly positive at every positive coupling. The witness suite checks this
and the existence of actual free-boundary local limits.

## Public results

- `RP3.log_square_quadrupolar_decay_signed`: for every β ≥ 0 there exist
  C > 0 and c > 0 such that every finite retained nearest-neighbor graph in
  ℤ², every real coupling array with |b(e)| ≤ β, and every two sites satisfy
  `|C_G,b(x,y)| ≤ C * exp(-c * log(2+r)²)`, where r is the lattice sup distance.
- `RP3.log_square_quadrupolar_decay_local_limit_signed`: the same constants
  apply to every existing signed-coupling free-boundary local limit.
- The corresponding names without `_signed` specialize to ferromagnetic
  couplings. The factorial and arbitrary-power superpolynomial bounds are
  also retained in the RP³ namespace.
- `RP3.exists_signed_local_limit_of_sequence` constructs a local limit from
  any exhausting sequence of admissible finite models. The theorems
  `RP3.exists_signed_free_boundary_local_limit` and
  `RP3.exists_free_boundary_local_limit` give actual signed and ferromagnetic
  witnesses for every β ≥ 0, using full boxes with constant coupling β.
- `RP3.elementary_exponential_quadrupolar_decay_signed` gives the explicit
  high-temperature bound below, with signed/ferromagnetic finite-volume and
  local-limit versions.

Constants precede the graph, coupling array, and sites in the theorem type.
No fourth-order inequality, comparison estimate, factorization certificate,
or decay assumption is a parameter of these endpoints. Finite-volume
boundary conditions are free. Local-limit existence is now proved separately
by compactness and subsequence extraction. Neither uniqueness nor a DLR
characterization is asserted.

## Elementary high-temperature bound

For `0 ≤ β < log(3/2)`, put

```text
m(β) = -log(max(1/2, 3*(1-exp(-β)))) > 0.
```

The actual RP³ correlation obeys `|C_G,b(x,y)| ≤ exp(-m(β)*r)` whenever
`|b(e)| ≤ β`. The prefactor is **1** for the unnormalized quadrupolar
observable used here. The finite-distance bound
`|C_G,b(x,y)| ≤ [3*(1-exp(-β))]^r` holds for every β ≥ 0; it becomes a
decay estimate in the stated high-temperature regime. The proof ports the
positive active-edge expansion and nonbacktracking path count from RP².
It assumes no percolation theorem. The same mass and prefactor pass to
free-boundary local limits.

## SO(3) matrix identities and exact scope

`RP3.SO3.rotOf` is the usual unit-quaternion rotation matrix. The development
proves that it belongs to `Matrix.specialOrthogonalGroup (Fin 3) ℝ`, proves
multiplicativity, and proves

```text
(q · q')² - 1/4 = (1/4) * Tr(R(q)ᵀ R(q')).
```

`RP3.SO3.correlation_eq_so3` rewrites the actual Gibbs integral with matrix
weight `exp(∑ e, b(e)*(1+Tr(R_xᵀ R_y))/4)`, and
`RP3.SO3.so3_log_square_decay_signed` supplies its decay bound. These integrals
still use the spherical reference law. The coefficient of the matrix trace
is `b(e)/4`.

`RP3.SO3.haarInvariance_of_surjective` proves left-invariance conditional on
surjectivity onto SO(3). Surjectivity and a complete Haar-measure pushforward
identification remain separate formalization targets. This conditional lemma
is not a premise of either unconditional RP³ decay theorem.

## The quaternion implementation

The proof works directly on S³. The real four-dimensional generators are
left multiplication by i/2, j/2, and k/2; they satisfy [a,b] = c. Their
operator norms are bounded by one, and the required fourth-order identities
are proved for these matrices. Closed quaternion-matrix multiplication keeps
these polynomial proofs manageable for the elaborator.

The finite averaging group is Q₈ = {±1, ±i, ±j, ±k}. Its action preserves
spherical probability, and its average annihilates the quadrupolar insertion.
The relevant rotation paths have period 4π on S³. The response-to-kernel
constants include this period. The spatial Fourier estimates, exact kernel
normalization, and thin-shell packing are adapted from the RP² development.

This directly proves the RP³ result. The original analytical note is omitted
from this software-only archive. The full Haar pushforward, anisotropic frame
extension, and sharper random-cluster thresholds remain outside the formalized
endpoints. Arbitrary pinned-boundary decay and explicit all-temperature
β-dependent constants also remain targets. No all-temperature exponential
decay or exclusion of a vortex-sector transition is claimed.

## Reproduction

Dependencies are pinned by `lean-toolchain`, `lake-manifest.json`, and
`verification/dependency-pins.json`: Lean 4.34.1 and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

```sh
lake exe cache get
python3 scripts/verify_rp3.py --standalone --replay
```

The verifier writes new records to `verification/rp3-latest/`, preserving the
archived release checks. It compiles the public import closure serially,
checks the model witnesses, enforces a reviewed semantic baseline, prints
public theorem axioms, and audits raw proof dependencies. `--replay`
additionally replays the public dependency closure
into a fresh Lean kernel environment. This uses Lean's kernel; it is not an
independently implemented checker. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed as axioms in public dependencies.

A standard Lake build is `lake build RP3`. Use the serial verifier on machines
with limited memory. RP³ now uses a shared targeted Mathlib prerequisite set;
none of its modules imports all of Mathlib. The isolated import check used
approximately 3.53 GiB peak resident memory in this container. This is an import
measurement, not a bound on every proof or a parallel Lake build. The RP²
imports are unchanged. No unlimited-heartbeat setting is used.

The semantic gate hashes elaborated statement types and definition bodies,
including structure fields, rather than just listing declaration names.
Theorem proof bodies are checked by the separate proof audit and replay.
An intentional semantic change requires explicit baseline regeneration with
`--write-semantic-baseline` and review; CI never supplies that flag.

The standalone file is generated from the same source:

```sh
python3 bundle_rp3.py
python3 bundle_rp3.py --check
lake env lean -j1 RP3-Formalization.lean
```

The standalone file imports Mathlib, so it still requires the pinned Lean and
Mathlib environment. It has no imports from the `RP2` or `RP3` source trees.

Keep the original RP² release records separate from new RP³ verification
records. Historical records do not validate the new target.

## Attribution

The RP³ construction extends the historical analytical note and the RP²
version 0.4.0 formalization. The fourth-order rotation method derives from
OpenAI's ClassicalON development at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. Source attributions and the
Apache-2.0 license are retained; see `NOTICE` and `LICENSE`.
