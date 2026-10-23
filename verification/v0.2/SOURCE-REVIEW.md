# Independent source review of the improved RP² formalization

Review is of source semantics and the mathematical dependency chain. Lean compilation and trust checks are performed separately by the release coordinator. The completed new sources have been reviewed; concrete verification results are recorded separately by the release coordinator.

## Signed-coupling extension: baseline assessment

The planned extension from `0 ≤ b_e ∧ b_e ≤ β` to `|b_e| ≤ β` does not require a new analytic positivity principle.

- `partition_pos` in `RP2/Model.lean` constructs the actual partition function from `exp (∑ b_e (n_u·n_v)^2)` and proves strict positivity for arbitrary real strengths. The signed interaction still has a positive, integrable weight on the compact configuration space.
- `pinnedPartition_pos` also has no nonnegativity restriction on the strengths. Dirac pins and free-spin surface measures remain positive probability measures.
- `rotation_family_bound`, `annulus_response_inverse_scale`, `annulus_partition_inverse_scale`, and `full_kernel_axisC_comparison` already use absolute bounds on the strengths.
- `concrete_kernel_product_bound` and `square_annuli_product_bound` take arbitrary real couplings. Their positivity hypotheses concern kernels and Boltzmann weights, not the sign of the energy coefficients. Locality and rotational invariance also hold independently of sign.
- The sole ferromagnetic-specific step in `exists_dyadicKernelComparison` is conversion of its stronger coupling hypothesis by `abs_of_nonneg`. The remaining restriction occurs in the statements of `DyadicKernelComparison` and the downstream rate wrappers.

Consequently the extension should preserve the same finite retained square-lattice graph domain, ℓ∞ distance, quadrupolar normalization, graph-independent constants, free-boundary convention, and summability conclusion. This does not by itself claim arbitrary graph geometry, a spatially infinite Gibbs-state construction, or pinned-boundary decay.

## Scope of the completed source review

1. Compare completed signed statements and wrappers to the baseline, including quantifier order and coupling-bound propagation.
2. Check signed and ferromagnetic local-limit factorial/logarithmic bounds and arbitrary exterior fillers.
3. Check public paper notation for conjugation and tensor trace conventions, and the generic remainder interface.
4. Check Fourier-series momentum pairing, differentiation domain, summability exponents, and the interpretation of a fixed-origin transform versus translation-invariant structure factor.

## Arbitrary exterior fillings and local convergence (source reviewed)

`HasLocalPairLimit` factors out precisely the original two-spin convergence content: one graph/coupling sequence works for every pair, but each pair may discard a different finite prefix. The existing `IsFreeBoundaryLocalLimit` retains the same meaning, and the signed analogue changes only the coupling bound. `IsFreeBoundaryLocalLimit.signed` is the correct one-way inclusion.

`HasLocalPairLimit.correlation_bound` transfers an arbitrary spatial envelope `B(x,y)`, restricted if desired by a property `P(x,y)`, to the infinite-volume pair correlation. Both the property and envelope refer to actual site values, and the proof rewrites the selected finite vertices to these same sites. Constants do not gain dependence on the limiting law or on the sites.

`extendConfigurationWith` leaves spins inside the finite graph untouched and installs a deterministic exterior configuration otherwise. Its continuity is in the finite spin configuration, so no spatial regularity of the filler is needed. `extendedFreeGibbsWith_const` exactly recovers the old embedding. For vertices inside the graph, the two-spin marginal agrees exactly with the intrinsic finite-volume marginal. Along exhaustion, this gives eventual equality, and hence equivalent convergence, for fillers varying independently with volume and site.

`hasLocalPairLimit_of_weak_limit_with` correctly shifts both the graph and the filler by the same pair-dependent prefix. The two signed/ferromagnetic wrappers then supply only the relevant uniform coupling bounds. These results establish the intended arbitrary-filler bridge; they do not need a converse asserting that pairwise convergence implies full weak convergence.

## Public mathematical interfaces (source reviewed)

`RP2.Paper.R` is the negative complex-bilinear second response, matching the note's normalized `W(A)=⟨exp H(A)⟩`; it is not a logarithmic Hessian. `R_conjugate` and symmetry imply that `R(h,conjugate h)` is real, and `R_hermitian_eq` proves explicitly that the real-valued wrapper does not discard a nonzero imaginary component. No positivity assumption is introduced.

The public Gram kernel `T(e,l)` has conjugation on the second edge index. The commutator current `q` retains the factor `1/2`, uses the conjugated second vertex field, and is proved purely imaginary. The family inequality is an exact alias of the established bound, including the smaller valid pair coefficient `4β`, rather than a postulated paper correspondence. It remains the fixed-axis-C analytic inequality with test functions vanishing on every pinned vertex.

`AveragingSystem.partition_replace_all` exports the multi-annulus equality of partition functions. Its proof successively applies the existing exact one-kernel replacement and preserves cross-invariance by commutation. Only nonzero remaindering parameters are needed for this algebraic identity; the existing positive-remainder bound provides the separate positivity interpretation when applicable. No independence is assumed.

`tetraAction_sum_Q_zero` proves cancellation entry by entry for the actual twelve-element tetrahedral action, using the unit-spin identity. The normalized tensor and scalar versions use `1/12`, consistent with the group's already established cardinality and the quadrupole convention `Q=nnᵀ−I/3`. No appeal to a full-SO(3) average is introduced.

## Completed signed finite-volume and limit statements (source reviewed)

`SignedDyadicKernelComparison` reproduces the original actual-kernel proposition with exactly one hypothesis change: `|b_e|≤β` replaces the two-sided ferromagnetic condition. The proof now directly feeds this bound to the established axis-C comparison. Its threshold and error constants are selected uniformly before graph, couplings, rotations, pins, and configurations. The old proposition and constructors are retained by specialization.

The generic `factorial_of_dyadic_kernel_bounds` isolates the chosen graph's kernel comparisons without sign conditions. Its annulus geometry, strict separation condition, count, and product-to-factorial estimate are unchanged. `uniform_decay_of_factorial_bound` factors out an arbitrary coupling-admissibility predicate, avoiding duplication without weakening the required common factorial envelope.

All three signed headline finite-volume theorems quantify their constants before the graph, all couplings, and both observation sites. They retain the literal normalized Gibbs correlation, the same ℓ∞ radius, the same empty-annulus convention, and the same leading logarithmic coefficient `1/log 4`. The original ferromagnetic theorem statements remain available with their original mathematical meanings.

The signed local-limit superpolynomial, factorial, and logarithmic theorems select constants before the limiting law and sites, then transfer the exact finite-volume envelope. In particular, the logarithmic theorem preserves its distance threshold; the factorial theorem retains the finite-volume values of `D` and `a`. Their ferromagnetic versions are straightforward specializations. Weighted absolute summability follows for every real weight exponent from the signed superpolynomial theorem by the previously checked square-lattice summability estimate. No positivity of the signed correlation itself is used.

## Smooth structure factors (source reviewed)

`momentumPhase x y` is the actual real continuous-linear pairing `k₁(y₁−x₁)+k₂(y₂−x₂)` on `Momentum = ℝ×ℝ`. `fourierTerm` uses `C(y) exp(i k·(y−x))`, with no `2π` factor. The product norm on momentum is harmless; its dual norm is bounded by twice the ℓ∞ lattice radius, and the implemented looser `2(1+r)` majorant works at the origin as well.

The natural-order moment hypothesis is sufficient for every finite derivative order. The proof bounds the norm of the n-th Fréchet derivative of each term uniformly in momentum by `2·2^n(1+r)^n|C(y)|`. The trigonometric oscillator estimate is deliberately nonsharp but valid, including n=0. The termwise bounds then supply summable majorants to Mathlib's smooth-series theorem. This proves joint real `C∞` regularity as a map from two-dimensional momentum space to the complex plane, not merely separate differentiability in each coordinate.

`summable_fourierTerm` separately proves actual absolute convergence at each momentum. `iteratedFDeriv_latticeFourierSeries` supplies the correct derivative/sum interchange for every natural order. Thus the statement does not exploit Lean's default totalized value for divergent `tsum`.

The applications obtain the natural-order moments from the signed/ferromagnetic local-limit weighted summability theorem via the real-power/natural-power identity. Translation invariance is unnecessary for the fixed-base-point Fourier series defined here. With translation invariance it has the conventional interpretation and is independent of the base point; that identification is explanatory prose rather than a newly exported translation-invariance theorem. No analyticity, exponential decay, positivity of the Fourier transform, or existence/uniqueness of the limiting law is claimed.

## Source-review verdict

No mathematical or semantic blocker was found in the completed new signed-coupling, local-limit, exterior-filler, paper-interface, tensor-cancellation, remainder-normalization, or structure-factor sources. Compilation, axiom gates, and release artifact agreement remain separate required checks by the coordinator. This is an incremental review of the changed proof and interfaces, building on the earlier full audit of the preserved original release; it is not a claim of a new independent-kernel validation.

## Verification workflow review

The pinned toolchain and package manifest are checked before and after cache retrieval and again at completion; the workflow never invokes `lake update`. Every package must be at its recorded revision and have no modified tracked or untracked files. The runner checks that every project module belongs to the entrypoint import closure, compiles them in dependency order, enforces standalone/source agreement, and compiles the literal Gibbs-integral and normalization witnesses.

The raw dependency driver follows declaration types and bodies, includes mutual-inductive siblings, rejects any axiom except `propext`, `Classical.choice`, and `Quot.sound`, and rejects unsafe or partial dependencies of the listed public theorem roots. Its optional replay uses the same Lean kernel starting from an empty environment. Audit-only metaprogramming is not imported by the proof. The public roots include the new signed, limit, filler, response, tensor, remainder, and Fourier API families.

The review identified minor reproducibility weaknesses in an initial runner draft, all resolved before the release run: resumed checks now verify their log hashes as well as output object hashes; semantic checks, axiom reports, and raw dependency/replay gates always rerun; dependency cleanliness includes untracked files; and no project source module can be silently omitted from the import closure. Fresh standalone replay puts the newly generated object ahead of all other import paths. These were verification-workflow improvements, not defects in a proof theorem.

The GitHub workflow pins its action revisions and Lean release archive checksum and runs the same local verifier. Actual hosted GitHub execution is distinct from local validation and should not be claimed unless a hosted run has occurred.
