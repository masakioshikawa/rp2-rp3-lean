# v0.4 source correspondence and scope review

## All-temperature log-square theorem

The new endpoint `RP2.log_square_quadrupolar_decay_signed` is a theorem
about the existing actual normalized Gibbs correlation. Its only model
assumptions are β≥0, the finite retained nearest-neighbor square-lattice
graph, and |b(e)|≤β. The positive constants precede all graph/coupling/site
choices. It does not assume an analytic response or a kernel comparison.

The proof chain was checked at the following interfaces:

- ThinProfiles rescales the previously verified fixed profiles using a
  signed plateau map. At its corners, short steps map into a region where
  the directional gradient and exact profile-product difference vanish.
  The discrete trapezoid estimate therefore remains valid uniformly in
  the annulus location parameter a.
- ThinFourier zeroes complete low-frequency shells; reflection preserves
  each shell, hence the transverse sine cancellation remains exact.
  The normalization is at least k/4 when 2h≤k. Full-k upper cost sums
  introduce only a harmless constant factor.
- The Bessel estimate applies to the entire family with a bounded diagonal
  multiplier. It assumes neither periodic profiles nor independent shells.
- ThinSupport counts origins in a closed annulus and uses injectivity of
  origin plus positive direction. This yields at most 64N(S−R) supported
  edges, including origins on the inner pinned boundary.
- The Gram estimate retains each column's spatial-support bound separately
  from the operator norm. This supplies the essential single inverse power
  of the relative annular width.
- ThinResponse substitutes these proved bounds into the actual squared
  interaction Ward estimate and actual real-response transfer. No model
  estimate is supplied as an axiom.
- ThinKernel and ThinKernelEstimate prove exact restriction, translation,
  arbitrary pinned-boundary rotation, periodic comparison and tetrahedral
  comparison. Every required rotation angle and boundary array is covered.
- ThinAnnuli allocates an edge to a kernel exactly when it meets the strict
  interior. Width≥2 ensures every cut-crossing edge is allocated. Shared
  pinned boundaries are allowed; the edge/cut conditions needed by the
  exact product theorem are proved.
- ThinScaleChoice chooses scales before the model and obtains contraction
  at most 1/2 with linearly many shells per dyadic band. LogSquarePacking
  uses an explicit finite ordered sigma type and its exact cardinality.
- LogSquareRates converts the quadratic band exponent into an all-distance
  log(2+r)^2 envelope. LogSquareLimits transfers the identical constants
  through convergence of actual two-spin Gibbs marginals.

## Direct high-temperature exponential theorem

The signed activity shift exp[b(s·t)^2−min(b,0)] makes every activity
nonnegative and cancels exactly from numerator and partition. Prescribed
active-edge-set probabilities are bounded by a pointwise product estimate,
not by assuming independence or FKG. A connected active configuration
contains a simple path; its prefix of exactly the lattice distance is
counted by 4·3^(r−1). The graph's degree-four and edge-injectivity hypotheses,
and the lower bound of path length by lattice distance, are proved.

The direct bound is (8/9)[3(1−exp(−β))]^r. The explicit mass
−log(max(1/2,3(1−exp(−β)))) is positive for 0≤β<log(3/2).
The same-site and β=0 cases are included, and the local-limit constants
are unchanged. No external percolation theorem or connectivity estimate
is assumed by the public endpoint.

## Boundaries

The optimized FK thresholds in the analytical note remain unformalized.
The formal infinite-volume scope is existing free-boundary local limits;
there is no assertion of existence, uniqueness, general DLR identification,
continuum limit, all-observable clustering, or all-temperature exponential
decay. These source reviews accompany compilation and dependency checks;
they are not represented as a new full independent audit of the release.
