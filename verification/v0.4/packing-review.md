# Log-square packing and rate review

The modules `RP2.LogSquareRates`, `RP2.LogSquarePacking`, and `RP2.LogSquareLimits` compile under the configured Lean toolchain with default asynchronous elaboration. They introduce no axioms or placeholders. The endpoint module compiled successfully after the actual response-to-comparison existence theorem was completed (5.9 seconds).

## Exact packing

At scale n, choose h(n) from `ThinScaleChoice`, width w=2^(n-h), and m=2^(h-1). For each 0<=j<m retain [R,S] with R=2^n+2jw and S=R+w. The identity 2mw=2^n proves S<2^(n+1). Consecutive shells are separated by w. Shells in different dyadic bands are ordered and disjoint. The existing exact kernel product theorem is applied to the finite lexicographic sigma type of band and shell indices; its cardinal is exactly the sum of shell counts.

If k=denseAnnulusCount(2^a,r), every selected band a+j with j<k has outer radius strictly below r. Thus every selected shell separates the two sites. This is valid also when r is exactly a power of two: the count definition uses a non-strict cover and strictly smaller earlier thresholds.

## Quadratic count and rate conversion

The scale choice gives n <= 2*A*2^h=4*A*m. Hence m(a+j)>=j/(4*A). With gamma=1/(4*A), the cumulative count is at least gamma*k^2/4-gamma/4, by summing j and using (k-1)^2>=0. The exact half-power contraction is bounded by exp(log(2)*gamma/4)*exp(-d*k^2), d=log(2)*gamma/4.

No asymptotic floor/log estimate is needed. The covering count gives log(2+r)<=a0+k*log(2), a0=log(2*N+2). Both sides are nonnegative, so log(2+r)^2<=2*a0^2+2*k^2*log(2)^2. Set c=d/(2*log(2)^2), and absorb exp(2*c*a0^2) into the prefactor. This yields the requested all-distance C*exp(-c*log(2+r)^2), including r=0.

## Scope and uniformity

Constants are selected from beta-dependent analytic comparison constants before graph, coupling, or site choices. Signed couplings are primary; the ferromagnetic theorem is a specialization. The local-limit theorem transfers the same finite-volume bound through the existing bounded continuous pair-observable interface; no uniqueness or arbitrary-Gibbs-state assertion is made.

## Analytic hypothesis discharged

`log_square_of_thin_comparison_signed` exposes the exact analytic hypothesis `SignedThinDyadicKernelComparison`. The compiled public endpoint obtains it from `Fourier.LatticeGraph.exists_thinKernelComparison_signed`, which in turn uses the actual finite-graph thin-annulus response and exact restriction/rotation identities. None of the four public endpoint statements retains an analytic comparison hypothesis.

Public exports:
- `RP2.log_square_quadrupolar_decay_signed`
- `RP2.log_square_quadrupolar_decay`
- `RP2.log_square_quadrupolar_decay_local_limit_signed`
- `RP2.log_square_quadrupolar_decay_local_limit`

Whole-project raw dependency, axiom, kernel replay, and standalone checks are performed separately by the release validation; this review does not claim their results in advance.
