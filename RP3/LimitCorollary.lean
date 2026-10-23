module

public import RP3.Full
public import RP3.GibbsProbability
public import RP3.WeightedSummability

public section

/-!
# Local weak limits and weighted summability

All finite-volume decay envelopes pass to the corresponding local limits with
exactly the same constants. The signed-coupling statements include the original
ferromagnetic statements as corollaries.
-/
namespace RP3
noncomputable section
open MeasureTheory

/-- The signed-coupling superpolynomial bound passes to every local limit with
its original volume-independent constants. -/
theorem superpolynomial_quadrupolar_decay_local_limit_signed
    (β : ℝ) (hβ : 0 ≤ β) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      |infiniteCorrelation μ x y| ≤
        A * (1 + (Fourier.siteRadius x y : ℝ)) ^ (-p) := by
  obtain ⟨A, hA, hbound⟩ := superpolynomial_quadrupolar_decay_signed β hβ p
  refine ⟨A, hA, ?_⟩
  intro μ hμ x y
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => A * (1 + (Fourier.siteRadius x y : ℝ)) ^ (-p))
    (fun n u v _ => hbound (G n) (b n) (hb n) u v) x y trivial

/-- Corollary 5.1: ferromagnetic local weak limits obey the finite-volume bound
with the same volume-independent constants. -/
theorem superpolynomial_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      |infiniteCorrelation μ x y| ≤
        A * (1 + (Fourier.siteRadius x y : ℝ)) ^ (-p) := by
  obtain ⟨A, hA, hbound⟩ := superpolynomial_quadrupolar_decay_local_limit_signed β hβ p
  exact ⟨A, hA, fun μ hμ => hbound μ hμ.signed⟩

/-- The factorial estimate passes to signed-coupling local limits with exactly
the finite-volume annulus scale and coefficient. -/
theorem factorial_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      let r := (Fourier.siteRadius x y).toNat
      let k := annulusCount (2^a) r (by positivity)
      |infiniteCorrelation μ x y| ≤ (3 : ℝ) / 4 * (D/2)^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hbound⟩ := factorial_quadrupolar_decay_signed β hβ
  refine ⟨D, hD, a, ha, ?_⟩
  intro μ hμ x y
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => let k := annulusCount (2^a) (Fourier.siteRadius x y).toNat (by positivity)
      (3 : ℝ) / 4 * (D/2)^k/k.factorial)
    (fun n u v _ => hbound (G n) (b n) (hb n) u v) x y trivial

/-- The factorial estimate in a ferromagnetic local weak limit. -/
theorem factorial_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      let r := (Fourier.siteRadius x y).toNat
      let k := annulusCount (2^a) r (by positivity)
      |infiniteCorrelation μ x y| ≤ (3 : ℝ) / 4 * (D/2)^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hbound⟩ := factorial_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨D, hD, a, ha, fun μ hμ => hbound μ hμ.signed⟩

/-- The explicit logarithmic rate in signed-coupling local limits, preserving
both the finite-volume coefficient and its distance threshold. -/
theorem logarithmic_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      R ≤ (Fourier.siteRadius x y).toNat →
      |infiniteCorrelation μ x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x y : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 4 +
          C * Real.log (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := logarithmic_quadrupolar_decay_signed β hβ
  refine ⟨C, hC, R, ?_⟩
  intro μ hμ x y hr
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound
    (fun x y => R ≤ (Fourier.siteRadius x y).toNat)
    (fun x y => Real.exp (-Real.log (Fourier.siteRadius x y : ℝ) *
      Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 4 +
      C * Real.log (Fourier.siteRadius x y : ℝ)))
    (fun n u v huv => hbound (G n) (b n) (hb n) u v huv) x y hr

/-- The explicit logarithmic rate in ferromagnetic local weak limits. -/
theorem logarithmic_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      R ≤ (Fourier.siteRadius x y).toNat →
      |infiniteCorrelation μ x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x y : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 4 +
          C * Real.log (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := logarithmic_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨C, hC, R, fun μ hμ => hbound μ hμ.signed⟩

/-- Every polynomially weighted quadrupolar two-point series is absolutely
summable in a signed-coupling free-boundary local weak limit. -/
theorem weighted_summability_local_limit_signed (β : ℝ) (hβ : 0 ≤ β)
    (μ : ProbabilityMeasure InfiniteConfiguration) (hμ : IsSignedFreeBoundaryLocalLimit β μ)
    (x : Fourier.Site) (s : ℝ) :
    Summable (fun y : Fourier.Site =>
      (1 + (Fourier.siteRadius x y : ℝ))^s * |infiniteCorrelation μ x y|) := by
  apply Fourier.weighted_summable_of_decay x (infiniteCorrelation μ x) _ s
  intro p
  obtain ⟨A, hA, hbound⟩ := superpolynomial_quadrupolar_decay_local_limit_signed β hβ p
  exact ⟨A, hA, fun y => hbound μ hμ x y⟩

/-- Every polynomially weighted quadrupolar two-point series is absolutely
summable in a ferromagnetic free-boundary local weak limit. -/
theorem weighted_summability_local_limit (β : ℝ) (hβ : 0 ≤ β)
    (μ : ProbabilityMeasure InfiniteConfiguration) (hμ : IsFreeBoundaryLocalLimit β μ)
    (x : Fourier.Site) (s : ℝ) :
    Summable (fun y : Fourier.Site =>
      (1 + (Fourier.siteRadius x y : ℝ))^s * |infiniteCorrelation μ x y|) :=
  weighted_summability_local_limit_signed β hβ μ hμ.signed x s

end
end RP3
