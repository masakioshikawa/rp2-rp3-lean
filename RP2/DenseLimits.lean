module

public import RP2.TwoEndpointRates
public import RP2.LimitCorollary

public section

/-!
# Stronger annular decay in free-boundary local limits

Both the adjacent-scale estimate and its two-endpoint square pass to every
signed-coupling free-boundary local limit with exactly the finite-volume
constants and distance thresholds. Ferromagnetic local limits are included.
-/
namespace RP2
noncomputable section
open MeasureTheory

/-- The factorial estimate passes to signed-coupling local limits with exactly
the finite-volume annulus scale and coefficient. -/
theorem dense_factorial_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      let r := (Fourier.siteRadius x y).toNat
      let k := denseAnnulusCount (2^a) r (by positivity)
      |infiniteCorrelation μ x y| ≤ (2:ℝ)/3 * D^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hbound⟩ := dense_factorial_quadrupolar_decay_signed β hβ
  refine ⟨D, hD, a, ha, ?_⟩
  intro μ hμ x y
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => let k := denseAnnulusCount (2^a) (Fourier.siteRadius x y).toNat (by positivity)
      (2:ℝ)/3 * D^k/k.factorial)
    (fun n u v _ => hbound (G n) (b n) (hb n) u v) x y trivial

/-- The factorial estimate in a ferromagnetic local weak limit. -/
theorem dense_factorial_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      let r := (Fourier.siteRadius x y).toNat
      let k := denseAnnulusCount (2^a) r (by positivity)
      |infiniteCorrelation μ x y| ≤ (2:ℝ)/3 * D^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hbound⟩ := dense_factorial_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨D, hD, a, ha, fun μ hμ => hbound μ hμ.signed⟩

/-- The explicit logarithmic rate in signed-coupling local limits, preserving
both the finite-volume coefficient and its distance threshold. -/
theorem dense_logarithmic_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      R ≤ (Fourier.siteRadius x y).toNat →
      |infiniteCorrelation μ x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x y : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := dense_logarithmic_quadrupolar_decay_signed β hβ
  refine ⟨C, hC, R, ?_⟩
  intro μ hμ x y hr
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound
    (fun x y => R ≤ (Fourier.siteRadius x y).toNat)
    (fun x y => Real.exp (-Real.log (Fourier.siteRadius x y : ℝ) *
      Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 2 +
      C * Real.log (Fourier.siteRadius x y : ℝ)))
    (fun n u v huv => hbound (G n) (b n) (hb n) u v huv) x y hr

/-- The explicit logarithmic rate in ferromagnetic local weak limits. -/
theorem dense_logarithmic_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      R ≤ (Fourier.siteRadius x y).toNat →
      |infiniteCorrelation μ x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x y : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := dense_logarithmic_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨C, hC, R, fun μ hμ => hbound μ hμ.signed⟩

/-- The factorial estimate passes to signed-coupling local limits with exactly
the finite-volume annulus scale and coefficient. -/
theorem two_endpoint_factorial_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      let r := (Fourier.siteRadius x y).toNat
      let k := denseAnnulusCount (2^(a+1)) r (by positivity)
      |infiniteCorrelation μ x y| ≤ (2:ℝ)/3 * (D^k/k.factorial)^2 := by
  obtain ⟨D, hD, a, ha, hbound⟩ := two_endpoint_factorial_quadrupolar_decay_signed β hβ
  refine ⟨D, hD, a, ha, ?_⟩
  intro μ hμ x y
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => let k := denseAnnulusCount (2^(a+1)) (Fourier.siteRadius x y).toNat (by positivity)
      (2:ℝ)/3 * (D^k/k.factorial)^2)
    (fun n u v _ => hbound (G n) (b n) (hb n) u v) x y trivial

/-- The factorial estimate in a ferromagnetic local weak limit. -/
theorem two_endpoint_factorial_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      let r := (Fourier.siteRadius x y).toNat
      let k := denseAnnulusCount (2^(a+1)) r (by positivity)
      |infiniteCorrelation μ x y| ≤ (2:ℝ)/3 * (D^k/k.factorial)^2 := by
  obtain ⟨D, hD, a, ha, hbound⟩ := two_endpoint_factorial_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨D, hD, a, ha, fun μ hμ => hbound μ hμ.signed⟩

/-- The explicit logarithmic rate in signed-coupling local limits, preserving
both the finite-volume coefficient and its distance threshold. -/
theorem two_endpoint_logarithmic_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      R ≤ (Fourier.siteRadius x y).toNat →
      |infiniteCorrelation μ x y| ≤
        Real.exp (-2*Real.log (Fourier.siteRadius x y : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := two_endpoint_logarithmic_quadrupolar_decay_signed β hβ
  refine ⟨C, hC, R, ?_⟩
  intro μ hμ x y hr
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound
    (fun x y => R ≤ (Fourier.siteRadius x y).toNat)
    (fun x y => Real.exp (-2*Real.log (Fourier.siteRadius x y : ℝ) *
      Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 2 +
      C * Real.log (Fourier.siteRadius x y : ℝ)))
    (fun n u v huv => hbound (G n) (b n) (hb n) u v huv) x y hr

/-- The explicit logarithmic rate in ferromagnetic local weak limits. -/
theorem two_endpoint_logarithmic_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      R ≤ (Fourier.siteRadius x y).toNat →
      |infiniteCorrelation μ x y| ≤
        Real.exp (-2*Real.log (Fourier.siteRadius x y : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x y : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := two_endpoint_logarithmic_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨C, hC, R, fun μ hμ => hbound μ hμ.signed⟩

end
end RP2
