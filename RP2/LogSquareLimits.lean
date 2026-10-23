module

public import RP2.ThinKernelEstimate
public import RP2.LimitCorollary

public section

/-!
# Uniform log-square quadrupolar decay

The constants are chosen before the graph, the signed couplings, and the
marked sites.  The same constants pass to every existing free-boundary
local limit.  No existence or uniqueness of an infinite-volume Gibbs state
is assumed or concluded by the limit transfer.
-/
namespace RP2
noncomputable section
open MeasureTheory

/-- All-temperature log-square decay for the actual finite RP² model with
arbitrary bounded signed couplings. -/
theorem log_square_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        C * Real.exp (-c * (Real.log (2+(Fourier.siteRadius x.val y.val:ℝ)))^2) := by
  obtain ⟨E, hE, F, hF, hcomparison⟩ :=
    Fourier.LatticeGraph.exists_thinKernelComparison_signed β hβ
  exact log_square_of_thin_comparison_signed β E F hE hF hcomparison

/-- Ferromagnetic specialization of the uniform all-temperature theorem. -/
theorem log_square_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        C * Real.exp (-c * (Real.log (2+(Fourier.siteRadius x.val y.val:ℝ)))^2) := by
  obtain ⟨C, hC, c, hc, hbound⟩ := log_square_quadrupolar_decay_signed β hβ
  exact ⟨C, hC, c, hc, fun G b hb x y => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y⟩

/-- The all-distance log-square estimate passes to signed-coupling local
limits with exactly the constants chosen in finite volume. -/
theorem log_square_quadrupolar_decay_local_limit_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      |infiniteCorrelation μ x y| ≤
        C * Real.exp (-c * (Real.log (2+(Fourier.siteRadius x y:ℝ)))^2) := by
  obtain ⟨C, hC, c, hc, hbound⟩ := log_square_quadrupolar_decay_signed β hβ
  refine ⟨C, hC, c, hc, ?_⟩
  intro μ hμ x y
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => C * Real.exp (-c * (Real.log (2+(Fourier.siteRadius x y:ℝ)))^2))
    (fun n u v _ => hbound (G n) (b n) (hb n) u v) x y trivial

/-- Ferromagnetic free-boundary local limits satisfy the same bound. -/
theorem log_square_quadrupolar_decay_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      |infiniteCorrelation μ x y| ≤
        C * Real.exp (-c * (Real.log (2+(Fourier.siteRadius x y:ℝ)))^2) := by
  obtain ⟨C, hC, c, hc, hbound⟩ := log_square_quadrupolar_decay_local_limit_signed β hβ
  exact ⟨C, hC, c, hc, fun μ hμ => hbound μ hμ.signed⟩

end
end RP2
