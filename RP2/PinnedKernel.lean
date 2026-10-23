import RP2.Model
import RP2.PeriodicODE

/-!
# Pinned partition functions and the curvature-to-comparison interface

We define the pinned RP² partition function itself and show that a periodic
second-derivative bound implies the rotational kernel comparison. This is a
reusable conditional interface. The actual squared-interaction estimate is
proved in `AnnularEstimate.lean` and connected to these pinned integrals in
`KernelEstimate.lean`; the final decay theorems have no analytic hypothesis.
-/

namespace RP2

open MeasureTheory

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- Overwrite pinned sites with the prescribed boundary configuration. -/
noncomputable def fillPins (pins : Finset V) (τ : Configuration V) :
    C(Configuration V, Configuration V) :=
  ⟨fun σ v => if v ∈ pins then τ v else σ v, by
    apply continuous_pi
    intro v
    by_cases hv : v ∈ pins
    · simpa only [hv, ite_true] using (continuous_const : Continuous (fun _ : Configuration V => τ v))
    · simpa only [hv, ite_false] using (continuous_apply v : Continuous (fun σ : Configuration V => σ v))⟩

/-- Pinned spins are dummy integration variables with probability mass one. -/
noncomputable def pinnedWeight (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (τ : Configuration V) : C(Configuration V, ℝ) :=
  (weight edge b).comp (fillPins pins τ)

noncomputable def pinnedPartition (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (τ : Configuration V) : ℝ :=
  (integralOnCompact (referenceLaw (V := V))).linear (pinnedWeight edge b pins τ)

theorem pinnedPartition_pos (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (τ : Configuration V) : 0 < pinnedPartition edge b pins τ := by
  change 0 < ∫ σ, Real.exp (interaction edge b (fillPins pins τ σ)) ∂referenceLaw
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    ((pinnedWeight edge b pins τ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).mpr
  have hs : Function.support (fun σ : Configuration V =>
      Real.exp (interaction edge b (fillPins pins τ σ))) = Set.univ := by
    ext σ
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

/-- Rotate all directors in the inner boundary by the same motion. -/
noncomputable def twistBoundary (inner : Finset V) (ρ : ℝ → C(Spin, Spin))
    (τ : Configuration V) (t : ℝ) : Configuration V :=
  fun v => if v ∈ inner then ρ t (τ v) else τ v

noncomputable def twistedPartition (edge : E → V × V) (b : E → ℝ)
    (pins inner : Finset V) (ρ : ℝ → C(Spin, Spin)) (τ : Configuration V) : ℝ → ℝ :=
  fun t => pinnedPartition edge b pins (twistBoundary inner ρ τ t)

theorem twistedPartition_periodic (edge : E → V × V) (b : E → ℝ)
    (pins inner : Finset V) (ρ : ℝ → C(Spin, Spin)) (τ : Configuration V)
    (P : ℝ) (hρ : Function.Periodic ρ P) :
    Function.Periodic (twistedPartition edge b pins inner ρ τ) P := by
  intro t
  change pinnedPartition edge b pins (twistBoundary inner ρ τ (t + P)) =
    pinnedPartition edge b pins (twistBoundary inner ρ τ t)
  apply congrArg (pinnedPartition edge b pins)
  funext v
  change (if v ∈ inner then ρ (t + P) (τ v) else τ v) =
    (if v ∈ inner then ρ t (τ v) else τ v)
  rw [hρ t]

/-- The analytic obligation. The desired annular input has
`δ = constant(β) / log N`, uniformly in all boundary directors. -/
def CurvatureBound (Z : ℝ → ℝ) (δ : ℝ) : Prop :=
  ∃ Z' Z'' : ℝ → ℝ,
    (∀ t, HasDerivAt Z (Z' t) t) ∧
    (∀ t, HasDerivAt Z' (Z'' t) t) ∧
    (∀ t, -(δ * Z t) ≤ Z'' t)

/-- Applied to the actual pinned RP² partition function, a uniform curvature
bound gives the comparison needed by `FiniteAction.comparison_lower`.
The constant `P²/2` is sufficient; no claim of an optimal ODE constant is made. -/
theorem pinned_kernel_comparison (edge : E → V × V) (b : E → ℝ)
    (pins inner : Finset V) (ρ : ℝ → C(Spin, Spin)) (τ : Configuration V)
    (P δ : ℝ) (hP : 0 < P) (hδ : 0 ≤ δ) (hρ : Function.Periodic ρ P)
    (hcurv : CurvatureBound (twistedPartition edge b pins inner ρ τ) δ)
    (x y : ℝ) :
    (1 - δ * P ^ 2 / 2) * twistedPartition edge b pins inner ρ τ y ≤
      twistedPartition edge b pins inner ρ τ x := by
  obtain ⟨Z', Z'', h1, h2, hode⟩ := hcurv
  exact periodic_kernel_lower _ Z' Z'' P δ hP hδ
    (twistedPartition_periodic edge b pins inner ρ τ P hρ)
    (fun t => pinnedPartition_pos edge b pins _) h1 h2 hode x y

end RP2
