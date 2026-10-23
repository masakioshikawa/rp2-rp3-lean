module

public import RP2.TetrahedralPaths

public section

/-!
# From one periodic axis estimate to the tetrahedral comparison

The only analytic input is the pointwise comparison for the axis-C cut rotation.
Global rotational invariance transfers it to each coordinate axis.  The exact
three-factor decomposition then gives the finite-group kernel comparison.
-/
namespace RP2

noncomputable section
open Rotation

variable {V : Type*} [DecidableEq V]

/-- Rotate every spin of a configuration by the same tetrahedral element. -/
@[expose] def tetraGlobalMove (g : Tetrahedral) (σ : Configuration V) : Configuration V :=
  fun v => tetraAction.move g (σ v)

/-- Rotate only sites in a cut by an arbitrary orthogonal transformation. -/
@[expose] def rotateCut (cut : Finset V) (R : E3 ≃ₗᵢ[ℝ] E3)
    (σ : Configuration V) : Configuration V :=
  fun v => if v ∈ cut then Rotation.spinRotation R (σ v) else σ v

/-- One coordinate-axis rotation localized to a cut. -/
@[expose] def coordinateCut (cut : Finset V) (a : Fin 3) (t : ℝ)
    (σ : Configuration V) : Configuration V :=
  rotateCut cut (coordinateRotation a t) σ

theorem global_coordinateCut_intertwine (cut : Finset V) (a : Fin 3) (t : ℝ)
    (σ : Configuration V) :
    tetraGlobalMove (axisConjugator a) (coordinateCut cut a t σ) =
      coordinateCut cut 2 t (tetraGlobalMove (axisConjugator a) σ) := by
  funext v
  by_cases hv : v ∈ cut
  · simpa only [tetraGlobalMove, coordinateCut, rotateCut, hv, ite_true] using
      spinRotation_intertwine_axisC a t (σ v)
  · simp only [tetraGlobalMove, coordinateCut, rotateCut, hv, ite_false]

/-- Global invariance transports the single-axis analytic estimate to all axes. -/
theorem coordinateCut_comparison_of_axisC (K : Configuration V → ℝ)
    (hglobal : ∀ g σ, K (tetraGlobalMove g σ) = K σ)
    (cut : Finset V) (η : ℝ)
    (hC : ∀ t σ, (1 - η) * K (coordinateCut cut 2 t σ) ≤ K σ)
    (a : Fin 3) (t : ℝ) (σ : Configuration V) :
    (1 - η) * K (coordinateCut cut a t σ) ≤ K σ := by
  have h := hC t (tetraGlobalMove (axisConjugator a) σ)
  rw [← global_coordinateCut_intertwine, hglobal, hglobal] at h
  exact h

/-- The tetrahedral cut action is the composition of three coordinate cut rotations. -/
theorem tetraCut_eq_three_coordinateCuts (cut : Finset V) (g : Tetrahedral)
    (σ : Configuration V) :
    (tetraAction.onCut cut).move g σ =
      coordinateCut cut (tetraPathAxis g 0) (tetraPathAngle g 0)
        (coordinateCut cut (tetraPathAxis g 1) (tetraPathAngle g 1)
          (coordinateCut cut (tetraPathAxis g 2) (tetraPathAngle g 2) σ)) := by
  funext v
  by_cases hv : v ∈ cut
  · simp only [FiniteAction.onCut_apply, coordinateCut, rotateCut, hv, ite_true]
    apply Subtype.ext
    exact tetraLinearIsometry_eq_three_rotations g (σ v).val
  · simp only [FiniteAction.onCut_apply, coordinateCut, rotateCut, hv, ite_false]

/-- Three comparisons multiply to a cube, which is at least `1 - 3η` on `[0,1]`. -/
theorem tetraCut_comparison_of_axisC (K : Configuration V → ℝ)
    (hK : ∀ σ, 0 ≤ K σ)
    (hglobal : ∀ g σ, K (tetraGlobalMove g σ) = K σ)
    (cut : Finset V) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hC : ∀ t σ, (1 - η) * K (coordinateCut cut 2 t σ) ≤ K σ)
    (g : Tetrahedral) (σ : Configuration V) :
    (1 - 3 * η) * K ((tetraAction.onCut cut).move g σ) ≤ K σ := by
  let σ₁ := coordinateCut cut (tetraPathAxis g 2) (tetraPathAngle g 2) σ
  let σ₂ := coordinateCut cut (tetraPathAxis g 1) (tetraPathAngle g 1) σ₁
  let σ₃ := coordinateCut cut (tetraPathAxis g 0) (tetraPathAngle g 0) σ₂
  have h₁ : (1 - η) * K σ₁ ≤ K σ :=
    coordinateCut_comparison_of_axisC K hglobal cut η hC _ _ _
  have h₂ : (1 - η) * K σ₂ ≤ K σ₁ :=
    coordinateCut_comparison_of_axisC K hglobal cut η hC _ _ _
  have h₃ : (1 - η) * K σ₃ ≤ K σ₂ :=
    coordinateCut_comparison_of_axisC K hglobal cut η hC _ _ _
  have hc : 0 ≤ 1 - η := sub_nonneg.mpr hη1
  have hpow : (1 - η)^3 * K σ₃ ≤ K σ := by
    calc
      (1 - η)^3 * K σ₃ = (1 - η) * ((1 - η) * ((1 - η) * K σ₃)) := by ring
      _ ≤ (1 - η) * ((1 - η) * K σ₂) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₃ hc) hc
      _ ≤ (1 - η) * K σ₁ := mul_le_mul_of_nonneg_left h₂ hc
      _ ≤ K σ := h₁
  have hb : 1 - 3 * η ≤ (1 - η)^3 := by
    nlinarith [mul_nonneg (sq_nonneg η) (show 0 ≤ 3 - η by linarith)]
  rw [tetraCut_eq_three_coordinateCuts]
  exact (mul_le_mul_of_nonneg_right hb (hK σ₃)).trans hpow

end
end RP2
