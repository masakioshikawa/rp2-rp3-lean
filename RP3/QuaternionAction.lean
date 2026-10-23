module

public import RP3.RotationGeometryBase
public import RP3.NestedCuts

public section

/-! The eight quaternion units acting on the unit sphere in real four-space. -/
namespace RP3
open MeasureTheory
open scoped BigOperators InnerProductSpace Pointwise

@[ext] structure Quaternion where
  index : Fin 8
  deriving DecidableEq, Fintype

@[expose] def quaternionMul (g h : Quaternion) : Quaternion :=
  ⟨![![0, 1, 2, 3, 4, 5, 6, 7],
    ![1, 4, 3, 6, 5, 0, 7, 2],
    ![2, 7, 4, 1, 6, 3, 0, 5],
    ![3, 2, 5, 4, 7, 6, 1, 0],
    ![4, 5, 6, 7, 0, 1, 2, 3],
    ![5, 0, 7, 2, 1, 4, 3, 6],
    ![6, 3, 0, 5, 2, 7, 4, 1],
    ![7, 6, 1, 0, 3, 2, 5, 4]] g.index h.index⟩
@[expose] def quaternionInv (g : Quaternion) : Quaternion :=
  ⟨![0,5,6,7,4,1,2,3] g.index⟩

set_option maxHeartbeats 3000000 in
@[expose] instance : Group Quaternion where
  mul := quaternionMul
  one := ⟨0⟩
  inv := quaternionInv
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

@[expose] def quaternionIndex : Quaternion ≃ Fin 8 where
  toFun g := g.index
  invFun i := ⟨i⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem quaternion_card : Fintype.card Quaternion = 8 := by
  rw [Fintype.card_congr quaternionIndex]
  decide

@[simp] theorem quaternionRotate_one (u : Fin 4 → ℝ) :
    quaternionRotate (1 : Quaternion).index u = u := by
  change quaternionRotate 0 u = u
  ext i
  fin_cases i <;> rfl

set_option maxHeartbeats 2000000 in
theorem quaternionRotate_mul (g h : Quaternion) (u : Fin 4 → ℝ) :
    quaternionRotate (g*h).index u = quaternionRotate g.index (quaternionRotate h.index u) := by
  rcases g with ⟨g⟩
  rcases h with ⟨h⟩
  change quaternionRotate (quaternionMul ⟨g⟩ ⟨h⟩).index u = _
  fin_cases g <;> fin_cases h <;> ext i <;> fin_cases i <;>
    simp [quaternionMul, quaternionRotate]

@[expose] noncomputable def quaternionLinear (g : Quaternion) : E4 →ₗ[ℝ] E4 where
  toFun u := WithLp.toLp 2 (quaternionRotate g.index u)
  map_add' u v := by
    rcases g with ⟨g⟩
    ext i
    fin_cases g <;> fin_cases i <;> simp [quaternionRotate, PiLp.add_apply, add_comm]
  map_smul' r u := by
    rcases g with ⟨g⟩
    ext i
    fin_cases g <;> fin_cases i <;> simp [quaternionRotate, PiLp.smul_apply]

@[simp] theorem quaternionLinear_apply (g : Quaternion) (u : E4) (i : Fin 4) :
    quaternionLinear g u i = quaternionRotate g.index u i := rfl

@[simp] theorem quaternionLinear_one (u : E4) : quaternionLinear 1 u = u := by
  ext i
  exact congrFun (quaternionRotate_one u) i

theorem quaternionLinear_mul (g h : Quaternion) (u : E4) :
    quaternionLinear (g*h) u = quaternionLinear g (quaternionLinear h u) := by
  ext i
  exact congrFun (quaternionRotate_mul g h u) i

theorem quaternionLinear_norm (g : Quaternion) (u : E4) :
    ‖quaternionLinear g u‖ = ‖u‖ := by
  have hs : ‖quaternionLinear g u‖^2 = ‖u‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    exact quaternionRotate_squares g.index u
  nlinarith [norm_nonneg (quaternionLinear g u), norm_nonneg u]

@[expose] noncomputable def quaternionLinearIsometry (g : Quaternion) : E4 ≃ₗᵢ[ℝ] E4 where
  toLinearEquiv := {
    quaternionLinear g with
    invFun := quaternionLinear g⁻¹
    left_inv := fun u => by
      change quaternionLinear g⁻¹ (quaternionLinear g u) = u
      rw [← quaternionLinear_mul, inv_mul_cancel, quaternionLinear_one]
    right_inv := fun u => by
      change quaternionLinear g (quaternionLinear g⁻¹ u) = u
      rw [← quaternionLinear_mul, mul_inv_cancel, quaternionLinear_one] }
  norm_map' := quaternionLinear_norm g

@[expose] noncomputable def quaternionAction : FiniteAction Quaternion Spin where
  move g := ⟨Rotation.spinRotation (quaternionLinearIsometry g),
    (Rotation.spinRotation (quaternionLinearIsometry g)).continuous⟩
  one_apply s := Subtype.ext (quaternionLinear_one s.val)
  mul_apply g h s := Subtype.ext (quaternionLinear_mul g h s.val)

@[simp] theorem quaternionAction_val (g : Quaternion) (s : Spin) :
    (quaternionAction.move g s).val = quaternionLinear g s.val := rfl

theorem quaternionAction_sum_qPair_zero (s t : Spin) :
    ∑ g : Quaternion, qPair (quaternionAction.move g s) t = 0 := by
  have h := quaternion_cancellation s.val t.val (spin_squares s) (spin_squares t)
  rw [← Equiv.sum_comp quaternionIndex] at h
  change (∑ g : Quaternion,
    ((∑ i : Fin 4, quaternionRotate g.index s.val i * t.val i)^2 - (1:ℝ)/4)) = 0 at h
  simpa only [qPair, quaternionAction_val, PiLp.inner_apply, Real.inner_apply,
    quaternionLinear_apply] using h


theorem quaternionAction_measurePreserving (g : Quaternion) :
    MeasurePreserving (quaternionAction.move g) sphereProbability sphereProbability :=
  Rotation.spinRotation_preserves_probability (quaternionLinearIsometry g)

@[simp] theorem quaternionAction_eq_spinRotation (g : Quaternion) (s : Spin) :
    quaternionAction.move g s = Rotation.spinRotation (quaternionLinearIsometry g) s := rfl

/-- On a separating cut the quadrupolar observable has exactly zero average. -/
theorem quaternionAction_cut_average_zero {V : Type*} [Fintype V] [DecidableEq V]
    (cut : Finset V) (x y : V) (hx : x ∈ cut) (hy : y ∉ cut) :
    (quaternionAction.onCut cut).average (observable x y) = 0 := by
  ext σ
  simp only [FiniteAction.average_apply, observable, ContinuousMap.coe_mk,
    FiniteAction.onCut_apply, hx, hy, ite_true, ite_false, ContinuousMap.zero_apply]
  rw [quaternionAction_sum_qPair_zero, mul_zero]

/-- Concrete averaging system for any nested chain of spatial cuts. -/
@[expose] noncomputable def quaternionNestedSystem {V ι : Type*} [Fintype V] [DecidableEq V]
    (cuts : ι → Finset V) (hchain : ∀ i j, cuts i ⊆ cuts j ∨ cuts j ⊆ cuts i) :
    AveragingSystem (integralOnCompact (referenceLaw (V := V))) ι :=
  quaternionAction.nestedSystem sphereProbability quaternionAction_measurePreserving cuts hchain

end RP3
