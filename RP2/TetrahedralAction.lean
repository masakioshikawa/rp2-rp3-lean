module

public import RP2.RotationGeometry
public import RP2.NestedCuts

public section

/-!
# The actual twelve-element tetrahedral rotation action

The finite group is constructed by a multiplication table on `Fin 3 × Fin 4`.
The finite table identities are checked by explicit cases and reflexivity.
Its representation is exactly the signed cyclic permutations used in the
polynomial certificate in `Model.lean`.
-/

namespace RP2

open MeasureTheory
open scoped BigOperators InnerProductSpace Pointwise

/-- Cyclic coordinate permutation and one of four even sign changes. -/
@[ext] structure Tetrahedral where
  cycle : Fin 3
  sign : Fin 4
  deriving DecidableEq, Fintype

@[expose] def signProduct (a b : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a b

@[expose] def signShift (a : Fin 3) (b : Fin 4) : Fin 4 :=
  ![![0, 1, 2, 3], ![0, 3, 1, 2], ![0, 2, 3, 1]] a b

@[expose] def cycleInverse (a : Fin 3) : Fin 3 := ![0, 2, 1] a

@[expose] def tetraMul (g h : Tetrahedral) : Tetrahedral :=
  ⟨g.cycle + h.cycle, signProduct g.sign (signShift g.cycle h.sign)⟩

@[expose] def tetraInv (g : Tetrahedral) : Tetrahedral :=
  ⟨cycleInverse g.cycle, signShift (cycleInverse g.cycle) g.sign⟩

theorem signProduct_assoc (a b c : Fin 4) :
    signProduct (signProduct a b) c = signProduct a (signProduct b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

theorem signShift_product (a : Fin 3) (b c : Fin 4) :
    signShift a (signProduct b c) = signProduct (signShift a b) (signShift a c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

theorem signShift_add (a b : Fin 3) (c : Fin 4) :
    signShift (a + b) c = signShift a (signShift b c) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rfl

theorem tetraMul_assoc (g h k : Tetrahedral) :
    tetraMul (tetraMul g h) k = tetraMul g (tetraMul h k) := by
  apply Tetrahedral.ext
  · exact add_assoc g.cycle h.cycle k.cycle
  · change signProduct (signProduct g.sign (signShift g.cycle h.sign))
        (signShift (g.cycle + h.cycle) k.sign) =
      signProduct g.sign (signShift g.cycle (signProduct h.sign (signShift h.cycle k.sign)))
    rw [signProduct_assoc, signShift_add, signShift_product]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
@[expose] instance : Group Tetrahedral where
  mul := tetraMul
  one := ⟨0, 0⟩
  inv := tetraInv
  mul_assoc := tetraMul_assoc
  one_mul := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl
  mul_one := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl
  inv_mul_cancel := by
    rintro ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> rfl

@[simp] theorem tetra_one_cycle : (1 : Tetrahedral).cycle = 0 := rfl

@[simp] theorem tetra_one_sign : (1 : Tetrahedral).sign = 0 := rfl

@[simp] theorem tetra_mul_cycle (g h : Tetrahedral) :
    (g * h).cycle = g.cycle + h.cycle := rfl

@[simp] theorem tetra_mul_sign (g h : Tetrahedral) :
    (g * h).sign = signProduct g.sign (signShift g.cycle h.sign) := rfl

/-- The index equivalence used to reuse the finite polynomial certificate. -/
@[expose] def tetrahedralIndex : Tetrahedral ≃ Fin 3 × Fin 4 where
  toFun g := (g.cycle, g.sign)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem tetrahedralIndex_apply (g : Tetrahedral) :
    tetrahedralIndex g = (g.cycle, g.sign) := rfl

@[simp] theorem tetrahedral_card : Fintype.card Tetrahedral = 12 := by
  rw [Fintype.card_congr tetrahedralIndex]
  decide

@[simp] theorem tetraRotate_one (u : Fin 3 → ℝ) :
    tetraRotate (1 : Tetrahedral).cycle (1 : Tetrahedral).sign u = u := by
  ext i
  fin_cases i <;> simp [tetraRotate, evenSigns, cyclic]

set_option maxHeartbeats 2000000 in
 theorem tetraRotate_mul (g h : Tetrahedral) (u : Fin 3 → ℝ) :
    tetraRotate (g * h).cycle (g * h).sign u =
      tetraRotate g.cycle g.sign (tetraRotate h.cycle h.sign u) := by
  simp only [tetra_mul_cycle, tetra_mul_sign]
  rcases g with ⟨a, b⟩
  rcases h with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    ext i <;> fin_cases i <;>
    norm_num [signProduct, signShift,
      tetraRotate, evenSigns, cyclic]

/-- Tetrahedral rotations as real linear maps. -/
@[expose] noncomputable def tetraLinear (g : Tetrahedral) : E3 →ₗ[ℝ] E3 where
  toFun u := WithLp.toLp 2 (tetraRotate g.cycle g.sign u)
  map_add' u v := by
    rcases g with ⟨a, b⟩
    ext i
    fin_cases a <;> fin_cases b <;> fin_cases i <;>
      simp [tetraRotate, evenSigns, cyclic, PiLp.add_apply, add_comm]
  map_smul' r u := by
    rcases g with ⟨a, b⟩
    ext i
    fin_cases a <;> fin_cases b <;> fin_cases i <;>
      simp [tetraRotate, evenSigns, cyclic, PiLp.smul_apply]

@[simp] theorem tetraLinear_apply (g : Tetrahedral) (u : E3) (i : Fin 3) :
    tetraLinear g u i = tetraRotate g.cycle g.sign u i := rfl

@[simp] theorem tetraLinear_one (u : E3) : tetraLinear 1 u = u := by
  ext i
  exact congrFun (tetraRotate_one u) i

theorem tetraLinear_mul (g h : Tetrahedral) (u : E3) :
    tetraLinear (g * h) u = tetraLinear g (tetraLinear h u) := by
  ext i
  exact congrFun (tetraRotate_mul g h u) i

theorem tetraLinear_norm (g : Tetrahedral) (u : E3) :
    ‖tetraLinear g u‖ = ‖u‖ := by
  have hs : ‖tetraLinear g u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    exact tetraRotate_squares g.cycle g.sign u
  nlinarith [norm_nonneg (tetraLinear g u), norm_nonneg u]

/-- Every group element has determinant one. -/
theorem tetraLinear_det (g : Tetrahedral) : LinearMap.det (tetraLinear g) = 1 := by
  rw [← LinearMap.det_toMatrix (PiLp.basisFun 2 ℝ (Fin 3)), Matrix.det_fin_three]
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.det_fin_three, LinearMap.toMatrix_apply, PiLp.basisFun_repr,
      PiLp.basisFun_apply, tetraLinear_apply, tetraRotate, evenSigns, cyclic,
      PiLp.single_apply]

/-- Each element is an actual orthogonal linear equivalence of three-space. -/
@[expose] noncomputable def tetraLinearIsometry (g : Tetrahedral) : E3 ≃ₗᵢ[ℝ] E3 where
  toLinearEquiv := {
    tetraLinear g with
    invFun := tetraLinear g⁻¹
    left_inv := fun u => by
      change tetraLinear g⁻¹ (tetraLinear g u) = u
      rw [← tetraLinear_mul, inv_mul_cancel, tetraLinear_one]
    right_inv := fun u => by
      change tetraLinear g (tetraLinear g⁻¹ u) = u
      rw [← tetraLinear_mul, mul_inv_cancel, tetraLinear_one] }
  norm_map' := tetraLinear_norm g

/-- A continuous action of the finite tetrahedral group on the spin sphere. -/
@[expose] noncomputable def tetraAction : FiniteAction Tetrahedral Spin where
  move g := ⟨Rotation.spinRotation (tetraLinearIsometry g),
    (Rotation.spinRotation (tetraLinearIsometry g)).continuous⟩
  one_apply s := Subtype.ext (tetraLinear_one s.val)
  mul_apply g h s := Subtype.ext (tetraLinear_mul g h s.val)

@[simp] theorem tetraAction_val (g : Tetrahedral) (s : Spin) :
    (tetraAction.move g s).val = tetraLinear g s.val := rfl

/-- The finite-group average annihilates the quadrupolar observable. -/
theorem tetraAction_sum_qPair_zero (s t : Spin) :
    ∑ g : Tetrahedral, qPair (tetraAction.move g s) t = 0 := by
  have h := tetrahedral_cancellation s.val t.val (spin_squares s) (spin_squares t)
  rw [← Fintype.sum_prod_type'] at h
  rw [← Equiv.sum_comp tetrahedralIndex] at h
  simpa only [qPair, tetraAction_val, PiLp.inner_apply, Real.inner_apply,
    tetraLinear_apply, tetrahedralIndex_apply] using h

/-- Surface area is invariant under every tetrahedral rotation. -/
theorem tetraAction_measurePreserving (g : Tetrahedral) :
    MeasurePreserving (tetraAction.move g) sphereProbability sphereProbability :=
  Rotation.spinRotation_preserves_probability (tetraLinearIsometry g)

@[simp] theorem tetraAction_eq_spinRotation (g : Tetrahedral) (s : Spin) :
    tetraAction.move g s = Rotation.spinRotation (tetraLinearIsometry g) s := rfl

/-- On a separating cut the quadrupolar observable has exactly zero average. -/
theorem tetraAction_cut_average_zero {V : Type*} [Fintype V] [DecidableEq V]
    (cut : Finset V) (x y : V) (hx : x ∈ cut) (hy : y ∉ cut) :
    (tetraAction.onCut cut).average (observable x y) = 0 := by
  ext σ
  simp only [FiniteAction.average_apply, observable, ContinuousMap.coe_mk,
    FiniteAction.onCut_apply, hx, hy, ite_true, ite_false, ContinuousMap.zero_apply]
  rw [tetraAction_sum_qPair_zero, mul_zero]

/-- Concrete averaging system for any nested chain of spatial cuts. -/
@[expose] noncomputable def tetraNestedSystem {V ι : Type*} [Fintype V] [DecidableEq V]
    (cuts : ι → Finset V) (hchain : ∀ i j, cuts i ⊆ cuts j ∨ cuts j ⊆ cuts i) :
    AveragingSystem (integralOnCompact (referenceLaw (V := V))) ι :=
  tetraAction.nestedSystem sphereProbability tetraAction_measurePreserving cuts hchain

end RP2
