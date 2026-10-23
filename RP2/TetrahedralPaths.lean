import RP2.TetrahedralAction

/-!
# Periodic coordinate rotations and finite paths to tetrahedral elements

The exponential-polynomial argument is adapted from OpenAI's
ClassicalON/AxisRotation.lean (Apache-2.0), generalized to all coordinate axes.
Every tetrahedral element is expressed as at most three coordinate rotations.
-/
namespace RP2.Rotation

noncomputable section
open scoped Real

theorem axis_smul_mul (r : ℝ) (A B : SpinOperator 3) :
    (r • A) * B = r • (A * B) := Algebra.smul_mul_assoc r A B

theorem axis_mul_smul (r : ℝ) (A B : SpinOperator 3) :
    A * (r • B) = r • (A * B) := Algebra.mul_smul_comm r A B

def axisPolynomialFor (X : SpinOperator 3) (t : ℝ) : SpinOperator 3 :=
  1 + (Real.sin t) • X + (1 - Real.cos t) • X^2

theorem axisPolynomialFor_derivative (X : SpinOperator 3) (hX : X^3 = -X) (t : ℝ) :
    HasDerivAt (axisPolynomialFor X) (axisPolynomialFor X t * X) t := by
  have h := ((hasDerivAt_const t (1 : SpinOperator 3)).add
    ((Real.hasDerivAt_sin t).smul_const X)).add
    (((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).smul_const (X^2))
  apply h.congr_deriv
  change 0 + (Real.cos t) • X + (0 - -Real.sin t) • X^2 = axisPolynomialFor X t * X
  have hs : X^2 * X = -X := by rw [← pow_succ, hX]
  simp only [axisPolynomialFor, add_mul, one_mul, axis_smul_mul, hs, ← pow_two]
  module

theorem axisPolynomialFor_commute (X : SpinOperator 3) (t : ℝ) :
    Commute (axisPolynomialFor X t) X := by
  change axisPolynomialFor X t * X = X * axisPolynomialFor X t
  simp only [axisPolynomialFor, add_mul, mul_add, one_mul, mul_one,
    axis_smul_mul, axis_mul_smul, ← pow_succ, ← pow_succ']

theorem exp_eq_axisPolynomialFor (X : SpinOperator 3) (hX : X^3 = -X) (t : ℝ) :
    NormedSpace.exp (t • X) = axisPolynomialFor X t := by
  let f := fun t : ℝ => NormedSpace.exp (t • (-X)) * axisPolynomialFor X t
  have hd (t : ℝ) : HasDerivAt f 0 t := by
    apply ((hasDerivAt_exp_smul_const (-X) t).mul
      (axisPolynomialFor_derivative X hX t)).congr_deriv
    rw [mul_assoc, neg_mul X (axisPolynomialFor X t), ← (axisPolynomialFor_commute X t).eq]
    simp
  have he : f t = f 0 := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  have h0 : f 0 = 1 := by
    simp [f, axisPolynomialFor, zero_smul ℝ X, zero_smul ℝ (X^2)]
  rw [h0] at he
  have hm := congrArg (fun Q : SpinOperator 3 => NormedSpace.exp (t • X) * Q) he
  dsimp only [f] at hm
  rw [← mul_assoc, smul_neg,
    ← NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_right,
    add_neg_cancel, NormedSpace.exp_zero, mul_one, one_mul] at hm
  exact hm.symm

theorem axisA_cube : axisA^3 = -axisA := by
  rw [axisA, ← map_pow, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisMatrixA, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem axisB_cube : axisB^3 = -axisB := by
  rw [axisB, ← map_pow, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisMatrixB, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem axisC_cube : axisC^3 = -axisC := by
  rw [axisC, ← map_pow, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [axisMatrixC, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem exp_axisA (t : ℝ) : NormedSpace.exp (t • axisA) = axisPolynomialFor axisA t :=
  exp_eq_axisPolynomialFor axisA axisA_cube t

theorem exp_axisB (t : ℝ) : NormedSpace.exp (t • axisB) = axisPolynomialFor axisB t :=
  exp_eq_axisPolynomialFor axisB axisB_cube t

theorem exp_axisC (t : ℝ) : NormedSpace.exp (t • axisC) = axisPolynomialFor axisC t :=
  exp_eq_axisPolynomialFor axisC axisC_cube t

/-- Each coordinate generator produces a two-pi periodic one-parameter subgroup. -/
theorem exp_axis_periodic (X : SpinOperator 3) (hX : X^3 = -X) :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • X)) (2 * Real.pi) := by
  intro t
  simp [exp_eq_axisPolynomialFor X hX, axisPolynomialFor,
    Real.sin_add_two_pi, Real.cos_add_two_pi]

theorem exp_axisA_periodic :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • axisA)) (2 * Real.pi) :=
  exp_axis_periodic axisA axisA_cube

theorem exp_axisB_periodic :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • axisB)) (2 * Real.pi) :=
  exp_axis_periodic axisB axisB_cube

theorem exp_axisC_periodic :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • axisC)) (2 * Real.pi) :=
  exp_axis_periodic axisC axisC_cube

/-- Coordinate generator 0, 1, or 2. -/
def coordinateAxis (a : Fin 3) : SpinOperator 3 := ![axisA, axisB, axisC] a

theorem coordinateAxis_skew (a : Fin 3) : coordinateAxis a ∈ skewAdjoint (SpinOperator 3) := by
  fin_cases a
  · exact axisA_skew
  · exact axisB_skew
  · exact axisC_skew

theorem coordinateAxis_cube (a : Fin 3) : (coordinateAxis a)^3 = -(coordinateAxis a) := by
  fin_cases a
  · exact axisA_cube
  · exact axisB_cube
  · exact axisC_cube

theorem coordinateAxis_norm_le (a : Fin 3) : ‖coordinateAxis a‖ ≤ 1 := by
  fin_cases a
  · exact axisA_norm_le
  · exact axisB_norm_le
  · exact axisC_norm_le

def coordinateRotation (a : Fin 3) (t : ℝ) : E3 ≃ₗᵢ[ℝ] E3 :=
  rotationExp (t • coordinateAxis a)
    (skewAdjoint.smul_mem t (coordinateAxis_skew a))

@[simp] theorem coordinateRotation_apply (a : Fin 3) (t : ℝ) (u : E3) :
    coordinateRotation a t u = NormedSpace.exp (t • coordinateAxis a) u := rfl

theorem coordinateRotation_periodic (a : Fin 3) :
    Function.Periodic (coordinateRotation a) (2 * Real.pi) := by
  intro t
  apply LinearIsometryEquiv.ext
  intro u
  exact congrArg (fun X : SpinOperator 3 => X u)
    (exp_axis_periodic (coordinateAxis a) (coordinateAxis_cube a) t)

@[simp] theorem coordinateRotation_zero (a : Fin 3) (u : E3) :
    coordinateRotation a 0 u = u := by
  rw [coordinateRotation_apply, zero_smul ℝ (coordinateAxis a), NormedSpace.exp_zero]
  rfl

/-- A cyclic relabelling carrying the chosen coordinate axis to the third axis. -/
def axisConjugator (a : Fin 3) : Tetrahedral := ⟨![1, 2, 0] a, 0⟩

/-- Conjugation by a global cyclic rotation reduces any coordinate-axis
rotation to the axis-C rotation used in the analytic estimates. -/
theorem coordinateRotation_intertwine_axisC (a : Fin 3) (t : ℝ) (u : E3) :
    tetraLinearIsometry (axisConjugator a) (coordinateRotation a t u) =
      coordinateRotation 2 t (tetraLinearIsometry (axisConjugator a) u) := by
  fin_cases a <;> ext i <;> fin_cases i <;>
    simp [tetraLinearIsometry, tetraLinear, tetraRotate, evenSigns, cyclic,
      axisConjugator, coordinateRotation_apply, coordinateAxis,
      exp_axisA, exp_axisB, exp_axisC, axisPolynomialFor,
      axisA_apply, axisB_apply, axisC_apply, pow_two] <;> ring

theorem spinRotation_intertwine_axisC (a : Fin 3) (t : ℝ) (s : RP2.Spin) :
    tetraAction.move (axisConjugator a) (spinRotation (coordinateRotation a t) s) =
      spinRotation (coordinateRotation 2 t) (tetraAction.move (axisConjugator a) s) :=
  Subtype.ext (coordinateRotation_intertwine_axisC a t s.val)

def tetraPathAxis (g : Tetrahedral) (k : Fin 3) : Fin 3 :=
  ![![0, 0, 1, 2] g.sign,
    ![0, 1, 0] g.cycle,
    ![0, 0, 1] g.cycle] k

def tetraPathAngle (g : Tetrahedral) (k : Fin 3) : ℝ :=
  ![if g.sign = 0 then 0 else Real.pi,
    ![0, -(Real.pi / 2), Real.pi / 2] g.cycle,
    ![0, -(Real.pi / 2), Real.pi / 2] g.cycle] k

theorem tetraPathAngle_abs_le_pi (g : Tetrahedral) (k : Fin 3) :
    |tetraPathAngle g k| ≤ Real.pi := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> fin_cases k <;>
    norm_num [tetraPathAngle, abs_div, abs_of_pos Real.pi_pos] <;>
    linarith [Real.pi_pos]

set_option maxHeartbeats 400000 in
/-- Exact decomposition into three periodic coordinate rotations; identity factors
are allowed, so the same expression covers all twelve group elements. -/
theorem tetraLinearIsometry_eq_three_rotations (g : Tetrahedral) (u : E3) :
    tetraLinearIsometry g u =
      coordinateRotation (tetraPathAxis g 0) (tetraPathAngle g 0)
        (coordinateRotation (tetraPathAxis g 1) (tetraPathAngle g 1)
          (coordinateRotation (tetraPathAxis g 2) (tetraPathAngle g 2) u)) := by
  rcases g with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    ext i <;> fin_cases i <;>
    norm_num [tetraLinearIsometry, tetraLinear, tetraRotate, evenSigns, cyclic,
      tetraPathAxis, tetraPathAngle, coordinateRotation_apply, coordinateAxis,
      exp_axisA, exp_axisB, exp_axisC, axisPolynomialFor,
      axisA_apply, axisB_apply, axisC_apply, pow_two] <;> ring

end
end RP2.Rotation
