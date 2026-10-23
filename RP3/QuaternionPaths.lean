import RP3.QuaternionAction

/-! Quaternion half-generators satisfy [a,b]=c and have period 4π on S³. -/
namespace RP3.Rotation
noncomputable section
open scoped Real

theorem axis_smul_mul (r : ℝ) (A B : SpinOperator 4) :
    (r • A) * B = r • (A * B) := Algebra.smul_mul_assoc r A B
theorem axis_mul_smul (r : ℝ) (A B : SpinOperator 4) :
    A * (r • B) = r • (A * B) := Algebra.mul_smul_comm r A B

def axisPolynomialFor (X : SpinOperator 4) (t : ℝ) : SpinOperator 4 :=
  (Real.cos (t/2)) • 1 + (2*Real.sin (t/2)) • X

theorem axisPolynomialFor_derivative (X : SpinOperator 4)
    (hX : X^2 = (-1/4 : ℝ) • 1) (t : ℝ) :
    HasDerivAt (axisPolynomialFor X) (axisPolynomialFor X t * X) t := by
  have hc := (Real.hasDerivAt_cos (t/2)).comp t ((hasDerivAt_id t).div_const 2)
  have hs := (Real.hasDerivAt_sin (t/2)).comp t ((hasDerivAt_id t).div_const 2)
  apply ((hc.smul_const (1 : SpinOperator 4)).add ((hs.const_mul 2).smul_const X)).congr_deriv
  simp only [axisPolynomialFor, add_mul, axis_smul_mul, one_mul, ← pow_two, hX, smul_smul]
  module

theorem axisPolynomialFor_commute (X : SpinOperator 4) (t : ℝ) :
    Commute (axisPolynomialFor X t) X := by
  change axisPolynomialFor X t * X = X * axisPolynomialFor X t
  simp only [axisPolynomialFor, add_mul, mul_add, one_mul, mul_one,
    axis_smul_mul, axis_mul_smul]

theorem exp_eq_axisPolynomialFor (X : SpinOperator 4)
    (hX : X^2 = (-1/4 : ℝ) • 1) (t : ℝ) :
    NormedSpace.exp (t • X) = axisPolynomialFor X t := by
  let f := fun t : ℝ => NormedSpace.exp (t • (-X)) * axisPolynomialFor X t
  have hd (t : ℝ) : HasDerivAt f 0 t := by
    apply ((hasDerivAt_exp_smul_const (-X) t).mul
      (axisPolynomialFor_derivative X hX t)).congr_deriv
    rw [mul_assoc, neg_mul X (axisPolynomialFor X t), ← (axisPolynomialFor_commute X t).eq]
    simp
  have he : f t = f 0 := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) t 0
  have h0 : f 0 = 1 := by simp [f, axisPolynomialFor, zero_smul ℝ X]
  rw [h0] at he
  have hm := congrArg (fun Q : SpinOperator 4 => NormedSpace.exp (t • X) * Q) he
  dsimp only [f] at hm
  rw [← mul_assoc, smul_neg,
    ← NormedSpace.exp_add_of_commute (Commute.refl (t • X)).neg_right,
    add_neg_cancel, NormedSpace.exp_zero, mul_one, one_mul] at hm
  exact hm.symm

theorem axisA_square : axisA^2 = (-1/4 : ℝ) • 1 := by
  have hm : axisMatrixA^2 = (-1/4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [axisMatrixA, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [axisA, ← map_pow, hm, map_smul, map_one]
theorem axisB_square : axisB^2 = (-1/4 : ℝ) • 1 := by
  have hm : axisMatrixB^2 = (-1/4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [axisMatrixB, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [axisB, ← map_pow, hm, map_smul, map_one]
theorem axisC_square : axisC^2 = (-1/4 : ℝ) • 1 := by
  have hm : axisMatrixC^2 = (-1/4 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [axisMatrixC, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]
  rw [axisC, ← map_pow, hm, map_smul, map_one]

theorem exp_axisA (t : ℝ) : NormedSpace.exp (t • axisA) = axisPolynomialFor axisA t :=
  exp_eq_axisPolynomialFor axisA axisA_square t
theorem exp_axisB (t : ℝ) : NormedSpace.exp (t • axisB) = axisPolynomialFor axisB t :=
  exp_eq_axisPolynomialFor axisB axisB_square t
theorem exp_axisC (t : ℝ) : NormedSpace.exp (t • axisC) = axisPolynomialFor axisC t :=
  exp_eq_axisPolynomialFor axisC axisC_square t

theorem exp_axis_periodic (X : SpinOperator 4) (hX : X^2 = (-1/4 : ℝ) • 1) :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • X)) (4 * Real.pi) := by
  intro t
  have ht : (t+4*Real.pi)/2 = t/2+2*Real.pi := by ring
  simp [exp_eq_axisPolynomialFor X hX, axisPolynomialFor, ht,
    Real.sin_add_two_pi, Real.cos_add_two_pi]
theorem exp_axisC_periodic :
    Function.Periodic (fun t : ℝ => NormedSpace.exp (t • axisC)) (4 * Real.pi) :=
  exp_axis_periodic axisC axisC_square

def coordinateAxis (a : Fin 3) : SpinOperator 4 := ![axisA, axisB, axisC] a
theorem coordinateAxis_skew (a : Fin 3) : coordinateAxis a ∈ skewAdjoint (SpinOperator 4) := by
  fin_cases a
  · exact axisA_skew
  · exact axisB_skew
  · exact axisC_skew
theorem coordinateAxis_square (a : Fin 3) : (coordinateAxis a)^2 = (-1/4 : ℝ) • 1 := by
  fin_cases a
  · exact axisA_square
  · exact axisB_square
  · exact axisC_square
theorem coordinateAxis_norm_le (a : Fin 3) : ‖coordinateAxis a‖ ≤ 1 := by
  fin_cases a
  · exact axisA_norm_le
  · exact axisB_norm_le
  · exact axisC_norm_le

def coordinateRotation (a : Fin 3) (t : ℝ) : E4 ≃ₗᵢ[ℝ] E4 :=
  rotationExp (t • coordinateAxis a) (skewAdjoint.smul_mem t (coordinateAxis_skew a))
@[simp] theorem coordinateRotation_apply (a : Fin 3) (t : ℝ) (u : E4) :
    coordinateRotation a t u = NormedSpace.exp (t • coordinateAxis a) u := rfl
@[simp] theorem coordinateRotation_zero (a : Fin 3) (u : E4) :
    coordinateRotation a 0 u = u := by
  rw [coordinateRotation_apply, zero_smul ℝ (coordinateAxis a), NormedSpace.exp_zero]
  rfl

def conjugatorCoordinates (a : Fin 3) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![![u 0,u 2,u 3,u 1], ![u 0,u 3,u 1,u 2], ![u 0,u 1,u 2,u 3]] a
def conjugatorInverse (a : Fin 3) : Fin 3 := ![1,0,2] a
def conjugatorLinear (a : Fin 3) : E4 →ₗ[ℝ] E4 where
  toFun u := WithLp.toLp 2 (conjugatorCoordinates a u)
  map_add' u v := by ext i; fin_cases a <;> fin_cases i <;> simp [conjugatorCoordinates]
  map_smul' r u := by ext i; fin_cases a <;> fin_cases i <;> simp [conjugatorCoordinates]
def axisConjugator (a : Fin 3) : E4 ≃ₗᵢ[ℝ] E4 where
  toLinearEquiv := {
    conjugatorLinear a with
    invFun := conjugatorLinear (conjugatorInverse a)
    left_inv := by
      intro u
      ext i
      fin_cases a <;> fin_cases i <;> simp [conjugatorLinear, conjugatorCoordinates, conjugatorInverse]
    right_inv := by
      intro u
      ext i
      fin_cases a <;> fin_cases i <;> simp [conjugatorLinear, conjugatorCoordinates, conjugatorInverse] }
  norm_map' := by
    intro u
    change ‖conjugatorLinear a u‖ = ‖u‖
    have hs : ‖conjugatorLinear a u‖^2 = ‖u‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      fin_cases a <;> simp [conjugatorLinear, conjugatorCoordinates, Fin.sum_univ_succ] <;> ring
    nlinarith [norm_nonneg (conjugatorLinear a u), norm_nonneg u]

theorem coordinateRotation_intertwine_axisC (a : Fin 3) (t : ℝ) (u : E4) :
    axisConjugator a (coordinateRotation a t u) =
      coordinateRotation 2 t (axisConjugator a u) := by
  fin_cases a <;> ext i <;> fin_cases i <;>
    simp [axisConjugator, conjugatorLinear, conjugatorCoordinates,
      coordinateRotation_apply, coordinateAxis, exp_axisA, exp_axisB, exp_axisC,
      axisPolynomialFor, axisA_apply, axisB_apply, axisC_apply] <;> ring
theorem spinRotation_intertwine_axisC (a : Fin 3) (t : ℝ) (s : RP3.Spin) :
    spinRotation (axisConjugator a) (spinRotation (coordinateRotation a t) s) =
      spinRotation (coordinateRotation 2 t) (spinRotation (axisConjugator a) s) :=
  Subtype.ext (coordinateRotation_intertwine_axisC a t s.val)

def quaternionPathAxis (g : Quaternion) (_ : Fin 3) : Fin 3 :=
  ![2,0,1,2,2,0,1,2] g.index
def quaternionPathAngle (g : Quaternion) (k : Fin 3) : ℝ :=
  if k = 0 then ![0,Real.pi,Real.pi,Real.pi,2*Real.pi,-Real.pi,-Real.pi,-Real.pi] g.index else 0

set_option maxHeartbeats 800000 in
theorem quaternionLinearIsometry_eq_three_rotations (g : Quaternion) (u : E4) :
    quaternionLinearIsometry g u =
      coordinateRotation (quaternionPathAxis g 0) (quaternionPathAngle g 0)
        (coordinateRotation (quaternionPathAxis g 1) (quaternionPathAngle g 1)
          (coordinateRotation (quaternionPathAxis g 2) (quaternionPathAngle g 2) u)) := by
  have hn : Real.pi*(-1/2) = -(Real.pi/2) := by ring
  have hc : Real.cos (Real.pi*(-1/2)) = 0 := by rw [hn, Real.cos_neg, Real.cos_pi_div_two]
  have hs : Real.sin (Real.pi*(-1/2)) = -1 := by rw [hn, Real.sin_neg, Real.sin_pi_div_two]
  rcases g with ⟨g⟩
  fin_cases g <;> ext i <;> fin_cases i <;>
    norm_num [quaternionLinearIsometry, quaternionLinear, quaternionRotate,
      quaternionPathAxis, quaternionPathAngle, coordinateRotation_apply, coordinateAxis,
      exp_axisA, exp_axisB, exp_axisC, axisPolynomialFor,
      axisA_apply, axisB_apply, axisC_apply, hc, hs, neg_div] <;> ring

end
end RP3.Rotation
