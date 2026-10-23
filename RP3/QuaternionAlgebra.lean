module

public import RP3.RotationGeometryBase

public section

/-! Closed multiplication of left-quaternion matrices keeps the fourth-order
calculation small. Every identity below is checked by scalar ring arithmetic. -/
namespace RP3.Rotation
noncomputable section

@[expose] def qMatrix (r a b c : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![r,-a,-b,-c; a,r,-c,b; b,c,r,-a; c,-b,a,r]

theorem qMatrix_mul (r a b c s d e f : ℝ) :
    qMatrix r a b c * qMatrix s d e f =
      qMatrix (r*s-a*d-b*e-c*f) (r*d+a*s+b*f-c*e)
        (r*e-a*f+b*s+c*d) (r*f+a*e-b*d+c*s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [qMatrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem qMatrix_add (r a b c s d e f : ℝ) :
    qMatrix r a b c + qMatrix s d e f = qMatrix (r+s) (a+d) (b+e) (c+f) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMatrix] <;> ring

theorem qMatrix_smul (t r a b c : ℝ) :
    t • qMatrix r a b c = qMatrix (t*r) (t*a) (t*b) (t*c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMatrix] <;> ring

theorem qMatrix_nsmul (n : ℕ) (r a b c : ℝ) :
    n • qMatrix r a b c = qMatrix (n*r) (n*a) (n*b) (n*c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qMatrix, nsmul_eq_mul] <;> ring

theorem plane_eq_qMatrix (f g : ℝ) : plane f g = qMatrix 0 (f/2) (g/2) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, qMatrix] <;> ring
theorem axisMatrixA_eq_qMatrix : axisMatrixA = qMatrix 0 (1/2) 0 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA, qMatrix]
theorem axisMatrixB_eq_qMatrix : axisMatrixB = qMatrix 0 0 (1/2) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixB, qMatrix]
theorem axisMatrixC_eq_qMatrix : axisMatrixC = qMatrix 0 0 0 (1/2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixC, qMatrix]

end
end RP3.Rotation
