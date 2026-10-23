module

public import RP3.QuaternionAlgebra

public section

namespace RP3.Rotation
universe uR uS
noncomputable section
open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 400000 in
lemma moment4_plane_even (f g h k : ℝ) :
    moment4Plane f g h k + moment4Plane f (-g) h (-k) =
      (6 * (f*k-g*h)^2) • third^2 := by
  unfold moment4Plane
  rw [plane_sub, plane_neg, plane_sub, plane_neg]
  simp only [tripleMoment_four]
  simp only [plane_eq_qMatrix, third, axisMatrixC_eq_qMatrix,
    pow_succ, pow_zero, one_mul, mul_one]
  simp only [qMatrix_mul, qMatrix_add, qMatrix_nsmul, qMatrix_smul]
  congr 1 <;> ring


theorem tripleJet_at_zero {n : ℕ} (X Y Z : SpinOperator n) (k a b c : ℕ) :
    tripleJet X Y Z k a b c 0 = tripleMoment X Y Z k a b c := by
  induction k generalizing a b c with
  | zero =>
      simp only [tripleJet, expPower, tripleMoment,
        zero_smul ℝ X, zero_smul ℝ Y, zero_smul ℝ Z, NormedSpace.exp_zero, one_mul]
  | succ k ih => simp only [tripleJet, tripleMoment, ih]

theorem map_tripleMoment {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (φ : R →+* S) (X Y Z : R) (k a b c : ℕ) :
    φ (tripleMoment X Y Z k a b c) =
      tripleMoment (φ X) (φ Y) (φ Z) k a b c := by
  induction k generalizing a b c with
  | zero => simp [tripleMoment]
  | succ k ih => simp [tripleMoment, ih]

@[expose] def planeOperator (f g : ℝ) : SpinOperator 4 := matrixOperator (plane f g)

theorem planeOperator_eq (f g : ℝ) : planeOperator f g = f • axisA + g • axisB := by
  rw [planeOperator, axisA, axisB, ← map_smul, ← map_smul, ← map_add]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane, axisMatrixA, axisMatrixB] <;> ring

theorem plane_commutator (f g h k : ℝ) :
    plane f g * plane h k - plane h k * plane f g = (f*k-g*h) • third := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [plane, third, Matrix.cons_val_two, axisMatrixA, axisMatrixB, axisMatrixC] <;> ring

theorem planeOperator_commutator (f g h k : ℝ) :
    planeOperator f g * planeOperator h k - planeOperator h k * planeOperator f g =
      (f*k-g*h) • axisC := by
  rw [planeOperator, planeOperator, ← map_mul, ← map_mul, ← map_sub, plane_commutator,
    map_smul]
  rfl

theorem gaugeJet_plane_four_even (f g h k : ℝ) :
    tripleJet (planeOperator f g) (planeOperator h k-planeOperator f g)
      (-planeOperator h k) 4 0 0 0 0 +
    tripleJet (planeOperator f (-g)) (planeOperator h (-k)-planeOperator f (-g))
      (-planeOperator h (-k)) 4 0 0 0 0 = (6*(f*k-g*h)^2) • axisC^2 := by
  simp only [tripleJet_at_zero, planeOperator]
  have hm (f g h k : ℝ) := map_tripleMoment matrixOperator.toRingHom
    (plane f g) (plane h k-plane f g) (-plane h k) 4 0 0 0
  change ∀ f g h k, matrixOperator (tripleMoment (plane f g)
    (plane h k-plane f g) (-plane h k) 4 0 0 0) =
      tripleMoment (matrixOperator (plane f g)) (matrixOperator (plane h k-plane f g))
        (matrixOperator (-plane h k)) 4 0 0 0 at hm
  simp only [map_sub, map_neg] at hm
  rw [← hm, ← hm, ← map_add]
  change matrixOperator (moment4Plane f g h k + moment4Plane f (-g) h (-k)) = _
  rw [moment4_plane_even, map_smul, map_pow]
  rfl

@[expose] def mixedMatrixAB : Matrix (Fin 4) (Fin 4) ℝ := 0
@[expose] def mixedMatrixAAB : Matrix (Fin 4) (Fin 4) ℝ := (-1/12 : ℝ) • axisMatrixB
@[expose] def mixedMatrixABB : Matrix (Fin 4) (Fin 4) ℝ := (-1/12 : ℝ) • axisMatrixA
@[expose] def mixedMatrixAABB : Matrix (Fin 4) (Fin 4) ℝ := (-1/24 : ℝ) • (axisMatrixA^2+axisMatrixB^2)

theorem plane_matrix_square (f g : ℝ) :
    plane f g ^ 2 = f^2 • axisMatrixA^2 + (2*f*g) • mixedMatrixAB + g^2 • axisMatrixB^2 := by
  simp only [plane_eq_qMatrix, mixedMatrixAB, mixedMatrixAAB, mixedMatrixABB,
    mixedMatrixAABB, axisMatrixA_eq_qMatrix, axisMatrixB_eq_qMatrix,
    pow_succ, pow_zero, one_mul, mul_one, smul_zero, add_zero]
  simp only [qMatrix_mul, qMatrix_add, qMatrix_smul]
  congr 1 <;> ring


theorem plane_matrix_cube (f g : ℝ) :
    plane f g ^ 3 = f^3 • axisMatrixA^3 + (3*f^2*g) • mixedMatrixAAB + (3*f*g^2) • mixedMatrixABB + g^3 • axisMatrixB^3 := by
  simp only [plane_eq_qMatrix, mixedMatrixAB, mixedMatrixAAB, mixedMatrixABB,
    mixedMatrixAABB, axisMatrixA_eq_qMatrix, axisMatrixB_eq_qMatrix,
    pow_succ, pow_zero, one_mul, mul_one, smul_zero, add_zero]
  simp only [qMatrix_mul, qMatrix_add, qMatrix_smul]
  congr 1 <;> ring


theorem plane_matrix_four_even (f g : ℝ) :
    plane f g ^ 4 + plane f (-g) ^ 4 = (2*f^4) • axisMatrixA^4 +
      (12*f^2*g^2) • mixedMatrixAABB + (2*g^4) • axisMatrixB^4 := by
  simp only [plane_eq_qMatrix, mixedMatrixAB, mixedMatrixAAB, mixedMatrixABB,
    mixedMatrixAABB, axisMatrixA_eq_qMatrix, axisMatrixB_eq_qMatrix,
    pow_succ, pow_zero, one_mul, mul_one, smul_zero, add_zero]
  simp only [qMatrix_mul, qMatrix_add, qMatrix_smul]
  congr 1 <;> ring


theorem mixedMatrixAB_sym : mixedMatrixAB = (1/2 : ℝ) • (axisMatrixA*axisMatrixB+axisMatrixB*axisMatrixA) := by
  simp only [plane_eq_qMatrix, mixedMatrixAB, mixedMatrixAAB, mixedMatrixABB,
    mixedMatrixAABB, axisMatrixA_eq_qMatrix, axisMatrixB_eq_qMatrix,
    pow_succ, pow_zero, one_mul, mul_one, smul_zero, add_zero]
  simp only [qMatrix_mul, qMatrix_add, qMatrix_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [qMatrix]


@[expose] def mixedAB : SpinOperator 4 := matrixOperator mixedMatrixAB
@[expose] def mixedAAB : SpinOperator 4 := matrixOperator mixedMatrixAAB
@[expose] def mixedABB : SpinOperator 4 := matrixOperator mixedMatrixABB
@[expose] def mixedAABB : SpinOperator 4 := matrixOperator mixedMatrixAABB

theorem planeOperator_square (f g : ℝ) :
    planeOperator f g ^ 2 = f^2 • axisA^2 + (2*f*g) • mixedAB + g^2 • axisB^2 := by
  have h := congrArg matrixOperator (plane_matrix_square f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

theorem planeOperator_cube (f g : ℝ) :
    planeOperator f g ^ 3 = f^3 • axisA^3 + (3*f^2*g) • mixedAAB +
      (3*f*g^2) • mixedABB + g^3 • axisB^3 := by
  have h := congrArg matrixOperator (plane_matrix_cube f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

theorem planeOperator_four_even (f g : ℝ) :
    planeOperator f g ^ 4 + planeOperator f (-g) ^ 4 = (2*f^4) • axisA^4 +
      (12*f^2*g^2) • mixedAABB + (2*g^4) • axisB^4 := by
  have h := congrArg matrixOperator (plane_matrix_four_even f g)
  simpa only [map_add, map_smul, map_pow, planeOperator, axisA, axisB, mixedAB, mixedAAB, mixedABB, mixedAABB] using h

end
end RP3.Rotation
