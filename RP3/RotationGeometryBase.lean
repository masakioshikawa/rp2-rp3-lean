module

public import RP3.Model

public section

/-!
Adapted from OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, licensed under Apache-2.0.
Copyright OpenAI. The namespace and imports have been changed and the
interaction-independent lemmas separated from the O(n) Gibbs model.
-/

namespace RP3.Rotation

universe uR uS uΩ uF
noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

abbrev Spin (n : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1

@[expose] def spinRotation {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Spin n ≃ₜ Spin n :=
  R.toHomeomorph.subtype fun x => by
    simp only [mem_sphere_zero_iff_norm]
    change ‖x‖ = 1 ↔ ‖R x‖ = 1
    rw [R.norm_map]

@[simp] theorem spinRotation_val {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) (s : Spin n) :
    (spinRotation R s).val = R s.val := rfl

theorem spinRotation_preserves_surface {n : ℕ}
    (R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    MeasurePreserving (spinRotation R)
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
      (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere := by
  open scoped Pointwise in
  refine ⟨(spinRotation R).measurable, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (spinRotation R).measurable hs,
    Measure.toSphere_apply' _ ((spinRotation R).measurable hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have hcone : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ((spinRotation R) ⁻¹' s)) =
      R ⁻¹' (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)) := by
    ext v
    constructor
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, rfl⟩
      exact ⟨r, hr, R t.val, ⟨spinRotation R t, ht, rfl⟩, (R.map_smul r t.val).symm⟩
    · rintro ⟨r, hr, w, ⟨t, ht, rfl⟩, hv⟩
      refine ⟨r, hr, R.symm t.val, ⟨(spinRotation R).symm t, ?_, rfl⟩, ?_⟩
      · simpa only [Set.mem_preimage, Homeomorph.apply_symm_apply] using ht
      · apply R.injective
        simpa only [map_smul, LinearIsometryEquiv.apply_symm_apply] using hv
  rw [hcone]
  have hm := R.toHomeomorph.measurableEmbedding.map_apply
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s))
  change (Measure.map R volume) _ = volume (R ⁻¹' _) at hm
  rw [R.measurePreserving.map_eq] at hm
  exact hm.symm

theorem spinRotation_preserves_probability
    (R : E4 ≃ₗᵢ[ℝ] E4) :
    MeasurePreserving (spinRotation R) sphereProbability sphereProbability :=
  (spinRotation_preserves_surface R).smul_measure _

abbrev SpinOperator (n : ℕ) :=
  EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)

@[expose] instance spinOperator_completeSpace (dimension : ℕ) : CompleteSpace (SpinOperator dimension) :=
  ContinuousLinearMap.instCompleteSpace

@[expose] instance spinOperator_ratNormedAlgebra (n : ℕ) : NormedAlgebra ℚ (SpinOperator n) :=
  NormedAlgebra.restrictScalars ℚ ℝ _

@[expose] def rotationExp {n : ℕ} (A : SpinOperator n) (hA : A ∈ skewAdjoint (SpinOperator n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Unitary.linearIsometryEquiv
    ⟨NormedSpace.exp A, NormedSpace.exp_mem_unitary_of_mem_skewAdjoint hA⟩

@[simp] theorem rotationExp_apply {n : ℕ} (A : SpinOperator n)
    (hA : A ∈ skewAdjoint (SpinOperator n)) (v : EuclideanSpace ℝ (Fin n)) :
    rotationExp A hA v = NormedSpace.exp A v := rfl

@[simp] theorem rotationExp_symm_apply {n : ℕ} (A : SpinOperator n)
    (hA : A ∈ skewAdjoint (SpinOperator n)) (v : EuclideanSpace ℝ (Fin n)) :
    (rotationExp A hA).symm v = NormedSpace.exp (-A) v := by
  change (star (NormedSpace.exp A)) v = _
  rw [NormedSpace.star_exp, skewAdjoint.mem_iff.mp hA]

@[expose] def expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) (t : ℝ) : SpinOperator n :=
  NormedSpace.exp (t • X) * X^a

theorem hasDerivAt_expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) (t : ℝ) :
    HasDerivAt (expPower X a) (expPower X (a+1) t) t := by
  exact ((hasDerivAt_exp_smul_const X t).mul_const (X^a)).congr_deriv
    (by simp only [expPower, pow_succ', mul_assoc])

theorem continuous_expPower {n : ℕ} (X : SpinOperator n) (a : ℕ) :
    Continuous (expPower X a) := by
  unfold expPower
  fun_prop

@[expose] def tripleJet {n : ℕ} (X Y Z : SpinOperator n) : ℕ → ℕ → ℕ → ℕ → ℝ → SpinOperator n
  | 0, a, b, c, t => expPower X a t * expPower Y b t * expPower Z c t
  | k+1, a, b, c, t => tripleJet X Y Z k (a+1) b c t +
      tripleJet X Y Z k a (b+1) c t + tripleJet X Y Z k a b (c+1) t

theorem continuous_tripleJet {n : ℕ} (X Y Z : SpinOperator n)
    (k a b c : ℕ) : Continuous (tripleJet X Y Z k a b c) := by
  induction k generalizing a b c with
  | zero => exact ((continuous_expPower X a).mul (continuous_expPower Y b)).mul (continuous_expPower Z c)
  | succ k ih => exact ((ih (a+1) b c).add (ih a (b+1) c)).add (ih a b (c+1))

theorem hasDerivAt_tripleJet {n : ℕ} (X Y Z : SpinOperator n)
    (k a b c : ℕ) (t : ℝ) :
    HasDerivAt (tripleJet X Y Z k a b c) (tripleJet X Y Z (k+1) a b c t) t := by
  induction k generalizing a b c with
  | zero =>
    exact (((hasDerivAt_expPower X a t).mul (hasDerivAt_expPower Y b t)).mul
      (hasDerivAt_expPower Z c t)).congr_deriv (by dsimp [tripleJet]; rw [add_mul, add_assoc])
  | succ k ih => exact ((ih (a+1) b c).add (ih a (b+1) c)).add (ih a b (c+1))

@[simp] theorem expPower_zero {n : ℕ} (X : SpinOperator n) (a : ℕ) :
    expPower X a 0 = X^a := by
  rw [expPower, zero_smul ℝ X, NormedSpace.exp_zero, one_mul]

theorem gaugeJets_zero_one {n : ℕ} (X Y : SpinOperator n) :
    tripleJet X (Y-X) (-Y) 0 0 0 0 0 = 1 ∧
    tripleJet X (Y-X) (-Y) 1 0 0 0 0 = 0 := by
  simp [tripleJet]

theorem gaugeJet_two {n : ℕ} (X Y : SpinOperator n) :
    tripleJet X (Y-X) (-Y) 2 0 0 0 0 = X*Y-Y*X := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [tripleJet, expPower_zero, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one, pow_two,
    add_apply, sub_apply, neg_apply, mul_apply_eq_comp, map_sub, map_neg]
  abel

open scoped Matrix

@[expose] def matrixOperator {n : ℕ} : Matrix (Fin n) (Fin n) ℝ ≃ₐ[ℝ] SpinOperator n :=
  (Matrix.toLinAlgEquiv (PiLp.basisFun 2 ℝ (Fin n))).trans
    (Module.End.toContinuousLinearMap (EuclideanSpace ℝ (Fin n)))
theorem matrixOperator_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (v : EuclideanSpace ℝ (Fin n)) :
    matrixOperator M v = WithLp.toLp 2 (M *ᵥ v.ofLp) := by
  change (Matrix.toLin (PiLp.basisFun 2 ℝ (Fin n)) (PiLp.basisFun 2 ℝ (Fin n)) M) v = _
  rw [← Matrix.toLpLin_eq_toLin, Matrix.toLpLin_apply]

@[expose] def axisMatrixA : Matrix (Fin 4) (Fin 4) ℝ := !![0,-1/2,0,0; 1/2,0,0,0; 0,0,0,-1/2; 0,0,1/2,0]
@[expose] def axisMatrixB : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,-1/2,0; 0,0,0,1/2; 1/2,0,0,0; 0,-1/2,0,0]
@[expose] def axisMatrixC : Matrix (Fin 4) (Fin 4) ℝ := !![0,0,0,-1/2; 0,0,-1/2,0; 0,1/2,0,0; 1/2,0,0,0]
@[expose] def axisA : SpinOperator 4 := matrixOperator axisMatrixA
@[expose] def axisB : SpinOperator 4 := matrixOperator axisMatrixB
@[expose] def axisC : SpinOperator 4 := matrixOperator axisMatrixC

theorem axisA_apply (v : EuclideanSpace ℝ (Fin 4)) :
    axisA v = WithLp.toLp 2 ![-v 1/2, v 0/2, -v 3/2, v 2/2] := by
  rw [axisA, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring


theorem matrixOperator_star {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    star (matrixOperator M) = matrixOperator M.transpose := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    matrixOperator_apply, matrixOperator_apply]
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

theorem axisA_skew : axisA ∈ skewAdjoint (SpinOperator 4) := by
  rw [skewAdjoint.mem_iff, axisA, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixA]

theorem axisA_norm_le : ‖axisA‖ ≤ 1 := by
  apply axisA.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  have hs : ‖axisA v‖^2 = ‖v‖^2/4 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, axisA_apply]
    simp [Fin.sum_univ_succ]
    ring
  nlinarith [norm_nonneg (axisA v), norm_nonneg v, sq_nonneg ‖v‖]


theorem axisB_skew : axisB ∈ skewAdjoint (SpinOperator 4) := by
  rw [skewAdjoint.mem_iff, axisB, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixB]

theorem axisC_skew : axisC ∈ skewAdjoint (SpinOperator 4) := by
  rw [skewAdjoint.mem_iff, axisC, matrixOperator_star, ← map_neg]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [axisMatrixC]

theorem axisB_apply (v : EuclideanSpace ℝ (Fin 4)) :
    axisB v = WithLp.toLp 2 ![-v 2/2, v 3/2, v 0/2, -v 1/2] := by
  rw [axisB, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixB, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring


theorem axisC_apply (v : EuclideanSpace ℝ (Fin 4)) :
    axisC v = WithLp.toLp 2 ![-v 3/2, -v 2/2, v 1/2, v 0/2] := by
  rw [axisC, matrixOperator_apply]
  congr 1
  ext i
  fin_cases i <;> simp [axisMatrixC, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring


theorem axisB_norm_le : ‖axisB‖ ≤ 1 := by
  apply axisB.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  have hs : ‖axisB v‖^2 = ‖v‖^2/4 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, axisB_apply]
    simp [Fin.sum_univ_succ]
    ring
  nlinarith [norm_nonneg (axisB v), norm_nonneg v, sq_nonneg ‖v‖]


theorem axisC_norm_le : ‖axisC‖ ≤ 1 := by
  apply axisC.opNorm_le_bound zero_le_one
  intro v
  rw [one_mul]
  have hs : ‖axisC v‖^2 = ‖v‖^2/4 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, axisC_apply]
    simp [Fin.sum_univ_succ]
    ring
  nlinarith [norm_nonneg (axisC v), norm_nonneg v, sq_nonneg ‖v‖]


@[expose] def tripleMoment {R : Type uR} [Ring R] (X Y Z : R) : ℕ → ℕ → ℕ → ℕ → R
  | 0, a, b, c => X^a * Y^b * Z^c
  | k+1, a, b, c => tripleMoment X Y Z k (a+1) b c +
      tripleMoment X Y Z k a (b+1) c + tripleMoment X Y Z k a b (c+1)

theorem tripleMoment_four {R : Type uR} [Ring R] (X Y Z : R) :
    tripleMoment X Y Z 4 0 0 0 = X^4+Y^4+Z^4 +
      4 • (X^3*Y+X^3*Z+X*Y^3+Y^3*Z+X*Z^3+Y*Z^3) +
      6 • (X^2*Y^2+X^2*Z^2+Y^2*Z^2) +
      12 • (X^2*Y*Z+X*Y^2*Z+X*Y*Z^2) := by
  simp only [tripleMoment, Nat.reduceAdd, pow_zero, pow_one, one_mul, mul_one]
  noncomm_ring

@[expose] def plane (f g : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := !![0,-f/2,-g/2,0; f/2,0,0,g/2; g/2,0,0,-f/2; 0,-g/2,f/2,0]
@[expose] def third : Matrix (Fin 4) (Fin 4) ℝ := axisMatrixC

lemma plane_sub (f g h k : ℝ) : plane f g - plane h k = plane (f-h) (g-k) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane] <;> ring
lemma plane_neg (f g : ℝ) : -plane f g = plane (-f) (-g) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plane] <;> ring

@[expose] def moment4Plane (f g h k : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  tripleMoment (plane f g) (plane h k - plane f g) (-plane h k) 4 0 0 0


end
end RP3.Rotation
