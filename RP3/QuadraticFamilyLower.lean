import RP3.QuadraticFamilyEstimates

namespace RP3.Quadratic

universe uE uI uV

noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open RP3.Fourier
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

theorem norm_avg_row_sum (S : SpinSystem V E) (u : I → E → ℂ)
    (F : E → C((V → RP3.Spin), ℂ)) (c : ℝ)
    (hF : ∀ e, ‖S.averageComplexLinear (F e)‖ ≤ c * rowSquare u e) :
    ‖S.averageComplexLinear (∑ e, F e)‖ ≤ c * familyHSSquare u := by
  simpa only [familyHSSquare, Finset.mul_sum] using
    S.norm_averageComplex_sum_le F (fun e => c * rowSquare u e) hF

omit [Fintype I] in
theorem norm_avg_add_le (S : SpinSystem V E) (F G : C((V → RP3.Spin), ℂ))
    (a b : ℝ) (hF : ‖S.averageComplexLinear F‖ ≤ a)
    (hG : ‖S.averageComplexLinear G‖ ≤ b) :
    ‖S.averageComplexLinear (F+G)‖ ≤ a+b := by
  rw [map_add]
  exact (norm_add_le _ _).trans (add_le_add hF hG)

theorem norm_familyRemainder_le (S : SpinSystem V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, |S.strength e| ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    ‖S.averageComplexLinear (S.familyRemainder (fun i => S.edgeGradient (f i)))‖ ≤
      (6*(16*β)^2+4*(16*β)*Real.sqrt (16*β)+16*β) * familyHSSquare (fun i => S.edgeGradient (f i)) := by
  let B : ℝ := 16*β
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hcoeff : ∀ a e σ, ‖S.mixedCoefficientObservable a e σ‖ ≤ B :=
    fun a e σ => S.mixedCoefficientObservable_norm_le β hb a e σ
  let u := fun i => S.edgeGradient (f i)
  let T := familyKernel u
  let X := fun M e => S.currentObservable M (T e)
  let C := S.mixedCoefficientObservable
  let bar := conjugateObservable (Ω := V → RP3.Spin)
  let k : ℂ → C((V → RP3.Spin), ℂ) := ContinuousMap.const (V → RP3.Spin)
  let H := familyHSSquare u
  have ha (e : E) : S.averageLinear (normObservable (X axisA e) * normObservable (X axisA e)) ≤
      B * rowSquare u e := (S.row_current_moment β hb axisA axisA_skew axisA_norm_le f hP e).trans
        (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (rowSquare_nonneg u e))
  have hb' (e : E) : S.averageLinear (normObservable (X axisB e) * normObservable (X axisB e)) ≤
      B * rowSquare u e := (S.row_current_moment β hb axisB axisB_skew axisB_norm_le f hP e).trans
        (mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) (rowSquare_nonneg u e))
  have hac (e : E) : S.averageLinear (normObservable (bar (X axisA e)) *
      normObservable (bar (X axisA e))) ≤ B * rowSquare u e := by
    simpa only [bar, normObservable_conjugate] using ha e
  have hbc (e : E) : S.averageLinear (normObservable (bar (X axisB e)) *
      normObservable (bar (X axisB e))) ≤ B * rowSquare u e := by
    simpa only [bar, normObservable_conjugate] using hb' e
  have row (a : MixedAlgebra.Slot)
      (F G : E → C((V → RP3.Spin), ℂ))
      (hF : ∀ e, S.averageLinear (normObservable (F e)*normObservable (F e)) ≤ B*rowSquare u e)
      (hG : ∀ e, S.averageLinear (normObservable (G e)*normObservable (G e)) ≤ B*rowSquare u e) :
      ‖S.averageComplexLinear (∑ e, C a e * F e * G e)‖ ≤ B^2*H := by
    apply S.norm_avg_row_sum u _ (B^2)
    intro e
    exact (S.norm_avg_coeff_two B (B*rowSquare u e) hB hcoeff a e (F e) (G e)
      (hF e) (hG e)).trans_eq (by ring)
  have b1 := row .aa
    (X axisB) (fun e => bar (X axisB e)) hb' hbc
  have b2 := row .ab (X axisB) (X axisA) hb' ha
  have b3 := row .ab (fun e => bar (X axisA e))
    (fun e => bar (X axisB e)) hac hbc
  have b4 := row .bb
    (fun e => bar (X axisA e)) (X axisA) hac ha
  have pair (a b : MixedAlgebra.Slot)
      (z : E → E → ℂ) (hz : ∀ e l, ‖z e l‖ = ‖T e l‖^2) :
      ‖S.averageComplexLinear (∑ e, ∑ l, C a e * C b l * k (z e l))‖ ≤ B^2*H := by
    apply S.norm_avg_row_sum u _ (B^2)
    intro e
    calc _ ≤ ∑ l, B^2*‖T e l‖^2 := by
          apply S.norm_averageComplex_sum_le
          intro l
          exact (S.norm_avg_coeff_coeff_const B hB hcoeff a b e l (z e l)).trans_eq
            (by rw [hz e l])
         _ = _ := by rw [← Finset.mul_sum]; rfl
  have b5 := pair .aa .bb (fun e l => T e l*conj (T e l))
    (by intro e l; simp only [norm_mul, Complex.norm_conj, pow_two])
  have b6 := pair .ab .ab (fun e l => T e l^2)
    (by intro e l; exact norm_pow _ _)
  have triple (a : MixedAlgebra.Slot)
      (z : E → ℂ) (hz : ∀ e, ‖z e‖ ≤ Real.sqrt (rowSquare u e))
      (F : E → C((V → RP3.Spin), ℂ))
      (hF : ∀ e, S.averageLinear (normObservable (F e)*normObservable (F e)) ≤ B*rowSquare u e) :
      ‖S.averageComplexLinear (∑ e, C a e * k (z e) * F e)‖ ≤ B*Real.sqrt B*H := by
    apply S.norm_avg_row_sum u _ (B*Real.sqrt B)
    intro e
    exact S.norm_avg_coeff_const_current B (rowSquare u e) hB (rowSquare_nonneg u e)
      hcoeff a e (z e) (hz e) (F e) (hF e)
  have hz (e : E) : ‖T e e‖ ≤ Real.sqrt (rowSquare u e) := kernel_diag_norm_le_sqrt u e
  have hzc (e : E) : ‖conj (T e e)‖ ≤ Real.sqrt (rowSquare u e) := by
    rw [Complex.norm_conj]; exact hz e
  have b7 := triple .aab (fun e => T e e) hz
    (fun e => bar (X axisB e)) hbc
  have b8 := triple .abb (fun e => T e e) hz (X axisA) ha
  have b9 := triple .aab (fun e => conj (T e e)) hzc (X axisB) hb'
  have b10 := triple .abb (fun e => conj (T e e)) hzc
    (fun e => bar (X axisA e)) hac
  have b11 : ‖S.averageComplexLinear (∑ e, C .aabb e * k (T e e*conj (T e e)))‖ ≤ B*H := by
    apply S.norm_avg_row_sum u _ B
    intro e
    calc _ ≤ B*‖T e e*conj (T e e)‖ := S.norm_avg_coeff_const B hcoeff .aabb e _
         _ = B*‖T e e‖^2 := by rw [norm_mul, Complex.norm_conj, pow_two]
         _ ≤ B*rowSquare u e := mul_le_mul_of_nonneg_left (kernel_diag_sq_le_row u e) hB
  have hadd := S.norm_avg_add_le
  have h := hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _
    (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ (hadd _ _ _ _ b1 b2)
      b3) b4) b5) b6) b7) b8) b9) b10) b11
  change ‖S.averageComplexLinear (S.familyRemainder u)‖ ≤ _ at h ⊢
  exact h.trans_eq (by dsimp only [H, B]; ring)

theorem fourth_family_lower (S : SpinSystem V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, |S.strength e| ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    -((6*(16*β)^2+4*(16*β)*Real.sqrt (16*β)+16*β)*familyHSSquare (fun i => S.edgeGradient (f i))) ≤
      (S.averageComplexLinear (∑ i, ∑ j,
        S.complexMixedObservable (S.edgeGradient (f i)) (fun e => conj (S.edgeGradient (f i) e))
          (fun e => conj (S.edgeGradient (f j) e)) (S.edgeGradient (f j)))).re := by
  rw [S.familyObservable_contraction, map_add, Complex.add_re]
  have hp := S.averageComplex_pos_square (S.familyPaired (fun i => S.edgeGradient (f i)))
  have hr := S.norm_familyRemainder_le β hβ hb f hP
  have hre := (abs_le.mp (Complex.abs_re_le_norm (S.averageComplexLinear
    (S.familyRemainder (fun i => S.edgeGradient (f i)))))).1
  linarith

end SpinSystem

end

end RP3.Quadratic
