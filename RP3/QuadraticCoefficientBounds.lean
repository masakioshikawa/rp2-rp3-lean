module

public import RP3.QuadraticMixedJets

public section

/-! # Uniform bounds on the actual mixed RP³ coefficients -/
namespace RP3.Quadratic
noncomputable section
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

theorem norm_square_le_one (M : SpinOperator 4) (hM : ‖M‖ ≤ 1) : ‖M^2‖ ≤ 1 := by
  calc ‖M^2‖ ≤ ‖M‖ * ‖M‖ := by simpa only [pow_two] using norm_mul_le M M
       _ ≤ 1 * 1 := mul_le_mul hM hM (norm_nonneg _) zero_le_one
       _ = 1 := one_mul _

theorem mixedAB_norm_le : ‖mixedAB‖ ≤ 1 := by
  have he : mixedAB = (1/2 : ℝ) • (axisA*axisB+axisB*axisA) := by
    have h := congrArg matrixOperator mixedMatrixAB_sym
    simpa only [map_smul, map_add, map_mul, mixedAB, axisA, axisB] using h
  rw [he, norm_smul]
  have hab := (norm_mul_le axisA axisB).trans
    (mul_le_mul axisA_norm_le axisB_norm_le (norm_nonneg _) zero_le_one)
  have hba := (norm_mul_le axisB axisA).trans
    (mul_le_mul axisB_norm_le axisA_norm_le (norm_nonneg _) zero_le_one)
  have hsum := norm_add_le (axisA*axisB) (axisB*axisA)
  norm_num at hab hba ⊢
  linarith

theorem mixedAAB_norm_le : ‖mixedAAB‖ ≤ 1 := by
  have he : mixedAAB = (-1/12 : ℝ) • axisB := by
    simp only [mixedAAB, mixedMatrixAAB, map_smul, axisB]
  rw [he, norm_smul]
  norm_num
  linarith [axisB_norm_le]

theorem mixedABB_norm_le : ‖mixedABB‖ ≤ 1 := by
  have he : mixedABB = (-1/12 : ℝ) • axisA := by
    simp only [mixedABB, mixedMatrixABB, map_smul, axisA]
  rw [he, norm_smul]
  norm_num
  linarith [axisA_norm_le]

theorem mixedAABB_norm_le : ‖mixedAABB‖ ≤ 1 := by
  have he : mixedAABB = (-1/24 : ℝ) • (axisA^2+axisB^2) := by
    simp only [mixedAABB, mixedMatrixAABB, map_smul, map_add, map_pow, axisA, axisB]
  rw [he, norm_smul]
  have hsum := norm_add_le (axisA^2) (axisB^2)
  have ha := norm_square_le_one axisA axisA_norm_le
  have hb := norm_square_le_one axisB axisB_norm_le
  norm_num
  linarith


namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem abs_localInner_le_one (S : SpinSystem V E) (M : SpinOperator 4)
    (hM : ‖M‖ ≤ 1) (σ : V → RP3.Spin) (e : E) :
    |S.localInner M σ e| ≤ 1 :=
  (abs_inner_operator_le _ _ _).trans hM

omit [Fintype V] [Fintype E] in
theorem abs_mixedCoefficient_le_sixteen (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (s : MixedAlgebra.Slot)
    (σ : V → RP3.Spin) (e : E) :
    |(S.mixedCoefficients σ).get s e| ≤ 16 * β := by
  let I := fun M => S.localInner M σ e
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb e)
  have hi (M : SpinOperator 4) (hM : ‖M‖ ≤ 1) : |I M| ≤ 1 :=
    S.abs_localInner_le_one M hM σ e
  have hm (M N : SpinOperator 4) (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1) :
      |I M * I N| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (hi M hM) (hi N hN)
      (abs_nonneg _) zero_le_one
  have h1 : ‖(1 : SpinOperator 4)‖ ≤ 1 := norm_one.le
  have hAA := norm_square_le_one axisA axisA_norm_le
  have hBB := norm_square_le_one axisB axisB_norm_le
  have ha := hm 1 axisA h1 axisA_norm_le
  have hb' := hm 1 axisB h1 axisB_norm_le
  have haa : |I axisA ^ 2 + I 1 * I (axisA^2)| ≤ 2 := by
    rw [pow_two]
    exact (abs_add_le _ _).trans (by linarith [hm axisA axisA axisA_norm_le axisA_norm_le, hm 1 (axisA^2) h1 hAA])
  have hab : |I axisA * I axisB + I 1 * I mixedAB| ≤ 2 :=
    (abs_add_le _ _).trans (by linarith [hm axisA axisB axisA_norm_le axisB_norm_le, hm 1 mixedAB h1 mixedAB_norm_le])
  have hbb : |I axisB ^ 2 + I 1 * I (axisB^2)| ≤ 2 := by
    rw [pow_two]
    exact (abs_add_le _ _).trans (by linarith [hm axisB axisB axisB_norm_le axisB_norm_le, hm 1 (axisB^2) h1 hBB])
  have htwo (M N : SpinOperator 4) (hM : ‖M‖ ≤ 1) (hN : ‖N‖ ≤ 1) :
      |2 * I M * I N| ≤ 2 := by
    rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    linarith [hm M N hM hN]
  have haab : |I axisB * I (axisA^2) + 2 * I axisA * I mixedAB +
      I 1 * I mixedAAB| ≤ 4 := by
    calc _ ≤ |I axisB * I (axisA^2) + 2 * I axisA * I mixedAB| +
        |I 1 * I mixedAAB| := abs_add_le _ _
      _ ≤ |I axisB * I (axisA^2)| + |2 * I axisA * I mixedAB| +
        |I 1 * I mixedAAB| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 4 := by linarith [hm axisB (axisA^2) axisB_norm_le hAA, htwo axisA mixedAB axisA_norm_le mixedAB_norm_le, hm 1 mixedAAB h1 mixedAAB_norm_le]
  have habb : |I axisA * I (axisB^2) + 2 * I axisB * I mixedAB +
      I 1 * I mixedABB| ≤ 4 := by
    calc _ ≤ |I axisA * I (axisB^2) + 2 * I axisB * I mixedAB| +
        |I 1 * I mixedABB| := abs_add_le _ _
      _ ≤ |I axisA * I (axisB^2)| + |2 * I axisB * I mixedAB| +
        |I 1 * I mixedABB| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 4 := by linarith [hm axisA (axisB^2) axisA_norm_le hBB, htwo axisB mixedAB axisB_norm_le mixedAB_norm_le, hm 1 mixedABB h1 mixedABB_norm_le]
  have haabb : |I (axisA^2) * I (axisB^2) + 2 * (I mixedAB)^2 +
      2 * I axisA * I mixedABB + 2 * I axisB * I mixedAAB + I 1 * I mixedAABB| ≤ 8 := by
    have hAB : |2 * (I mixedAB)^2| ≤ 2 := by
      simpa only [pow_two, mul_assoc] using htwo mixedAB mixedAB mixedAB_norm_le mixedAB_norm_le
    calc _ ≤ |I (axisA^2) * I (axisB^2) + 2 * (I mixedAB)^2 +
        2 * I axisA * I mixedABB + 2 * I axisB * I mixedAAB| + |I 1 * I mixedAABB| :=
        abs_add_le _ _
      _ ≤ (|I (axisA^2) * I (axisB^2) + 2 * (I mixedAB)^2 +
        2 * I axisA * I mixedABB| + |2 * I axisB * I mixedAAB|) + |I 1 * I mixedAABB| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ ((|I (axisA^2) * I (axisB^2) + 2 * (I mixedAB)^2| +
        |2 * I axisA * I mixedABB|) + |2 * I axisB * I mixedAAB|) + |I 1 * I mixedAABB| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ (((|I (axisA^2) * I (axisB^2)| + |2 * (I mixedAB)^2|) +
        |2 * I axisA * I mixedABB|) + |2 * I axisB * I mixedAAB|) + |I 1 * I mixedAABB| :=
        add_le_add (add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl) le_rfl
      _ ≤ 8 := by linarith [hm (axisA^2) (axisB^2) hAA hBB, hAB, htwo axisA mixedABB axisA_norm_le mixedABB_norm_le, htwo axisB mixedAAB axisB_norm_le mixedAAB_norm_le, hm 1 mixedAABB h1 mixedAABB_norm_le]
  have hs (p : ℝ) (hp : |p| ≤ 8) : |2 * S.strength e * p| ≤ 16 * β := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    calc 2 * |S.strength e| * |p| ≤ 2 * β * 8 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hb e) (by norm_num)) hp (abs_nonneg _) (by positivity)
      _ = 16 * β := by ring
  cases s with
  | a => simpa only [MixedAlgebra.Coeffs.get, mixedCoefficients, mul_assoc] using (hs (I 1 * I axisA) (ha.trans (by norm_num)))
  | b => simpa only [MixedAlgebra.Coeffs.get, mixedCoefficients, mul_assoc] using (hs (I 1 * I axisB) (hb'.trans (by norm_num)))
  | aa => exact hs _ (haa.trans (by norm_num))
  | ab => exact hs _ (hab.trans (by norm_num))
  | bb => exact hs _ (hbb.trans (by norm_num))
  | aab => exact hs _ (haab.trans (by norm_num))
  | abb => exact hs _ (habb.trans (by norm_num))
  | aabb => exact hs _ haabb

end SpinSystem
end
end RP3.Quadratic
