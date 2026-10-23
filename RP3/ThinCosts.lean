module

public import RP3.ThinFourier

public section

/-! Numerical scaling of the balanced-profile and real-response costs. -/
namespace RP3.Fourier.LatticeGraph
noncomputable section

theorem thin_balanced_column_eq (P δ : ℝ) (hδ : 0 < δ) :
    64*δ*(P/(δ*Real.sqrt δ)*δ+(P/Real.sqrt δ)*(Real.pi/4))^2 =
      64*(P+P*(Real.pi/4))^2 := by
  have hs : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  have hh : P/(δ*Real.sqrt δ)*δ+(P/Real.sqrt δ)*(Real.pi/4) =
      (P+P*(Real.pi/4))/Real.sqrt δ := by field_simp
  rw [hh, div_pow, Real.sq_sqrt hδ.le]
  field_simp

theorem thin_balanced_block_square (P δ : ℝ) (hδ : 0 < δ) :
    (2*thinModeBlockConstant (P/Real.sqrt δ) (P/(δ*Real.sqrt δ)) δ)^2 =
      (2*modeBlockConstant P)^2/δ := by
  have hs : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
  have hh : P/(δ*Real.sqrt δ)*δ = P/Real.sqrt δ := by field_simp
  unfold thinModeBlockConstant modeBlockConstant
  rw [hh]
  simp only [mul_pow]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  simp only [div_pow, Real.sq_sqrt hδ.le]
  ring

theorem thin_balanced_rotation_cost (M P δ : ℝ) (hδ : 0 < δ) :
    thinRotationCost M (P/Real.sqrt δ)
      (2*thinModeBlockConstant (P/Real.sqrt δ) (P/(δ*Real.sqrt δ)) δ)
      (64*δ*(P/(δ*Real.sqrt δ)*δ+(P/Real.sqrt δ)*(Real.pi/4))^2) =
    thinRotationCost M P (2*modeBlockConstant P) (64*(P+P*(Real.pi/4))^2)/δ := by
  rw [thin_balanced_column_eq P δ hδ]
  unfold thinRotationCost
  rw [thin_balanced_block_square P δ hδ, div_pow, Real.sq_sqrt hδ.le]
  ring

/-- Every monomial in the real-response remainder costs at most six inverse
powers of the annulus width. -/
theorem thin_transfer_cost_le (M L D δ : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hD : 0 ≤ D) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    transferCostConstant M (L/δ) (D/δ^3) ≤
      transferCostConstant M L D / δ^6 := by
  have hd1 : δ^1 ≤ 1 := by simpa using hδ1
  have hd2 : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hd3 : δ^3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have h4 : 1/δ^4 ≤ 1/δ^6 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc δ^6 = δ^4*δ^2 := by ring
      _ ≤ δ^4*1 := mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ = _ := mul_one _
  have h5 : 1/δ^5 ≤ 1/δ^6 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc δ^6 = δ^5*δ := by ring
      _ ≤ δ^5*1 := mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ = _ := mul_one _
  have h3 : 1/δ^3 ≤ 1/δ^6 := by
    apply one_div_le_one_div_of_le (by positivity)
    calc δ^6 = δ^3*δ^3 := by ring
      _ ≤ δ^3*1 := mul_le_mul_of_nonneg_left hd3 (by positivity)
      _ = _ := mul_one _
  have h4' := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 1024*M*D*L)
  have h5' := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 262144*M^2*D*L^2)
  have h3' := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ 512*M*D)
  unfold transferCostConstant
  calc _ = 1024*M*D*L*(1/δ^4) + 512*M*D^2*(1/δ^6) +
        262144*M^2*D*L^2*(1/δ^5) + 512*M*D*(1/δ^3) +
        262144*M^2*D^2*(1/δ^6) := by ring
    _ ≤ 1024*M*D*L*(1/δ^6) + 512*M*D^2*(1/δ^6) +
        262144*M^2*D*L^2*(1/δ^6) + 512*M*D*(1/δ^6) +
        262144*M^2*D^2*(1/δ^6) := by linarith
    _ = _ := by ring

end
end RP3.Fourier.LatticeGraph
