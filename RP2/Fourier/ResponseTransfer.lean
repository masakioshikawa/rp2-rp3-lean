import RP2.ComplexCurrents

/-!
# Transferring a small response between nearby real edge fields

The estimate is proved for the squared interaction. The elementary Young
inequality bounds the current cross term and gives an error of order N⁻¹
for the Fourier profile approximation. No sign of the response is assumed.
-/
namespace RP2.Quadratic
noncomputable section
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace
namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
def axisSecondCoefficient (S : SpinSystem V E) (σ : V → RP2.Spin) (e : E) : ℝ :=
  2 * S.strength e *
    (⟪(σ (S.left e)).val, axisC (σ (S.right e)).val⟫_ℝ ^ 2 +
      ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
        ⟪(σ (S.left e)).val, (axisC ^ 2) (σ (S.right e)).val⟫_ℝ)

omit [Fintype V] in
theorem secondAxisEnergy_eq_sum (S : SpinSystem V E) (u v : E → ℝ) (σ) :
    S.secondAxisEnergy u v σ = ∑ e, S.axisSecondCoefficient σ e * (u e * v e) := by
  apply Finset.sum_congr rfl
  intro e _
  unfold axisSecondCoefficient
  ring

omit [Fintype V] in
theorem abs_axisSecondCoefficient_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (σ) (e : E) :
    |S.axisSecondCoefficient σ e| ≤ 4 * β := by
  have hc := (abs_inner_operator_le (σ (S.left e)) (σ (S.right e)) axisC).trans axisC_norm_le
  have hd := abs_real_inner_le_norm (σ (S.left e)).val (σ (S.right e)).val
  simp only [RP2.spin_norm, one_mul] at hd
  have hcc : ‖axisC ^ 2‖ ≤ 1 := (norm_pow_le _ _).trans
    (pow_le_one₀ (norm_nonneg _) axisC_norm_le)
  have he := (abs_inner_operator_le (σ (S.left e)) (σ (S.right e)) (axisC ^ 2)).trans hcc
  have hs : |⟪(σ (S.left e)).val, axisC (σ (S.right e)).val⟫_ℝ ^ 2| ≤ 1 := by
    rw [abs_pow]
    exact (pow_le_one₀ (abs_nonneg _) hc)
  have hp : |⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
      ⟪(σ (S.left e)).val, (axisC ^ 2) (σ (S.right e)).val⟫_ℝ| ≤ 1 := by
    rw [abs_mul]
    exact mul_le_one₀ hd (abs_nonneg _) he
  have hsum := (abs_add_le _ _).trans (add_le_add hs hp)
  unfold axisSecondCoefficient
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (2 * β) * (1 + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hb e) (by norm_num)) hsum
        (abs_nonneg _) (by have := (abs_nonneg _).trans (hb e); positivity)
    _ = _ := by ring

omit [Fintype V] in
theorem abs_axisCurrent_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (u : E → ℝ) (σ) :
    |S.firstEnergy (fun e => u e • axisC) σ| ≤ 2 * β * ∑ e, |u e| := by
  unfold firstEnergy
  rw [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  have hβ : 0 ≤ β := (abs_nonneg _).trans (hb e)
  have hi := abs_real_inner_le_norm (σ (S.left e)).val (σ (S.right e)).val
  simp only [RP2.spin_norm, one_mul] at hi
  have hc := (abs_inner_operator_le (σ (S.left e)) (σ (S.right e)) axisC).trans axisC_norm_le
  simp only [smul_apply, real_inner_smul_right, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * β * 1 * (|u e| * 1) := by
      gcongr
      exact hb e
    _ = _ := by ring

omit [Fintype V] in
theorem axisCurrent_sub (S : SpinSystem V E) (u v : E → ℝ) (σ) :
    S.firstEnergy (fun e => (u e - v e) • axisC) σ =
      S.firstEnergy (fun e => u e • axisC) σ -
        S.firstEnergy (fun e => v e • axisC) σ := by
  simp only [firstEnergy, smul_apply, real_inner_smul_right, sub_mul, mul_sub,
    Finset.sum_sub_distrib]

omit [Fintype V] in
theorem secondAxisEnergy_lower (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (u : E → ℝ) (σ) :
    -(4 * β * ∑ e, (u e)^2) ≤ S.secondAxisEnergy u u σ := by
  rw [S.secondAxisEnergy_eq_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := (abs_le.mp (S.abs_axisSecondCoefficient_le β hb σ e)).1
  simpa only [pow_two, neg_mul] using mul_le_mul_of_nonneg_right h (sq_nonneg (u e))

omit [Fintype V] in
theorem secondAxisEnergy_difference_le (S : SpinSystem V E) (β : ℝ)
    (hβ : 0 ≤ β) (hb : ∀ e, |S.strength e| ≤ β) (u v : E → ℝ) (σ) :
    S.secondAxisEnergy v v σ - S.secondAxisEnergy u u σ ≤
      4 * β * ∑ e, |u e - v e| * (|u e| + |v e|) := by
  simp only [S.secondAxisEnergy_eq_sum, ← Finset.sum_sub_distrib, Finset.mul_sum, ← mul_sub]
  apply Finset.sum_le_sum
  intro e _
  have hs : |v e * v e - u e * u e| ≤ |u e - v e| * (|u e| + |v e|) := by
    rw [show v e*v e-u e*u e=(v e-u e)*(v e+u e) by ring, abs_mul, abs_sub_comm]
    exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans_eq (add_comm _ _)) (abs_nonneg _)
  calc
    _ ≤ |S.axisSecondCoefficient σ e * (v e*v e-u e*u e)| := le_abs_self _
    _ = |S.axisSecondCoefficient σ e| * |v e*v e-u e*u e| := abs_mul _ _
    _ ≤ _ := mul_le_mul (S.abs_axisSecondCoefficient_le β hb σ e) hs (abs_nonneg _) (by positivity)

omit [Fintype V] in
theorem continuous_secondAxisEnergy (S : SpinSystem V E) (u v : E → ℝ) :
    Continuous (S.secondAxisEnergy u v) := by unfold secondAxisEnergy; fun_prop

theorem transfer_average_add (S : SpinSystem V E)
    {f g : (V → RP2.Spin) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    S.average (fun σ => f σ + g σ) = S.average f + S.average g :=
  S.average_add (f := f) (g := g) hf hg

/-- A model-specific response transfer estimate. Only explicit couplings and
actual Gibbs averages occur in the statement. -/
theorem real_response_transfer (S : SpinSystem V E) (β a : ℝ)
    (hβ : 0 ≤ β) (ha : 0 ≤ a) (hb : ∀ e, |S.strength e| ≤ β)
    (u v : E → ℝ) (hr : -S.secondAxisResponse v v ≤ a) :
    -S.secondAxisResponse u u ≤ a +
      4 * β * ∑ e, |u e-v e| * (|u e|+|v e|) +
      (2 * β * ∑ e, |u e-v e|) * (4 * β * ∑ e, (u e)^2 + 1) +
      (2 * β * ∑ e, |u e-v e|)^2 := by
  let A := 4 * β * ∑ e, (u e)^2
  let B := 2 * β * ∑ e, |u e-v e|
  let C := 4 * β * ∑ e, |u e-v e| * (|u e|+|v e|)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let Ju := fun σ => S.firstEnergy (fun e => u e • axisC) σ
  let Jv := fun σ => S.firstEnergy (fun e => v e • axisC) σ
  have hJu : Continuous Ju := S.continuous_firstEnergy _
  have hJv : Continuous Jv := S.continuous_firstEnergy _
  have hu : S.secondAxisResponse u u =
      S.average (S.secondAxisEnergy u u) + S.average (fun σ => (Ju σ)^2) := by
    calc
      S.secondAxisResponse u u = S.average (fun σ => S.secondAxisEnergy u u σ+(Ju σ)^2) := by
        unfold secondAxisResponse
        congr 1
        funext σ
        dsimp only [Ju]
        ring
      _ = _ := S.transfer_average_add (f := S.secondAxisEnergy u u) (g := fun σ => (Ju σ)^2)
        (S.continuous_secondAxisEnergy u u) (hJu.pow 2)
  have hv : S.average (fun σ => S.secondAxisEnergy v v σ + (Jv σ)^2) =
      S.secondAxisResponse v v := by
    unfold secondAxisResponse
    congr 1
    funext σ
    simp only [Jv, pow_two]
  by_cases hR : S.secondAxisResponse u u ≤ 0
  · have hQ : -A ≤ S.average (S.secondAxisEnergy u u) := by
      rw [← S.average_const (-A)]
      exact S.average_mono continuous_const (S.continuous_secondAxisEnergy u u)
        (S.secondAxisEnergy_lower β hb u)
    have hM : S.average (fun σ => (Ju σ)^2) ≤ A := by rw [hu] at hR; linarith
    have hpoint (σ : V → RP2.Spin) :
        S.secondAxisEnergy v v σ + (Jv σ)^2 ≤
          S.secondAxisEnergy u u σ + (Ju σ)^2 + C + B*((Ju σ)^2+1)+B^2 := by
      have hd : |Jv σ-Ju σ| ≤ B := by
        rw [abs_sub_comm]
        simpa only [S.axisCurrent_sub] using S.abs_axisCurrent_le β hb (fun e => u e-v e) σ
      have htri : |Jv σ| ≤ |Jv σ-Ju σ|+|Ju σ| := by
        simpa only [sub_add_cancel] using abs_add_le (Jv σ-Ju σ) (Ju σ)
      have hnorm : |Jv σ| ≤ |Ju σ| + B := htri.trans (by linarith)
      have hsq : (Jv σ)^2 ≤ (|Ju σ|+B)^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hnorm 2
      have hy : 2*|Ju σ| ≤ (Ju σ)^2+1 := by nlinarith [sq_nonneg (|Ju σ|-1), sq_abs (Ju σ)]
      have hby := mul_le_mul_of_nonneg_left hy hB
      have hq := S.secondAxisEnergy_difference_le β hβ hb u v σ
      change S.secondAxisEnergy v v σ-S.secondAxisEnergy u u σ ≤ C at hq
      nlinarith [sq_abs (Ju σ)]
    have hav := S.average_mono
      (f := fun σ => S.secondAxisEnergy v v σ+(Jv σ)^2)
      (g := fun σ => S.secondAxisEnergy u u σ+(Ju σ)^2+C+B*((Ju σ)^2+1)+B^2)
      ((S.continuous_secondAxisEnergy v v).add (hJv.pow 2))
      (((((S.continuous_secondAxisEnergy u u).add (hJu.pow 2)).add continuous_const).add
        (continuous_const.mul ((hJu.pow 2).add continuous_const))).add continuous_const) hpoint
    rw [hv] at hav
    rw [S.transfer_average_add
      (f := fun σ => S.secondAxisEnergy u u σ+(Ju σ)^2+C+B*((Ju σ)^2+1))
      (g := fun _ => B^2)
      ((((S.continuous_secondAxisEnergy u u).add (hJu.pow 2)).add continuous_const).add
        (continuous_const.mul ((hJu.pow 2).add continuous_const))) continuous_const,
      S.average_const,
      S.transfer_average_add
        (f := fun σ => S.secondAxisEnergy u u σ+(Ju σ)^2+C)
        (g := fun σ => B*((Ju σ)^2+1))
        (((S.continuous_secondAxisEnergy u u).add (hJu.pow 2)).add continuous_const)
        (continuous_const.mul ((hJu.pow 2).add continuous_const)),
      S.transfer_average_add
        (f := fun σ => S.secondAxisEnergy u u σ+(Ju σ)^2)
        (g := fun _ => C)
        ((S.continuous_secondAxisEnergy u u).add (hJu.pow 2)) continuous_const,
      S.average_const, S.average_mul_const B (fun σ => (Ju σ)^2+1),
      S.transfer_average_add (f := fun σ => (Ju σ)^2) (g := fun _ => 1)
        (hJu.pow 2) continuous_const, S.average_const] at hav
    have hu' : S.average (fun σ => S.secondAxisEnergy u u σ+(Ju σ)^2) =
        S.secondAxisResponse u u := by
      unfold secondAxisResponse
      congr 1
      funext σ
      simp only [Ju, pow_two]
    rw [hu'] at hav
    have hm := mul_le_mul_of_nonneg_left hM hB
    change -S.secondAxisResponse u u ≤ a+C+B*(A+1)+B^2
    linarith
  · change -S.secondAxisResponse u u ≤ a+C+B*(A+1)+B^2
    have ht : 0 ≤ a+C+B*(A+1)+B^2 := by positivity
    linarith

end SpinSystem
end
end RP2.Quadratic
