module

public import RP3.QuadraticWard

public section

/-! # Bounds on the actual RP³ derivative jets -/
namespace RP3.Quadratic
noncomputable section
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

lemma abs_inner_operator_le (s t : RP3.Spin) (M : SpinOperator 4) :
    |⟪s.val, M t.val⟫_ℝ| ≤ ‖M‖ := by
  calc
    _ ≤ ‖s.val‖ * ‖M t.val‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖s.val‖ * (‖M‖ * ‖t.val‖) :=
      mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
    _ = ‖M‖ := by rw [RP3.spin_norm, RP3.spin_norm]; ring

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem abs_innerJet_at_zero_le_one (S : SpinSystem V E)
    (A : E → SpinOperator 4) (hA : ∀ e, ‖A e‖ ≤ 1)
    (e : E) (k : ℕ) (σ : V → RP3.Spin) :
    |S.innerJet (fun e => expPower (A e)) e k 0 σ| ≤ 1 := by
  simp only [innerJet, expPower_zero]
  exact (abs_inner_operator_le _ _ _).trans
    ((norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) (hA e)))

omit [Fintype V] [Fintype E] in
/-- The local k-th derivative is bounded by `2^k β`. The interaction
is squared, and the derivative is the product jet proved in ProductJets. -/
theorem abs_local_twistJet_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (A : E → SpinOperator 4)
    (hA : ∀ e, ‖A e‖ ≤ 1) (e : E) (k : ℕ) (σ : V → RP3.Spin) :
    |S.strength e * productJet (S.innerJet (fun e => expPower (A e)) e)
      (S.innerJet (fun e => expPower (A e)) e) k 0 0 0 σ| ≤ 2^k * β := by
  rw [abs_mul, mul_comm ((2 : ℝ)^k) β]
  exact mul_le_mul (hb e)
    (abs_productJet_le _ _ 0 σ (fun k => S.abs_innerJet_at_zero_le_one A hA e k σ)
      (fun k => S.abs_innerJet_at_zero_le_one A hA e k σ) k 0 0)
    (abs_nonneg _) ((abs_nonneg _).trans (hb e))

omit [Fintype V] [Fintype E] in
theorem abs_local_twistJet_le_sixteen (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (A : E → SpinOperator 4)
    (hA : ∀ e, ‖A e‖ ≤ 1) (e : E) (k : ℕ) (hk : k ≤ 4) (σ : V → RP3.Spin) :
    |S.strength e * productJet (S.innerJet (fun e => expPower (A e)) e)
      (S.innerJet (fun e => expPower (A e)) e) k 0 0 0 σ| ≤ 16 * β := by
  apply (S.abs_local_twistJet_le β hb A hA e k σ).trans
  have hp : (2 : ℝ)^k ≤ 16 := by
    calc (2 : ℝ)^k ≤ 2^4 := pow_le_pow_right₀ (by norm_num) hk
         _ = 16 := by norm_num
  exact mul_le_mul_of_nonneg_right hp ((abs_nonneg _).trans (hb e))

omit [Fintype V] in
theorem continuous_firstEnergy (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (S.firstEnergy A) := by unfold firstEnergy; fun_prop

omit [Fintype V] in
theorem continuous_secondEnergy (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (S.secondEnergy A) := by unfold secondEnergy; fun_prop

omit [Fintype V] in
theorem abs_secondEnergy_le (S : SpinSystem V E) (A : E → SpinOperator 4)
    (σ : V → RP3.Spin) :
    |S.secondEnergy A σ| ≤ ∑ e, 4 * |S.strength e| * ‖A e‖^2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro e _
  have hu := abs_inner_operator_le (σ (S.left e)) (σ (S.right e)) (A e)
  have hv := abs_inner_operator_le (σ (S.left e)) (σ (S.right e)) (A e ^ 2)
  have hw := abs_real_inner_le_norm (σ (S.left e)).val (σ (S.right e)).val
  simp only [RP3.spin_norm, one_mul] at hw
  have hu2 : |⟪(σ (S.left e)).val, A e (σ (S.right e)).val⟫_ℝ ^ 2| ≤ ‖A e‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have huv : |⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
      ⟪(σ (S.left e)).val, (A e ^ 2) (σ (S.right e)).val⟫_ℝ| ≤ ‖A e‖^2 := by
    rw [abs_mul]
    calc _ ≤ 1 * ‖A e‖^2 := mul_le_mul hw (hv.trans (norm_pow_le _ _))
           (abs_nonneg _) zero_le_one
         _ = _ := one_mul _
  have hs := (abs_add_le _ _).trans (add_le_add hu2 huv)
  calc
    _ = 2 * |S.strength e| * |⟪(σ (S.left e)).val, A e (σ (S.right e)).val⟫_ℝ ^ 2 +
        ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
          ⟪(σ (S.left e)).val, (A e ^ 2) (σ (S.right e)).val⟫_ℝ| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * |S.strength e| * (‖A e‖^2 + ‖A e‖^2) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring


omit [Fintype V] in
theorem abs_axis_secondEnergy_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (g : SpinOperator 4) (hg : ‖g‖ ≤ 1)
    (f : V → ℝ) (σ : V → RP3.Spin) :
    |S.secondEnergy (S.axisGradient f g) σ| ≤
      4 * β * ∑ e, (f (S.right e) - f (S.left e))^2 := by
  apply (S.abs_secondEnergy_le _ σ).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hβ := (abs_nonneg _).trans (hb e)
  have hn : ‖S.axisGradient f g e‖ ≤ |f (S.right e) - f (S.left e)| := by
    rw [axisGradient, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hg
  have hn2 : ‖S.axisGradient f g e‖^2 ≤ (f (S.right e) - f (S.left e))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hb e) (by norm_num)) hn2
    (sq_nonneg _) (by positivity)

/-- The second Ward identity gives a genuine Gibbs current estimate for
arbitrary pinned boundary spins and the squared RP³ interaction. -/
theorem gradient_current_bound (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (g : SpinOperator 4)
    (hg : g ∈ skewAdjoint (SpinOperator 4)) (hgn : ‖g‖ ≤ 1) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => (S.firstEnergy (S.axisGradient f g) σ)^2) ≤
      4 * β * ∑ e, (f (S.right e) - f (S.left e))^2 := by
  let A := S.axisGradient f g
  let C := 4 * β * ∑ e, (f (S.right e) - f (S.left e))^2
  have hl : -C ≤ S.average (S.secondEnergy A) := by
    rw [← S.average_const (-C)]
    apply S.average_mono continuous_const (S.continuous_secondEnergy A)
    intro σ
    exact (abs_le.mp (S.abs_axis_secondEnergy_le β hb g hgn f σ)).1
  have hw : S.average (S.secondEnergy A) +
      S.average (fun σ => (S.firstEnergy A σ)^2) = 0 := by
    rw [← S.average_add (f := S.secondEnergy A) (g := fun σ => (S.firstEnergy A σ)^2)
      (S.continuous_secondEnergy A)
      (by
        convert (S.continuous_firstEnergy A).pow 2 using 1)]
    exact S.second_gradient_identity g hg f hP
  change S.average (fun σ => (S.firstEnergy A σ)^2) ≤ C
  linarith

end SpinSystem
end
end RP3.Quadratic
