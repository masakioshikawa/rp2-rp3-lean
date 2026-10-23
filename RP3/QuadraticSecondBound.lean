import RP3.QuadraticSecondGauge
/-!
# Quantitative bounds for the RP³ second response
Adapted from OpenAI ClassicalON/SecondBound.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The coefficient estimate is proved for the quadratic interaction, giving 4β.
-/

namespace RP3.Quadratic

universe uE uV

noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem abs_scalarHessianCoefficient_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (g : SpinOperator 4) (hg : ‖g‖ ≤ 1)
    (σ : V → RP3.Spin) (e : E) : |S.scalarHessianCoefficient g σ e| ≤ 4*β := by
  have hu := (abs_inner_operator_le (σ (S.left e)) (σ (S.right e)) g).trans hg
  have hv : |⟪(σ (S.left e)).val, (g^2) (σ (S.right e)).val⟫_ℝ| ≤ 1 :=
    (abs_inner_operator_le _ _ _).trans
      ((norm_pow_le g 2).trans (pow_le_one₀ (norm_nonneg _) hg))
  have hw : |⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ| ≤ 1 := by
    simpa only [RP3.spin_norm, one_mul] using
      abs_real_inner_le_norm (σ (S.left e)).val (σ (S.right e)).val
  have hu2 : |⟪(σ (S.left e)).val, g (σ (S.right e)).val⟫_ℝ ^ 2| ≤ 1 := by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg _) hu 2
  have huv : |⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
      ⟪(σ (S.left e)).val, (g^2) (σ (S.right e)).val⟫_ℝ| ≤ 1 := by
    rw [abs_mul]
    simpa using mul_le_mul hw hv (abs_nonneg _) zero_le_one
  have hs := (abs_add_le _ _).trans (add_le_add hu2 huv)
  norm_num at hs
  unfold scalarHessianCoefficient
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc _ ≤ (2*β)*2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hb e) (by norm_num)) hs
        (abs_nonneg _) (by have := (abs_nonneg _).trans (hb e); positivity)
    _ = 4*β := by ring

omit [Fintype V] in
theorem complexHessian_normSq_re (S : SpinSystem V E) (M : SpinOperator 4)
    (u : E → ℂ) (σ : V → RP3.Spin) :
    (S.complexHessian M (fun e => u e * conj (u e)) σ).re =
      ∑ e, S.scalarHessianCoefficient M σ e * ‖u e‖^2 := by
  simp [complexHessian, MixedAlgebra.weighted, Complex.mul_conj, Complex.normSq_eq_norm_sq, -Complex.ofReal_pow]

theorem complexSecondResponse_upper (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (u : E → ℂ) :
    -(S.complexSecondResponse u (fun e => conj (u e))).re ≤ (4*β)*∑ e, ‖u e‖^2 := by
  unfold complexSecondResponse
  rw [S.averageComplex_re]
  have h (σ : V → RP3.Spin) :
      -((4*β)*∑ e, ‖u e‖^2) ≤
        reObservable (S.complexSecondObservable u (fun e => conj (u e))) σ := by
    change _ ≤ (S.complexHessian axisC (u*(fun e => conj (u e))) σ +
      S.complexCurrent axisC u σ * S.complexCurrent axisC (fun e => conj (u e)) σ).re
    have hcc : S.complexCurrent axisC (fun e => conj (u e)) σ =
        conj (S.complexCurrent axisC u σ) := by
      simpa only [Complex.star_def] using S.complexCurrent_conj axisC u σ
    rw [hcc, Complex.mul_conj, Complex.add_re, Complex.ofReal_re]
    have hc := S.complexHessian_normSq_re axisC u σ
    change (S.complexHessian axisC (u*(fun e => conj (u e))) σ).re = _ at hc
    rw [hc]
    have he : -((4*β)*∑ e, ‖u e‖^2) ≤ ∑ e, S.scalarHessianCoefficient axisC σ e*‖u e‖^2 := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_le_sum
      intro e _
      have hb' := (abs_le.mp (S.abs_scalarHessianCoefficient_le β hb axisC axisC_norm_le σ e)).1
      nlinarith [sq_nonneg ‖u e‖]
    exact he.trans (le_add_of_nonneg_right (Complex.normSq_nonneg _))
  have hm := S.averageLinear_mono (ContinuousMap.const _ (-((4*β)*∑ e, ‖u e‖^2)))
    (reObservable (S.complexSecondObservable u (fun e => conj (u e)))) h
  rw [S.averageLinear_const] at hm
  linarith

omit [Fintype V] [Fintype E] in

def commutatorForm (S : SpinSystem V E) (f g : V → ℂ) : E → ℂ :=
  (1/2 : ℂ) • S.complexCross f g

omit [Fintype V] [Fintype E] in
theorem commutatorForm_adjust (S : SpinSystem V E) (f g : V → ℂ) :
    S.commutatorForm f g + S.edgeGradient ((1/2 : ℂ) • (f*g)) =
      fun e => ((f (S.left e)+f (S.right e))/2) * S.edgeGradient g e := by
  ext e
  simp only [commutatorForm, complexCross, edgeGradient, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype E] in
theorem commutatorForm_adjust_norm (S : SpinSystem V E) (f g : V → ℂ) (e : E) :
    ‖((f (S.left e)+f (S.right e))/2) * S.edgeGradient g e‖ ≤
      ‖f‖ * ‖S.edgeGradient g e‖ := by
  rw [norm_mul, norm_div]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  norm_num
  have h := norm_add_le (f (S.left e)) (f (S.right e))
  have hx := norm_le_pi_norm f (S.left e)
  have hy := norm_le_pi_norm f (S.right e)
  linarith

theorem commutatorForm_bound_left (S : SpinSystem V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, |S.strength e| ≤ β)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        (4*β)*(‖f‖^2*∑ e, ‖S.edgeGradient g e‖^2) := by
  let F : V → ℂ := (1/2 : ℂ) • (f*g)
  have hp (x) (s) (hs : S.pin x = some s) : F x = 0 := by
    simp only [F, Pi.smul_apply, Pi.mul_apply, hP x s hs, zero_mul, smul_zero]
  have hq (x) (s) (hs : S.pin x = some s) : conj (F x) = 0 := by rw [hp x s hs, map_zero]
  have hd : S.edgeGradient (fun x => conj (F x)) = fun e => conj (S.edgeGradient F e) := by
    ext e
    simp only [edgeGradient, map_sub]
  have hid := S.complexSecondResponse_add_gradients (S.commutatorForm f g)
    (fun e => conj (S.commutatorForm f g e)) F (fun x => conj (F x)) hp hq
  rw [hd] at hid
  have hc : ((fun e => conj (S.commutatorForm f g e)) + (fun e => conj (S.edgeGradient F e))) =
      (fun e => conj ((S.commutatorForm f g + S.edgeGradient F) e)) := by
    ext e
    simp only [Pi.add_apply, map_add]
  rw [hc] at hid
  rw [← hid]
  apply (S.complexSecondResponse_upper β hb _).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4*β)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  change ‖(S.commutatorForm f g + S.edgeGradient ((1/2 : ℂ) • (f*g))) e‖^2 ≤ _
  rw [S.commutatorForm_adjust]
  have h := S.commutatorForm_adjust_norm f g e
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ _)

/-- Simultaneous sign reversal leaves the bilinear response unchanged. -/
theorem complexSecondResponse_neg_neg (S : SpinSystem V E) (u v : E → ℂ) :
    S.complexSecondResponse (-u) (-v) = S.complexSecondResponse u v := by
  calc
    _ = -S.complexSecondResponse u (-v) := by
      simpa using S.complexSecondResponse_smul_left u (-v) (-1 : ℂ)
    _ = S.complexSecondResponse u v := by
      rw [show S.complexSecondResponse u (-v) = -S.complexSecondResponse u v from by
        simpa using S.complexSecondResponse_smul_right u v (-1 : ℂ)]
      exact neg_neg _

omit [Fintype V] [Fintype E] in
theorem commutatorForm_swap (S : SpinSystem V E) (f g : V → ℂ) :
    S.commutatorForm g f = -S.commutatorForm f g := by
  ext e
  simp only [commutatorForm, complexCross, Pi.smul_apply, smul_eq_mul, Pi.neg_apply]
  ring

theorem commutatorForm_bound_right (S : SpinSystem V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, |S.strength e| ≤ β)
    (f g : V → ℂ) (hQ : ∀ x s, S.pin x = some s → g x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
        (4*β)*(‖g‖^2*∑ e, ‖S.edgeGradient f e‖^2) := by
  have h := S.commutatorForm_bound_left β hβ hb g f hQ
  simp only [S.commutatorForm_swap f g] at h
  have hc : (fun e => conj ((-S.commutatorForm f g) e)) =
      -(fun e => conj (S.commutatorForm f g e)) := by
    ext e
    simp only [Pi.neg_apply, map_neg]
  rw [hc, S.complexSecondResponse_neg_neg] at h
  exact h

/-- Appendix A.4, with the coefficient proved for the squared interaction. -/
theorem commutatorForm_bound (S : SpinSystem V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, |S.strength e| ≤ β) (f g : V → ℂ)
    (hP : ∀ x s, S.pin x = some s → f x = 0)
    (hQ : ∀ x s, S.pin x = some s → g x = 0) :
    -(S.complexSecondResponse (S.commutatorForm f g)
      (fun e => conj (S.commutatorForm f g e))).re ≤
      (4*β)*min (‖f‖^2*∑ e, ‖S.edgeGradient g e‖^2)
        (‖g‖^2*∑ e, ‖S.edgeGradient f e‖^2) := by
  rcases le_total (‖f‖^2*∑ e, ‖S.edgeGradient g e‖^2)
      (‖g‖^2*∑ e, ‖S.edgeGradient f e‖^2) with h | h
  · rw [min_eq_left h]
    exact S.commutatorForm_bound_left β hβ hb f g hP
  · rw [min_eq_right h]
    exact S.commutatorForm_bound_right β hβ hb f g hQ

end SpinSystem

end

end RP3.Quadratic
