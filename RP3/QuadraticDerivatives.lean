import RP3.QuadraticGibbs
import RP3.ProductJets

/-!
# Actual derivatives of the pinned RP³ partition function

The Bell-polynomial differentiation proofs are adapted from OpenAI's
ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The energy derivatives themselves are newly constructed from product jets
for the squared interaction.
-/
namespace RP3.Quadratic

noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

def innerJet (S : SpinSystem V E) (U : E → ℕ → ℝ → SpinOperator 4)
    (e : E) (k : ℕ) (t : ℝ) (σ : V → RP3.Spin) : ℝ :=
  ⟪(σ (S.left e)).val, U e k t (σ (S.right e)).val⟫_ℝ

def pathEnergy (S : SpinSystem V E) (U : E → ℕ → ℝ → SpinOperator 4)
    (k : ℕ) (t : ℝ) (σ : V → RP3.Spin) : ℝ :=
  ∑ e, S.strength e * productJet (S.innerJet U e) (S.innerJet U e) k 0 0 t σ

omit [Fintype V] [Fintype E] in
theorem continuous_innerJet (S : SpinSystem V E) (U : E → ℕ → ℝ → SpinOperator 4)
    (hU : ∀ e k, Continuous (U e k)) (e : E) (k : ℕ) :
    Continuous (Function.uncurry (S.innerJet U e k)) := by
  exact (((continuous_apply (S.left e)).comp continuous_snd).subtype_val.inner
    (((hU e k).comp continuous_fst).clm_apply
      (((continuous_apply (S.right e)).comp continuous_snd).subtype_val)))

omit [Fintype V] [Fintype E] in
theorem hasDerivAt_innerJet (S : SpinSystem V E) (U : E → ℕ → ℝ → SpinOperator 4)
    (hU : ∀ e k t, HasDerivAt (U e k) (U e (k+1) t) t)
    (e : E) (k : ℕ) (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.innerJet U e k u σ) (S.innerJet U e (k+1) t σ) t := by
  exact ((hasDerivAt_const t (σ (S.left e)).val).inner ℝ
    ((hU e k t).clm_apply (hasDerivAt_const t (σ (S.right e)).val))).congr_deriv
    (by simp [innerJet])

omit [Fintype V] in
theorem continuous_pathEnergy (S : SpinSystem V E) (U : E → ℕ → ℝ → SpinOperator 4)
    (hU : ∀ e k, Continuous (U e k)) (k : ℕ) :
    Continuous (Function.uncurry (S.pathEnergy U k)) := by
  apply continuous_finsetSum
  intro e _
  exact continuous_const.mul (continuous_productJet _ _
    (S.continuous_innerJet U hU e) (S.continuous_innerJet U hU e) k 0 0)

omit [Fintype V] in
theorem hasDerivAt_pathEnergy (S : SpinSystem V E) (U : E → ℕ → ℝ → SpinOperator 4)
    (hU : ∀ e k t, HasDerivAt (U e k) (U e (k+1) t) t)
    (k : ℕ) (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.pathEnergy U k u σ) (S.pathEnergy U (k+1) t σ) t := by
  apply HasDerivAt.fun_sum
  intro e _
  exact (hasDerivAt_productJet _ _ (S.hasDerivAt_innerJet U hU e)
    (S.hasDerivAt_innerJet U hU e) k 0 0 t σ).const_mul (S.strength e)

def twistEnergy (S : SpinSystem V E) (A : E → SpinOperator 4) :
    ℕ → ℝ → (V → RP3.Spin) → ℝ :=
  S.pathEnergy (fun e => expPower (A e))

omit [Fintype V] in
theorem continuous_twistEnergy (S : SpinSystem V E) (A : E → SpinOperator 4) (k : ℕ) :
    Continuous (Function.uncurry (S.twistEnergy A k)) :=
  S.continuous_pathEnergy _ (fun e => continuous_expPower (A e)) k

omit [Fintype V] in
theorem hasDerivAt_twistEnergy (S : SpinSystem V E) (A : E → SpinOperator 4)
    (k : ℕ) (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.twistEnergy A k u σ) (S.twistEnergy A (k+1) t σ) t :=
  S.hasDerivAt_pathEnergy _ (fun e => hasDerivAt_expPower (A e)) k t σ

omit [Fintype V] in
@[simp] theorem twistEnergy_zero (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) :
    S.twistEnergy A 0 t σ = S.energy (fun e => NormedSpace.exp (t • A e)) σ := by
  simp [twistEnergy, pathEnergy, productJet, innerJet, expPower, energy, pow_two]

def firstEnergy (S : SpinSystem V E) (A : E → SpinOperator 4) (σ : V → RP3.Spin) : ℝ :=
  ∑ e, 2 * S.strength e * ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
    ⟪(σ (S.left e)).val, A e (σ (S.right e)).val⟫_ℝ

def secondEnergy (S : SpinSystem V E) (A : E → SpinOperator 4) (σ : V → RP3.Spin) : ℝ :=
  ∑ e, 2 * S.strength e *
    (⟪(σ (S.left e)).val, A e (σ (S.right e)).val⟫_ℝ ^ 2 +
      ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
        ⟪(σ (S.left e)).val, (A e ^ 2) (σ (S.right e)).val⟫_ℝ)

omit [Fintype V] in
theorem twistEnergy_one_at_zero (S : SpinSystem V E) (A : E → SpinOperator 4)
    (σ : V → RP3.Spin) : S.twistEnergy A 1 0 σ = S.firstEnergy A σ := by
  unfold twistEnergy pathEnergy firstEnergy
  apply Finset.sum_congr rfl
  intro e _
  simp only [squareJet_one, innerJet, expPower_zero, pow_zero, pow_one, one_apply_eq_self]
  ring

omit [Fintype V] in
theorem twistEnergy_two_at_zero (S : SpinSystem V E) (A : E → SpinOperator 4)
    (σ : V → RP3.Spin) : S.twistEnergy A 2 0 σ = S.secondEnergy A σ := by
  unfold twistEnergy pathEnergy secondEnergy
  apply Finset.sum_congr rfl
  intro e _
  simp only [squareJet_two, innerJet, expPower_zero, pow_zero, pow_one, one_apply_eq_self]
  ring

def firstWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) * S.twistEnergy A 1 t σ

def secondWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 2 t σ + (S.twistEnergy A 1 t σ)^2)

omit [Fintype V] in
theorem continuous_firstWeight (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (Function.uncurry (S.firstWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul (S.continuous_twistEnergy A 1)

omit [Fintype V] in
theorem continuous_secondWeight (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (Function.uncurry (S.secondWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    ((S.continuous_twistEnergy A 2).add ((S.continuous_twistEnergy A 1).pow 2))

omit [Fintype V] in
theorem hasDerivAt_weight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A t σ) t := by
  exact (S.hasDerivAt_twistEnergy A 0 t σ).exp

omit [Fintype V] in
theorem hasDerivAt_firstWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.firstWeight A u σ) (S.secondWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul (S.hasDerivAt_twistEnergy A 1 t σ)).congr_deriv
    (by unfold firstWeight secondWeight; ring)

theorem hasDerivAt_twistZ (S : SpinSystem V E)
    (A : E → SpinOperator 4) (t : ℝ) :
    HasDerivAt (fun u => S.Z (fun e => NormedSpace.exp (u • A e)))
      (∫ σ, S.firstWeight A t σ ∂S.reference) t := by
  simpa only [twistEnergy_zero, Z] using
    hasDerivAt_integral_compact S.reference
      (fun u σ => Real.exp (S.twistEnergy A 0 u σ)) (S.firstWeight A)
      (S.continuous_twistEnergy A 0).rexp (S.continuous_firstWeight A)
      (S.hasDerivAt_weight A) t

theorem hasDerivAt_firstVariation (S : SpinSystem V E)
    (A : E → SpinOperator 4) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.firstWeight A u σ ∂S.reference)
      (∫ σ, S.secondWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.firstWeight A) (S.secondWeight A)
    (S.continuous_firstWeight A) (S.continuous_secondWeight A)
    (S.hasDerivAt_firstWeight A) t

def thirdWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 3 t σ + 3 * S.twistEnergy A 1 t σ * S.twistEnergy A 2 t σ +
      (S.twistEnergy A 1 t σ)^3)

def fourthWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) : ℝ :=
  Real.exp (S.twistEnergy A 0 t σ) *
    (S.twistEnergy A 4 t σ + 4 * S.twistEnergy A 1 t σ * S.twistEnergy A 3 t σ +
      3 * (S.twistEnergy A 2 t σ)^2 +
      6 * (S.twistEnergy A 1 t σ)^2 * S.twistEnergy A 2 t σ +
      (S.twistEnergy A 1 t σ)^4)

omit [Fintype V] in
theorem continuous_thirdWeight (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (Function.uncurry (S.thirdWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    (((S.continuous_twistEnergy A 3).add
      (((S.continuous_twistEnergy A 1).const_mul 3).mul
        (S.continuous_twistEnergy A 2))).add ((S.continuous_twistEnergy A 1).pow 3))

omit [Fintype V] in
theorem continuous_fourthWeight (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (Function.uncurry (S.fourthWeight A)) := by
  exact (S.continuous_twistEnergy A 0).rexp.mul
    (((((S.continuous_twistEnergy A 4).add
      (((S.continuous_twistEnergy A 1).const_mul 4).mul
        (S.continuous_twistEnergy A 3))).add
      (((S.continuous_twistEnergy A 2).pow 2).const_mul 3)).add
      ((((S.continuous_twistEnergy A 1).pow 2).const_mul 6).mul
        (S.continuous_twistEnergy A 2))).add ((S.continuous_twistEnergy A 1).pow 4))

omit [Fintype V] in
theorem hasDerivAt_secondWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.secondWeight A u σ) (S.thirdWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul
    ((S.hasDerivAt_twistEnergy A 2 t σ).add
      ((S.hasDerivAt_twistEnergy A 1 t σ).pow 2))).congr_deriv
    (by dsimp [firstWeight, thirdWeight]; ring)

omit [Fintype V] in
theorem hasDerivAt_thirdWeight (S : SpinSystem V E) (A : E → SpinOperator 4)
    (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.thirdWeight A u σ) (S.fourthWeight A t σ) t := by
  exact ((S.hasDerivAt_weight A t σ).mul
    (((S.hasDerivAt_twistEnergy A 3 t σ).add
      (((S.hasDerivAt_twistEnergy A 1 t σ).const_mul 3).mul
        (S.hasDerivAt_twistEnergy A 2 t σ))).add
      ((S.hasDerivAt_twistEnergy A 1 t σ).pow 3))).congr_deriv
    (by dsimp [firstWeight, fourthWeight]; ring)

theorem hasDerivAt_secondVariation (S : SpinSystem V E)
    (A : E → SpinOperator 4) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.secondWeight A u σ ∂S.reference)
      (∫ σ, S.thirdWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.secondWeight A) (S.thirdWeight A)
    (S.continuous_secondWeight A) (S.continuous_thirdWeight A)
    (S.hasDerivAt_secondWeight A) t

theorem hasDerivAt_thirdVariation (S : SpinSystem V E)
    (A : E → SpinOperator 4) (t : ℝ) :
    HasDerivAt (fun u => ∫ σ, S.thirdWeight A u σ ∂S.reference)
      (∫ σ, S.fourthWeight A t σ ∂S.reference) t :=
  hasDerivAt_integral_compact S.reference (S.thirdWeight A) (S.fourthWeight A)
    (S.continuous_thirdWeight A) (S.continuous_fourthWeight A)
    (S.hasDerivAt_thirdWeight A) t

omit [Fintype V] [Fintype E] in

theorem exp_smul_add (g : SpinOperator 4) (r s : ℝ) :
    NormedSpace.exp ((r+s) • g) = NormedSpace.exp (r • g) * NormedSpace.exp (s • g) := by
  rw [add_smul r s g]
  apply NormedSpace.exp_add_of_commute
  change (r • g) * (s • g) = (s • g) * (r • g)
  rw [Algebra.smul_mul_assoc r g (s • g), Algebra.mul_smul_comm s g g,
    smul_smul r s (g*g), Algebra.smul_mul_assoc s g (r • g),
    Algebra.mul_smul_comm r g g, smul_smul s r (g*g), mul_comm r s]

theorem W_add_gradient (S : SpinSystem V E) (g : SpinOperator 4)
    (hg : g ∈ skewAdjoint (SpinOperator 4)) (h : E → ℝ) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.W (fun e => (h e + f (S.right e) - f (S.left e)) • g) =
      S.W (fun e => h e • g) := by
  let U := fun x => rotationExp (-(f x • g)) ((skewAdjoint _).neg_mem (skewAdjoint.smul_mem _ hg))
  have hfix : ∀ x s, S.pin x = some s → spinRotation (U x) s = s := by
    intro x s hs
    apply Subtype.ext
    change NormedSpace.exp (-(f x • g)) s.val = s.val
    rw [hP x s hs, zero_smul ℝ g, neg_zero, NormedSpace.exp_zero]
    rfl
  have hK : S.gauge
      (fun e => NormedSpace.exp ((h e + f (S.right e) - f (S.left e)) • g)) U =
      (fun e => NormedSpace.exp (h e • g)) := by
    funext e
    apply ContinuousLinearMap.ext
    intro v
    change (U (S.left e)).symm
      (NormedSpace.exp ((h e + f (S.right e) - f (S.left e)) • g)
        (U (S.right e) v)) = _
    simp only [U, rotationExp_symm_apply, rotationExp_apply, neg_neg]
    rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, ← neg_smul (f (S.right e)) g,
      ← exp_smul_add,
      ← exp_smul_add]
    have hc : f (S.left e) + (h e + f (S.right e) - f (S.left e)) + -f (S.right e) =
        h e := by ring
    rw [hc]
  unfold W
  congr 1
  rw [← hK]
  exact (S.Z_gauge_of_fixes_pins _ U hfix).symm

theorem W_gradient (S : SpinSystem V E) (g : SpinOperator 4)
    (hg : g ∈ skewAdjoint (SpinOperator 4)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.W (fun e => (f (S.right e) - f (S.left e)) • g) = 1 := by
  have h := S.W_add_gradient g hg 0 f hP
  simp only [Pi.zero_apply, zero_add, zero_smul ℝ g] at h
  exact h.trans (S.W_zero)

def average (S : SpinSystem V E) (f : (V → RP3.Spin) → ℝ) : ℝ :=
  (∫ σ, f σ * Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) / S.Z (fun _ => 1)

theorem integrable_average_integrand (S : SpinSystem V E)
    {f : (V → RP3.Spin) → ℝ} (hf : Continuous f) :
    Integrable (fun σ => f σ * Real.exp (S.energy (fun _ => 1) σ)) S.reference :=
  (hf.mul (S.continuous_energy _).rexp).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[simp] theorem average_const (S : SpinSystem V E) (c : ℝ) :
    S.average (fun _ => c) = c := by
  unfold average
  rw [integral_const_mul]
  change c * S.Z (fun _ => 1) / S.Z (fun _ => 1) = c
  exact mul_div_cancel_right₀ c (S.Z_pos _).ne'

theorem average_add (S : SpinSystem V E)
    {f g : (V → RP3.Spin) → ℝ} (hf : Continuous f) (hg : Continuous g) :
    S.average (f+g) = S.average f + S.average g := by
  unfold average
  simp only [Pi.add_apply, add_mul]
  rw [integral_add (S.integrable_average_integrand hf)
    (S.integrable_average_integrand hg), add_div]

theorem average_mono (S : SpinSystem V E)
    {f g : (V → RP3.Spin) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ σ, f σ ≤ g σ) : S.average f ≤ S.average g := by
  apply div_le_div_of_nonneg_right _ (S.Z_pos _).le
  apply integral_mono (S.integrable_average_integrand hf) (S.integrable_average_integrand hg)
  intro σ
  exact mul_le_mul_of_nonneg_right (hfg σ) (Real.exp_pos _).le

theorem average_nonneg (S : SpinSystem V E)
    {f : (V → RP3.Spin) → ℝ} (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ S.average f :=
  div_nonneg (integral_nonneg fun σ => mul_nonneg (hf σ) (Real.exp_pos _).le) (S.Z_pos _).le

omit [Fintype V] [Fintype E] in

def axisGradient (S : SpinSystem V E) (f : V → ℝ) (g : SpinOperator 4) : E → SpinOperator 4 :=
  fun e => (f (S.right e) - f (S.left e)) • g

theorem Z_gradient_line (S : SpinSystem V E) (g : SpinOperator 4)
    (hg : g ∈ skewAdjoint (SpinOperator 4)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) (t : ℝ) :
    S.Z (fun e => NormedSpace.exp (t • S.axisGradient f g e)) = S.Z (fun _ => 1) := by
  have hp : ∀ x s, S.pin x = some s → t * f x = 0 := by
    intro x s hs
    rw [hP x s hs, mul_zero]
  have h := S.W_gradient g hg (fun x => t * f x) hp
  unfold W at h
  have ha : (fun e => (t * f (S.right e) - t * f (S.left e)) • g) =
      (fun e => t • S.axisGradient f g e) := by
    funext e
    simp only [axisGradient, smul_smul, mul_sub]
  rw [ha] at h
  exact (div_eq_one_iff_eq (S.Z_pos _).ne').mp h


end SpinSystem
end
end RP3.Quadratic
