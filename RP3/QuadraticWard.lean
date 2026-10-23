import RP3.QuadraticDerivatives

/-!
# Second and fourth Ward identities for the quadratic interaction

The change-of-variables and fourth-derivative proof pattern is adapted from
OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
All energy derivatives refer to the squared interaction in QuadraticGibbs.
-/
namespace RP3.Quadratic
noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

theorem second_gradient_identity (S : SpinSystem V E) (g : SpinOperator 4)
    (hg : g ∈ skewAdjoint (SpinOperator 4)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => S.secondEnergy (S.axisGradient f g) σ +
      (S.firstEnergy (S.axisGradient f g) σ)^2) = 0 := by
  let A := S.axisGradient f g
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun _ : ℝ => S.Z (fun _ => 1)) := funext (S.Z_gradient_line g hg f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (hasDerivAt_const t _)
  have hsecond : (∫ σ, S.secondWeight A 0 σ ∂S.reference) = 0 := by
    have h := S.hasDerivAt_firstVariation A 0
    rw [hfirst] at h
    exact h.unique (hasDerivAt_const 0 0)
  unfold average
  have hfun : (fun σ => (S.secondEnergy A σ + (S.firstEnergy A σ)^2) *
      Real.exp (S.energy (fun _ => 1) σ)) = (fun σ => S.secondWeight A 0 σ) := by
    funext σ
    have hz (e : E) : (0 : ℝ) • A e = 0 := zero_smul ℝ (A e)
    simp only [secondWeight, twistEnergy_zero, twistEnergy_one_at_zero,
      twistEnergy_two_at_zero, hz, NormedSpace.exp_zero]
    exact mul_comm (S.secondEnergy A σ + S.firstEnergy A σ ^ 2) (Real.exp (S.energy (fun _ => 1) σ))
  change (∫ σ, (S.secondEnergy A σ + (S.firstEnergy A σ)^2) *
    Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) / S.Z (fun _ => 1) = 0
  rw [hfun, hsecond, zero_div]

def gaugeEnergy (S : SpinSystem V E) (F : V → SpinOperator 4) :
    ℕ → ℝ → (V → RP3.Spin) → ℝ :=
  S.pathEnergy (fun e k => tripleJet (F (S.left e))
    (F (S.right e) - F (S.left e)) (-F (S.right e)) k 0 0 0)

omit [Fintype V] in
theorem continuous_gaugeEnergy (S : SpinSystem V E) (F : V → SpinOperator 4) (k : ℕ) :
    Continuous (Function.uncurry (S.gaugeEnergy F k)) :=
  S.continuous_pathEnergy _ (fun _ k => continuous_tripleJet _ _ _ k 0 0 0) k

omit [Fintype V] in
set_option maxHeartbeats 800000 in
theorem hasDerivAt_gaugeEnergy (S : SpinSystem V E) (F : V → SpinOperator 4)
    (k : ℕ) (t : ℝ) (σ : V → RP3.Spin) :
    HasDerivAt (fun u => S.gaugeEnergy F k u σ) (S.gaugeEnergy F (k+1) t σ) t :=
  S.hasDerivAt_pathEnergy _ (fun e k t => hasDerivAt_tripleJet
    (F (S.left e)) (F (S.right e) - F (S.left e)) (-F (S.right e)) k 0 0 0 t) k t σ

omit [Fintype V] in
theorem gaugeEnergy_at_zero (S : SpinSystem V E) (F : V → SpinOperator 4)
    (σ : V → RP3.Spin) :
    S.gaugeEnergy F 0 0 σ = S.energy (fun _ => 1) σ ∧
    S.gaugeEnergy F 1 0 σ = 0 ∧
    S.gaugeEnergy F 2 0 σ = S.firstEnergy
      (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ := by
  have h0 := fun e => (gaugeJets_zero_one (F (S.left e)) (F (S.right e))).1
  have h1 := fun e => (gaugeJets_zero_one (F (S.left e)) (F (S.right e))).2
  constructor
  · simp only [gaugeEnergy, pathEnergy, productJet, innerJet, h0, energy, pow_two]
  constructor
  · simp [gaugeEnergy, pathEnergy, squareJet_one, innerJet, h1]
  · unfold gaugeEnergy pathEnergy firstEnergy
    apply Finset.sum_congr rfl
    intro e _
    simp only [squareJet_two, innerJet, h0, h1, gaugeJet_two]
    simp only [zero_apply, inner_zero_right, one_apply_eq_self, zero_pow (by decide : 2 ≠ 0),
      zero_add]
    ring

theorem fourth_noncommuting_identity (S : SpinSystem V E)
    (F : V → SpinOperator 4) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator 4))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    (∫ σ, S.fourthWeight (fun e => F (S.right e)-F (S.left e)) 0 σ ∂S.reference) =
      ∫ σ, Real.exp (S.energy (fun _ => 1) σ) *
        (S.gaugeEnergy F 4 0 σ + 3 * (S.firstEnergy
          (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ)^2)
        ∂S.reference := by
  let A : E → SpinOperator 4 := fun e => F (S.right e)-F (S.left e)
  have heq : (fun t => ∫ σ, Real.exp (S.twistEnergy A 0 t σ) ∂S.reference) =
      (fun t => ∫ σ, Real.exp (S.gaugeEnergy F 0 t σ) ∂S.reference) := by
    funext t
    have htP : ∀ x s, S.pin x = some s → t • F x = 0 := by
      intro x s hs
      rw [hP x s hs]
      exact smul_zero (M := ℝ) (A := SpinOperator 4) t
    have h := S.noncommuting_gauge (fun x => t • F x)
      (fun x => skewAdjoint.smul_mem t (hF x)) htP
    have hd (e : E) : t • F (S.right e) - t • F (S.left e) = t • A e :=
      (smul_sub t (F (S.right e)) (F (S.left e))).symm
    have hGP : S.gaugeProduct (fun x => t • F x) =
        (fun e => tripleJet (F (S.left e)) (F (S.right e)-F (S.left e))
          (-F (S.right e)) 0 0 0 0 t) := by
      funext e
      change NormedSpace.exp (t • F (S.left e)) *
        NormedSpace.exp (t • F (S.right e) - t • F (S.left e)) *
        NormedSpace.exp (-(t • F (S.right e))) = _
      rw [hd]
      simp only [tripleJet, expPower, pow_zero, mul_one]
      rw [smul_neg t (F (S.right e))]
    rw [hGP] at h
    simpa only [Z, twistEnergy_zero, gaugeEnergy, pathEnergy, productJet, innerJet, energy, pow_two, hd] using h
  have hl := iteratedDeriv_four_integral_exp S.reference (S.twistEnergy A)
    (S.continuous_twistEnergy A) (S.hasDerivAt_twistEnergy A) 0
  have hr := iteratedDeriv_four_integral_exp S.reference (S.gaugeEnergy F)
    (S.continuous_gaugeEnergy F) (S.hasDerivAt_gaugeEnergy F) 0
  rw [heq, hr] at hl
  refine hl.symm.trans (integral_congr_ae (Filter.Eventually.of_forall ?_))
  intro σ
  have hz := S.gaugeEnergy_at_zero F σ
  simp [fourthBell, hz.1, hz.2.1, hz.2.2]


end SpinSystem
end
end RP3.Quadratic
