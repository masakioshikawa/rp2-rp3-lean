module

public import RP3.QuadraticSecondResponse

public section

/-!
# Gauge invariance of the RP³ second response

Adapted from OpenAI ClassicalON/SecondGauge.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The partition function and all derivatives are those of the squared RP³ interaction.
-/

namespace RP3.Quadratic

universe uE uV

noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace ComplexConjugate

namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem secondAxisResponse_integral (S : SpinSystem V E) (u : E → ℝ) :
    S.secondAxisResponse u u =
      (∫ σ, S.secondWeight (fun e => u e • axisC) 0 σ ∂S.reference) / S.Z (fun _ => 1) := by
  unfold secondAxisResponse average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  have hE : S.secondEnergy (fun e => u e • axisC) σ = S.secondAxisEnergy u u σ := by
    unfold secondEnergy secondAxisEnergy
    apply Finset.sum_congr rfl
    intro e _
    have hp : (u e • axisC)^2 = (u e*u e) • axisC^2 := by
      rw [pow_two, pow_two, Algebra.smul_mul_assoc (u e) axisC (u e • axisC),
        Algebra.mul_smul_comm (u e) axisC axisC, smul_smul]
    rw [hp]
    simp only [smul_apply, real_inner_smul_right]
    ring
  have hz (e : E) : (0 : ℝ) • (u e • axisC) = 0 := zero_smul ℝ (u e • axisC)
  simp only [secondWeight, S.twistEnergy_zero, hz, NormedSpace.exp_zero,
    S.twistEnergy_one_at_zero, S.twistEnergy_two_at_zero, hE, pow_two]
  ring

theorem Z_axis_add_gradient (S : SpinSystem V E) (u : E → ℝ) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) (t : ℝ) :
    S.Z (fun e => NormedSpace.exp (t • ((u+S.edgeGradient f) e • axisC))) =
      S.Z (fun e => NormedSpace.exp (t • (u e • axisC))) := by
  have hp (x) (s) (hs : S.pin x = some s) : t*f x = 0 := by rw [hP x s hs, mul_zero]
  have h := S.W_add_gradient axisC axisC_skew (fun e => t*u e) (fun x => t*f x) hp
  unfold W at h
  have ha : (fun e => (t*u e + t*f (S.right e) - t*f (S.left e)) • axisC) =
      (fun e => t • ((u+S.edgeGradient f) e • axisC)) := by
    funext e
    simp only [Pi.add_apply, edgeGradient, smul_smul]
    congr 1
    ring
  rw [ha] at h
  simpa only [← smul_smul] using (div_left_inj' (S.Z_pos _).ne').mp h

theorem secondAxisResponse_gradient_diag (S : SpinSystem V E) (u : E → ℝ)
    (f : V → ℝ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.secondAxisResponse (u+S.edgeGradient f) (u+S.edgeGradient f) =
      S.secondAxisResponse u u := by
  let A : E → SpinOperator 4 := fun e => (u+S.edgeGradient f) e • axisC
  let B : E → SpinOperator 4 := fun e => u e • axisC
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun t => S.Z (fun e => NormedSpace.exp (t • B e))) :=
    funext (S.Z_axis_add_gradient u f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) =
      (fun t => ∫ σ, S.firstWeight B t σ ∂S.reference) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (S.hasDerivAt_twistZ B t)
  have hsecond : (∫ σ, S.secondWeight A 0 σ ∂S.reference) =
      (∫ σ, S.secondWeight B 0 σ ∂S.reference) := by
    have h := S.hasDerivAt_firstVariation A 0
    rw [hfirst] at h
    exact h.unique (S.hasDerivAt_firstVariation B 0)
  rw [S.secondAxisResponse_integral, S.secondAxisResponse_integral]
  exact congrArg (fun q => q / S.Z (fun _ => 1)) hsecond

theorem secondAxisResponse_gradient_right (S : SpinSystem V E) (u : E → ℝ)
    (f : V → ℝ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.secondAxisResponse u (S.edgeGradient f) = 0 := by
  have h := S.secondAxisResponse_gradient_diag u f hP
  have hz := S.secondAxisResponse_gradient_diag 0 f hP
  have he (v : E → ℝ) : S.secondAxisResponse 0 v = 0 := by
    unfold secondAxisResponse
    have h0 : (fun σ => S.secondAxisEnergy 0 v σ +
        S.firstEnergy (fun e => (0 : E → ℝ) e • axisC) σ *
          S.firstEnergy (fun e => v e • axisC) σ) = (fun _ => 0) := by
      funext σ
      simp [secondAxisEnergy, firstEnergy]
    rw [h0, S.average_const]
  simp only [zero_add, he] at hz
  rw [S.secondAxisResponse_add_left, S.secondAxisResponse_add_right,
    S.secondAxisResponse_add_right, S.secondAxisResponse_symm (S.edgeGradient f), hz] at h
  linarith

omit [Fintype V] [Fintype E] in
theorem edgeGradient_add_complex (S : SpinSystem V E) (f g : V → ℂ) :
    S.edgeGradient (f+g) = S.edgeGradient f + S.edgeGradient g := by
  ext e
  simp only [edgeGradient, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem edgeGradient_smul_complex (S : SpinSystem V E) (r : ℂ) (f : V → ℂ) :
    S.edgeGradient (r • f) = r • S.edgeGradient f := by
  ext e
  simp only [edgeGradient, Pi.smul_apply, smul_eq_mul, mul_sub]

theorem complexSecondResponse_gradient_right (S : SpinSystem V E) (u : E → ℂ)
    (f : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.complexSecondResponse u (S.edgeGradient f) = 0 := by
  apply complex_linear_zero_of_real (fun _ : E => False)
    (fun u => S.complexSecondResponse u (S.edgeGradient f))
    (fun u v => S.complexSecondResponse_add_left u v _)
    (fun r u => S.complexSecondResponse_smul_left u _ r) ?_ u (fun _ h => h.elim)
  intro a _
  apply complex_linear_zero_of_real (fun x => ∃ s, S.pin x = some s)
    (fun f => S.complexSecondResponse (fun e => (a e : ℂ)) (S.edgeGradient f)) ?_ ?_ ?_ f ?_
  · intro f g
    rw [S.edgeGradient_add_complex, S.complexSecondResponse_add_right]
  · intro r f
    rw [S.edgeGradient_smul_complex, S.complexSecondResponse_smul_right]
  · intro b hb
    rw [S.edgeGradient_ofReal, S.complexSecondResponse_ofReal,
      S.secondAxisResponse_gradient_right a b (fun x s hs => hb x ⟨s,hs⟩),
      Complex.ofReal_zero]
  · intro x hx
    obtain ⟨s, hs⟩ := hx
    exact hP x s hs

theorem complexSecondResponse_add_gradient_right (S : SpinSystem V E) (u v : E → ℂ)
    (f : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.complexSecondResponse u (v+S.edgeGradient f) = S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_add_right, S.complexSecondResponse_gradient_right u f hP, add_zero]

theorem complexSecondResponse_add_gradients (S : SpinSystem V E) (u v : E → ℂ)
    (f g : V → ℂ) (hP : ∀ x s, S.pin x = some s → f x = 0)
    (hQ : ∀ x s, S.pin x = some s → g x = 0) :
    S.complexSecondResponse (u+S.edgeGradient f) (v+S.edgeGradient g) =
      S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_add_gradient_right _ v g hQ,
    S.complexSecondResponse_symm, S.complexSecondResponse_add_gradient_right _ u f hP,
    S.complexSecondResponse_symm]

end SpinSystem

end

end RP3.Quadratic
