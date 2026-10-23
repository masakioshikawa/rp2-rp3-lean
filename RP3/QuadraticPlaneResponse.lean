module

public import RP3.QuadraticPlane
public import RP3.QuadraticBounds

public section

/-!
# The normalized two-axis Ward identity for RP³

Adapted from OpenAI's ClassicalON/RotationWork.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The first and second responses are replaced by their proved quadratic
counterparts; the squared-interaction fourth-order identity supplies the
model-specific step.
-/
namespace RP3.Quadratic
noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace
namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

theorem fourthResponse_plane_even (S : SpinSystem V E) (f g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    S.fourthResponse (S.planarGradient f g) +
      S.fourthResponse (S.planarGradient f (-g)) =
        6 * S.secondAxisResponse (S.crossForm f g) (S.crossForm f g) := by
  have hsk (f g : V → ℝ) (x : V) :
      planeOperator (f x) (g x) ∈ skewAdjoint (SpinOperator 4) := by
    rw [planeOperator_eq]
    exact (skewAdjoint _).add_mem (skewAdjoint.smul_mem _ axisA_skew)
      (skewAdjoint.smul_mem _ axisB_skew)
  have hp : ∀ x s, S.pin x = some s → planeOperator (f x) (g x) = 0 := by
    intro x s hs
    rw [hf x s hs, hg x s hs, planeOperator_eq]
    simp only [zero_smul ℝ axisA, zero_smul ℝ axisB, add_zero]
  have hm : ∀ x s, S.pin x = some s → planeOperator (f x) ((-g) x) = 0 := by
    intro x s hs
    rw [Pi.neg_apply, hg x s hs, neg_zero, hf x s hs, planeOperator_eq]
    simp only [zero_smul ℝ axisA, zero_smul ℝ axisB, add_zero]
  change S.fourthResponse (fun e => planeOperator (f (S.right e)) (g (S.right e)) -
    planeOperator (f (S.left e)) (g (S.left e))) + S.fourthResponse (fun e =>
      planeOperator (f (S.right e)) ((-g) (S.right e)) -
      planeOperator (f (S.left e)) ((-g) (S.left e))) = _
  rw [S.fourthResponse_gauge _ (hsk f g) hp,
    S.fourthResponse_gauge _ (hsk f (-g)) hm]
  let w := S.crossForm f g
  have he (σ : V → RP3.Spin) :
      S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
      S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ =
        6 * S.secondAxisEnergy w w σ :=
    S.gaugeEnergy_plane_four_even f g σ
  have hcm : (fun e =>
      planeOperator (f (S.left e)) ((-g) (S.left e)) *
        planeOperator (f (S.right e)) ((-g) (S.right e)) -
      planeOperator (f (S.right e)) ((-g) (S.right e)) *
        planeOperator (f (S.left e)) ((-g) (S.left e))) = -(fun e => w e • axisC) := by
    funext e
    rw [planeOperator_commutator]
    change (f (S.left e) * (-g) (S.right e) - (-g) (S.left e) * f (S.right e)) • axisC = -(w e • axisC)
    rw [← neg_smul (w e) axisC]
    congr 1
    dsimp only [w, crossForm, Pi.neg_apply]
    ring
  have hcp : (fun e =>
      planeOperator (f (S.left e)) (g (S.left e)) *
        planeOperator (f (S.right e)) (g (S.right e)) -
      planeOperator (f (S.right e)) (g (S.right e)) *
        planeOperator (f (S.left e)) (g (S.left e))) = (fun e => w e • axisC) := by
    funext e
    exact planeOperator_commutator _ _ _ _
  rw [hcp, hcm]
  simp only [S.firstEnergy_neg, neg_sq]
  have hc (F : V → SpinOperator 4) : Continuous (fun σ =>
      S.gaugeEnergy F 4 0 σ + 3 * (S.firstEnergy (fun e => w e • axisC) σ)^2) :=
    ((S.continuous_gaugeEnergy F 4).comp (continuous_const.prodMk continuous_id)).add
      (continuous_const.mul ((S.continuous_firstEnergy _).pow 2))
  rw [← S.average_add (hc _) (hc _)]
  have hpoint : (fun σ =>
      (S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
        3 * (S.firstEnergy (fun e => w e • axisC) σ)^2) +
      (S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ +
        3 * (S.firstEnergy (fun e => w e • axisC) σ)^2)) =
      (fun σ => 6 * (S.secondAxisEnergy w w σ +
        S.firstEnergy (fun e => w e • axisC) σ * S.firstEnergy (fun e => w e • axisC) σ)) := by
    funext σ
    have ht := he σ
    linarith
  change S.average (fun σ =>
      (S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
        3 * (S.firstEnergy (fun e => w e • axisC) σ)^2) +
      (S.gaugeEnergy (fun x => planeOperator (f x) ((-g) x)) 4 0 σ +
        3 * (S.firstEnergy (fun e => w e • axisC) σ)^2)) = _
  rw [hpoint, S.average_mul_const]
  rfl


theorem fourthResponse_axisGradient (S : SpinSystem V E)
    (g : SpinOperator 4) (hg : g ∈ skewAdjoint (SpinOperator 4)) (f : V → ℝ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.fourthResponse (S.axisGradient f g) = 0 := by
  let A := S.axisGradient f g
  have hZ : (fun t => S.Z (fun e => NormedSpace.exp (t • A e))) =
      (fun _ : ℝ => S.Z (fun _ => 1)) := funext (S.Z_gradient_line g hg f hP)
  have hfirst : (fun t => ∫ σ, S.firstWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_twistZ A t
    rw [hZ] at h
    exact h.unique (hasDerivAt_const t _)
  have hsecond : (fun t => ∫ σ, S.secondWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_firstVariation A t
    rw [hfirst] at h
    exact h.unique (hasDerivAt_const t 0)
  have hthird : (fun t => ∫ σ, S.thirdWeight A t σ ∂S.reference) = (fun _ : ℝ => 0) := by
    funext t
    have h := S.hasDerivAt_secondVariation A t
    rw [hsecond] at h
    exact h.unique (hasDerivAt_const t 0)
  have hfourth : (∫ σ, S.fourthWeight A 0 σ ∂S.reference) = 0 := by
    have h := S.hasDerivAt_thirdVariation A 0
    rw [hthird] at h
    exact h.unique (hasDerivAt_const 0 0)
  rw [S.fourthResponse_integral, hfourth, zero_div]

end SpinSystem
end
end RP3.Quadratic
