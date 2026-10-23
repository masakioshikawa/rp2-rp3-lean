import RP2.QuadraticWard

/-!
# The noncommuting two-axis identity for RP²

This derives the diagonal fourth-order Ward identity from the *quadratic*
Gibbs weight. In particular, the additional square of the second derivative
in the squared edge interaction is retained.
The response/gauge proof pattern and matrix identity are adapted from
OpenAI's ClassicalON development (Apache-2.0); see NOTICE.
-/
namespace RP2.Quadratic
noncomputable section
open MeasureTheory
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

theorem average_mul_const (S : SpinSystem V E) (r : ℝ) (f : (V → RP2.Spin) → ℝ) :
    S.average (fun σ => r * f σ) = r * S.average f := by
  simp only [average, mul_assoc, integral_const_mul, mul_div_assoc]

def fourthPolynomial (F : ℕ → ℝ) : ℝ :=
  F 4 + 4 * F 1 * F 3 + 3 * (F 2)^2 + 6 * (F 1)^2 * F 2 + (F 1)^4

def fourthResponse (S : SpinSystem V E) (A : E → SpinOperator 3) : ℝ :=
  S.average (fun σ => fourthPolynomial (fun k => S.twistEnergy A k 0 σ))

theorem fourthResponse_integral (S : SpinSystem V E) (A : E → SpinOperator 3) :
    S.fourthResponse A = (∫ σ, S.fourthWeight A 0 σ ∂S.reference) / S.Z (fun _ => 1) := by
  unfold fourthResponse average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  have hz : S.twistEnergy A 0 0 σ = S.energy (fun _ => 1) σ := by
    rw [twistEnergy_zero]
    congr 1
    funext e
    rw [zero_smul ℝ (A e), NormedSpace.exp_zero]
  simp only [fourthWeight, fourthPolynomial, hz]
  ring

theorem fourthResponse_gauge (S : SpinSystem V E)
    (F : V → SpinOperator 3) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator 3))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    S.fourthResponse (fun e => F (S.right e)-F (S.left e)) =
      S.average (fun σ => S.gaugeEnergy F 4 0 σ + 3 * (S.firstEnergy
        (fun e => F (S.left e)*F (S.right e)-F (S.right e)*F (S.left e)) σ)^2) := by
  rw [S.fourthResponse_integral, S.fourth_noncommuting_identity F hF hP]
  unfold average
  congr 1
  apply integral_congr_ae (Filter.Eventually.of_forall _)
  intro σ
  exact mul_comm _ _

omit [Fintype V] [Fintype E] in
def crossForm (S : SpinSystem V E) (f g : V → ℝ) : E → ℝ :=
  fun e => f (S.left e)*g (S.right e)-g (S.left e)*f (S.right e)

omit [Fintype V] [Fintype E] in
def planarGradient (S : SpinSystem V E) (f g : V → ℝ) : E → SpinOperator 3 :=
  fun e => planeOperator (f (S.right e)) (g (S.right e)) -
    planeOperator (f (S.left e)) (g (S.left e))

def secondAxisEnergy (S : SpinSystem V E) (h k : E → ℝ) (σ : V → RP2.Spin) : ℝ :=
  ∑ e, 2 * S.strength e * (h e * k e) *
    (⟪(σ (S.left e)).val, axisC (σ (S.right e)).val⟫_ℝ ^ 2 +
      ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
        ⟪(σ (S.left e)).val, (axisC ^ 2) (σ (S.right e)).val⟫_ℝ)

def secondAxisResponse (S : SpinSystem V E) (h k : E → ℝ) : ℝ :=
  S.average (fun σ => S.secondAxisEnergy h k σ +
    S.firstEnergy (fun e => h e • axisC) σ * S.firstEnergy (fun e => k e • axisC) σ)

omit [Fintype V] in
theorem firstEnergy_neg (S : SpinSystem V E) (A : E → SpinOperator 3) (σ : V → RP2.Spin) :
    S.firstEnergy (-A) σ = -S.firstEnergy A σ := by
  simp [firstEnergy]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
omit [Fintype V] in
/-- The product-rule terms combine into six times the actual second response. -/
theorem gaugeEnergy_plane_four_even (S : SpinSystem V E) (f g : V → ℝ)
    (σ : V → RP2.Spin) :
    S.gaugeEnergy (fun x => planeOperator (f x) (g x)) 4 0 σ +
      S.gaugeEnergy (fun x => planeOperator (f x) (-g x)) 4 0 σ =
        6 * S.secondAxisEnergy (S.crossForm f g) (S.crossForm f g) σ := by
  unfold gaugeEnergy pathEnergy secondAxisEnergy
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  let u := (σ (S.left e)).val
  let v := (σ (S.right e)).val
  let a := f (S.left e)
  let b := g (S.left e)
  let c := f (S.right e)
  let d := g (S.right e)
  let jp := fun k => tripleJet (planeOperator a b)
    (planeOperator c d-planeOperator a b) (-planeOperator c d) k 0 0 0 0
  let jm := fun k => tripleJet (planeOperator a (-b))
    (planeOperator c (-d)-planeOperator a (-b)) (-planeOperator c (-d)) k 0 0 0 0
  have hp0 : jp 0 = 1 := (gaugeJets_zero_one _ _).1
  have hm0 : jm 0 = 1 := (gaugeJets_zero_one _ _).1
  have hp1 : jp 1 = 0 := (gaugeJets_zero_one _ _).2
  have hm1 : jm 1 = 0 := (gaugeJets_zero_one _ _).2
  have hp2 : jp 2 = (a*d-b*c) • axisC := by
    exact (gaugeJet_two _ _).trans (planeOperator_commutator a b c d)
  have hm2 : jm 2 = -(a*d-b*c) • axisC := by
    change tripleJet _ _ _ 2 0 0 0 0 = _
    rw [gaugeJet_two, planeOperator_commutator]
    congr 1
    ring
  have h4 : jp 4 + jm 4 = (6*(a*d-b*c)^2) • axisC^2 :=
    gaugeJet_plane_four_even a b c d
  have h4i := congrArg (fun M : SpinOperator 3 => ⟪u, M v⟫_ℝ) h4
  simp only [add_apply, smul_apply, inner_add_right, real_inner_smul_right] at h4i
  simp only [squareJet_four, innerJet]
  change S.strength e * (2 * (3 * ⟪u, jp 2 v⟫_ℝ ^ 2 +
        4 * ⟪u, jp 1 v⟫_ℝ * ⟪u, jp 3 v⟫_ℝ + ⟪u, jp 0 v⟫_ℝ * ⟪u, jp 4 v⟫_ℝ)) +
      S.strength e * (2 * (3 * ⟪u, jm 2 v⟫_ℝ ^ 2 +
        4 * ⟪u, jm 1 v⟫_ℝ * ⟪u, jm 3 v⟫_ℝ + ⟪u, jm 0 v⟫_ℝ * ⟪u, jm 4 v⟫_ℝ)) =
      6 * (2 * S.strength e * ((a*d-b*c) * (a*d-b*c)) *
        (⟪u, axisC v⟫_ℝ ^ 2 + ⟪u, v⟫_ℝ * ⟪u, (axisC^2) v⟫_ℝ))
  rw [hp0, hm0, hp1, hm1, hp2, hm2]
  simp only [one_apply_eq_self, zero_apply, inner_zero_right, mul_zero, zero_mul,
    add_zero, smul_apply, real_inner_smul_right]
  linear_combination 2 * S.strength e * ⟪u, v⟫_ℝ * h4i

end SpinSystem
end
end RP2.Quadratic
