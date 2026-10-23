module

public import RP3.QuadraticAverages
public import RP3.MixedAlgebra

public section

/-!
# Mixed fourth derivatives of the squared interaction

All local coefficients below are obtained by differentiating the actual
squared scalar product. The terms quadratic in lower scalar-product jets
are retained at every order.
-/
namespace RP3.Quadratic
noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
@[expose] def localInner (S : SpinSystem V E) (M : SpinOperator 4)
    (σ : V → RP3.Spin) (e : E) : ℝ :=
  ⟪(σ (S.left e)).val, M (σ (S.right e)).val⟫_ℝ

omit [Fintype V] [Fintype E] in
@[expose] def axisCoefficient (S : SpinSystem V E) (M : SpinOperator 4)
    (k : ℕ) (σ : V → RP3.Spin) (e : E) : ℝ :=
  S.strength e * productJet
    (fun n (_ : ℝ) (_ : Unit) => S.localInner (M^n) σ e)
    (fun n (_ : ℝ) (_ : Unit) => S.localInner (M^n) σ e) k 0 0 0 ()

omit [Fintype V] [Fintype E] in
@[expose] def mixedCoefficients (S : SpinSystem V E) (σ : V → RP3.Spin) :
    MixedAlgebra.Coeffs E ℝ where
  a e := 2 * S.strength e * S.localInner 1 σ e * S.localInner axisA σ e
  b e := 2 * S.strength e * S.localInner 1 σ e * S.localInner axisB σ e
  aa e := 2 * S.strength e * ((S.localInner axisA σ e)^2 +
    S.localInner 1 σ e * S.localInner (axisA^2) σ e)
  ab e := 2 * S.strength e * (S.localInner axisA σ e * S.localInner axisB σ e +
    S.localInner 1 σ e * S.localInner mixedAB σ e)
  bb e := 2 * S.strength e * ((S.localInner axisB σ e)^2 +
    S.localInner 1 σ e * S.localInner (axisB^2) σ e)
  aab e := 2 * S.strength e * (S.localInner axisB σ e * S.localInner (axisA^2) σ e +
    2 * S.localInner axisA σ e * S.localInner mixedAB σ e +
    S.localInner 1 σ e * S.localInner mixedAAB σ e)
  abb e := 2 * S.strength e * (S.localInner axisA σ e * S.localInner (axisB^2) σ e +
    2 * S.localInner axisB σ e * S.localInner mixedAB σ e +
    S.localInner 1 σ e * S.localInner mixedABB σ e)
  aabb e := 2 * S.strength e * (S.localInner (axisA^2) σ e * S.localInner (axisB^2) σ e +
    2 * (S.localInner mixedAB σ e)^2 +
    2 * S.localInner axisA σ e * S.localInner mixedABB σ e +
    2 * S.localInner axisB σ e * S.localInner mixedAAB σ e +
    S.localInner 1 σ e * S.localInner mixedAABB σ e)

omit [Fintype V] in
theorem weighted_mixed_a (S : SpinSystem V E) (u : E → ℝ) (σ : V → RP3.Spin) :
    MixedAlgebra.weighted (S.mixedCoefficients σ).a u =
      S.firstEnergy (fun e => u e • axisA) σ := by
  unfold MixedAlgebra.weighted firstEnergy
  apply Finset.sum_congr rfl
  intro e _
  simp only [mixedCoefficients, localInner, one_apply_eq_self, smul_apply,
    real_inner_smul_right]
  ring

omit [Fintype V] in
theorem weighted_mixed_b (S : SpinSystem V E) (u : E → ℝ) (σ : V → RP3.Spin) :
    MixedAlgebra.weighted (S.mixedCoefficients σ).b u =
      S.firstEnergy (fun e => u e • axisB) σ := by
  unfold MixedAlgebra.weighted firstEnergy
  apply Finset.sum_congr rfl
  intro e _
  simp only [mixedCoefficients, localInner, one_apply_eq_self, smul_apply,
    real_inner_smul_right]
  ring

omit [Fintype V] [Fintype E] in
theorem operator_smul_pow (r : ℝ) (M : SpinOperator 4) (k : ℕ) :
    (r • M)^k = r^k • M^k := by
  induction k with
  | zero => simp only [pow_zero, one_smul]
  | succ k ih =>
    rw [pow_succ, ih, Algebra.smul_mul_assoc (r^k) (M^k) (r • M),
      Algebra.mul_smul_comm r (M^k) M, smul_smul (r^k) r (M^k*M),
      ← pow_succ, ← pow_succ]

omit [Fintype V] in
theorem energy_scaled_power (S : SpinSystem V E) (M : SpinOperator 4)
    (u : E → ℝ) (k : ℕ) (hk : k ≤ 4) (σ : V → RP3.Spin) :
    S.twistEnergy (fun e => u e • M) k 0 σ =
      MixedAlgebra.weighted (S.axisCoefficient M k σ) (u^k) := by
  unfold twistEnergy pathEnergy MixedAlgebra.weighted axisCoefficient
  apply Finset.sum_congr rfl
  intro e _
  interval_cases k <;>
    simp only [productJet, innerJet, expPower_zero, localInner, operator_smul_pow,
      smul_apply, real_inner_smul_right, Pi.pow_apply, pow_zero, pow_one,
      one_apply_eq_self] <;> ring

omit [Fintype V] in
theorem planeEnergy_one (S : SpinSystem V E) (u v : E → ℝ) (σ : V → RP3.Spin) :
    S.twistEnergy (fun e => planeOperator (u e) (v e)) 1 0 σ =
      MixedAlgebra.weighted (S.mixedCoefficients σ).a u +
      MixedAlgebra.weighted (S.mixedCoefficients σ).b v := by
  unfold twistEnergy pathEnergy MixedAlgebra.weighted
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [squareJet_one, innerJet, expPower_zero, pow_zero, pow_one,
    planeOperator_eq, add_apply, smul_apply, inner_add_right, real_inner_smul_right,
    mixedCoefficients, localInner, one_apply_eq_self]
  ring

omit [Fintype V] in
theorem planeEnergy_two (S : SpinSystem V E) (u v : E → ℝ) (σ : V → RP3.Spin) :
    S.twistEnergy (fun e => planeOperator (u e) (v e)) 2 0 σ =
      MixedAlgebra.weighted (S.mixedCoefficients σ).aa (u*u) +
      2 * MixedAlgebra.weighted (S.mixedCoefficients σ).ab (u*v) +
      MixedAlgebra.weighted (S.mixedCoefficients σ).bb (v*v) := by
  unfold twistEnergy pathEnergy MixedAlgebra.weighted
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [squareJet_two, innerJet, expPower_zero, pow_zero, pow_one,
    planeOperator_square]
  simp only [planeOperator_eq, add_apply, smul_apply, inner_add_right,
    real_inner_smul_right, mixedCoefficients, localInner, one_apply_eq_self, Pi.mul_apply]
  ring

omit [Fintype V] in
theorem planeEnergy_three (S : SpinSystem V E) (u v : E → ℝ) (σ : V → RP3.Spin) :
    S.twistEnergy (fun e => planeOperator (u e) (v e)) 3 0 σ =
      MixedAlgebra.weighted (S.axisCoefficient axisA 3 σ) (u^3) +
      3 * MixedAlgebra.weighted (S.mixedCoefficients σ).aab (u*u*v) +
      3 * MixedAlgebra.weighted (S.mixedCoefficients σ).abb (u*v*v) +
      MixedAlgebra.weighted (S.axisCoefficient axisB 3 σ) (v^3) := by
  unfold twistEnergy pathEnergy MixedAlgebra.weighted
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [axisCoefficient, squareJet_three, innerJet, expPower_zero, pow_zero, pow_one,
    planeOperator_cube, planeOperator_square]
  simp only [planeOperator_eq, add_apply, smul_apply,
    inner_add_right, real_inner_smul_right, mixedCoefficients, localInner,
    one_apply_eq_self, Pi.mul_apply, Pi.pow_apply]
  ring

omit [Fintype V] in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem planeEnergy_four_even (S : SpinSystem V E) (u v : E → ℝ) (σ : V → RP3.Spin) :
    S.twistEnergy (fun e => planeOperator (u e) (v e)) 4 0 σ +
      S.twistEnergy (fun e => planeOperator (u e) (-v e)) 4 0 σ =
      2 * MixedAlgebra.weighted (S.axisCoefficient axisA 4 σ) (u^4) +
      12 * MixedAlgebra.weighted (S.mixedCoefficients σ).aabb (u*u*v*v) +
      2 * MixedAlgebra.weighted (S.axisCoefficient axisB 4 σ) (v^4) := by
  unfold twistEnergy pathEnergy MixedAlgebra.weighted
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have h4 := congrArg (fun M : SpinOperator 4 => S.localInner M σ e)
    (planeOperator_four_even (u e) (v e))
  simp only [localInner, planeOperator_eq, add_apply, smul_apply, inner_add_right,
    real_inner_smul_right] at h4
  simp only [axisCoefficient, squareJet_four, innerJet, expPower_zero, pow_zero, pow_one,
    planeOperator_cube, planeOperator_square]
  simp only [planeOperator_eq, add_apply, smul_apply,
    inner_add_right, real_inner_smul_right, mixedCoefficients, localInner,
    one_apply_eq_self, Pi.mul_apply, Pi.pow_apply]
  linear_combination 2 * S.strength e *
    ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ * h4

omit [Fintype V] [Fintype E] in
@[fun_prop] theorem continuous_localInner (S : SpinSystem V E) (M : SpinOperator 4) (e : E) :
    Continuous (fun σ => S.localInner M σ e) := by
  exact ((continuous_apply (S.left e)).subtype_val).inner
    (continuous_const.clm_apply ((continuous_apply (S.right e)).subtype_val))

omit [Fintype V] in
@[fun_prop] theorem continuous_mixedPolynomial (S : SpinSystem V E) (u v w z : E → ℝ) :
    Continuous (fun σ => MixedAlgebra.four (S.mixedCoefficients σ) u v w z) := by
  simp only [MixedAlgebra.four, MixedAlgebra.weighted, mixedCoefficients]
  fun_prop

omit [Fintype V] in
@[fun_prop] theorem continuous_fourthPolynomial (S : SpinSystem V E) (A : E → SpinOperator 4) :
    Continuous (fun σ => fourthPolynomial (fun k => S.twistEnergy A k 0 σ)) := by
  have h (k : ℕ) : Continuous (fun σ => S.twistEnergy A k 0 σ) :=
    (S.continuous_twistEnergy A k).comp (continuous_const.prodMk continuous_id)
  unfold fourthPolynomial
  exact ((((h 4).add ((continuous_const.mul (h 1)).mul (h 3))).add
    (continuous_const.mul ((h 2).pow 2))).add
    ((continuous_const.mul ((h 1).pow 2)).mul (h 2))).add ((h 1).pow 4)

@[expose] def fourthObservable (S : SpinSystem V E) (A : E → SpinOperator 4) : C((V → RP3.Spin), ℝ) :=
  ⟨_, S.continuous_fourthPolynomial A⟩

@[expose] def mixedObservable (S : SpinSystem V E) (u v w z : E → ℝ) : C((V → RP3.Spin), ℝ) :=
  ⟨_, S.continuous_mixedPolynomial u v w z⟩

@[expose] def mixedResponse (S : SpinSystem V E) (u v w z : E → ℝ) : ℝ :=
  S.averageLinear (S.mixedObservable u v w z)

@[simp] theorem average_fourthObservable (S : SpinSystem V E) (A : E → SpinOperator 4) :
    S.averageLinear (S.fourthObservable A) = S.fourthResponse A := rfl

omit [Fintype V] [Fintype E] in
theorem axisCoefficient_one (S : SpinSystem V E) (σ : V → RP3.Spin) :
    S.axisCoefficient axisA 1 σ = (S.mixedCoefficients σ).a ∧
    S.axisCoefficient axisB 1 σ = (S.mixedCoefficients σ).b := by
  constructor <;> funext e <;>
    simp only [axisCoefficient, squareJet_one, pow_zero, pow_one, mixedCoefficients] <;> ring

omit [Fintype V] [Fintype E] in
theorem axisCoefficient_two (S : SpinSystem V E) (σ : V → RP3.Spin) :
    S.axisCoefficient axisA 2 σ = (S.mixedCoefficients σ).aa ∧
    S.axisCoefficient axisB 2 σ = (S.mixedCoefficients σ).bb := by
  constructor <;> funext e <;>
    simp only [axisCoefficient, squareJet_two, pow_zero, pow_one, mixedCoefficients] <;> ring

omit [Fintype V] in
theorem fourthObservable_even (S : SpinSystem V E) (u v : E → ℝ) :
    S.fourthObservable (fun e => planeOperator (u e) (v e)) +
      S.fourthObservable (fun e => planeOperator (u e) (-v e)) -
      (2:ℝ) • S.fourthObservable (fun e => u e • axisA) -
      (2:ℝ) • S.fourthObservable (fun e => v e • axisB) =
      (12:ℝ) • S.mixedObservable u v u v := by
  ext σ
  change fourthPolynomial (fun k => S.twistEnergy (fun e => planeOperator (u e) (v e)) k 0 σ) +
    fourthPolynomial (fun k => S.twistEnergy (fun e => planeOperator (u e) (-v e)) k 0 σ) -
    2 * fourthPolynomial (fun k => S.twistEnergy (fun e => u e • axisA) k 0 σ) -
    2 * fourthPolynomial (fun k => S.twistEnergy (fun e => v e • axisB) k 0 σ) =
    12 * MixedAlgebra.four (S.mixedCoefficients σ) u v u v
  simp only [fourthPolynomial, planeEnergy_one, planeEnergy_two, planeEnergy_three,
    energy_scaled_power S axisA u 1 (by decide), energy_scaled_power S axisA u 2 (by decide),
    energy_scaled_power S axisA u 3 (by decide), energy_scaled_power S axisA u 4 (by decide),
    energy_scaled_power S axisB v 1 (by decide), energy_scaled_power S axisB v 2 (by decide),
    energy_scaled_power S axisB v 3 (by decide), energy_scaled_power S axisB v 4 (by decide),
    (S.axisCoefficient_one σ).1, (S.axisCoefficient_one σ).2,
    (S.axisCoefficient_two σ).1, (S.axisCoefficient_two σ).2, pow_one]
  have hn : (fun e => -v e) = -v := rfl
  have hv3 : (-v)^3 = -(v^3) := by ring
  simp only [hn, hv3, neg_mul, mul_neg, neg_neg, MixedAlgebra.weighted_neg]
  have hb := bell4_even
    (MixedAlgebra.weighted (S.mixedCoefficients σ).a u)
    (MixedAlgebra.weighted (S.mixedCoefficients σ).b v)
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aa (u*u))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).ab (u*v))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).bb (v*v))
    (MixedAlgebra.weighted (S.axisCoefficient axisA 3 σ) (u^3))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aab (u*u*v))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).abb (u*v*v))
    (MixedAlgebra.weighted (S.axisCoefficient axisB 3 σ) (v^3))
    (S.twistEnergy (fun e => planeOperator (u e) (v e)) 4 0 σ)
    (S.twistEnergy (fun e => planeOperator (u e) (-v e)) 4 0 σ)
    (MixedAlgebra.weighted (S.axisCoefficient axisA 4 σ) (u^4))
    (MixedAlgebra.weighted (S.mixedCoefficients σ).aabb (u*u*v*v))
    (MixedAlgebra.weighted (S.axisCoefficient axisB 4 σ) (v^4))
    (S.planeEnergy_four_even u v σ)
  rw [MixedAlgebra.four_diagonal]
  simp only [bell4] at hb
  convert hb using 1 <;> ring_nf

end SpinSystem
end
end RP3.Quadratic
