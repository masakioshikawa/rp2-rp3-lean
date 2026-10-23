module

public import RP3.QuaternionAction

public section

/-!
# The positive active-edge expansion of the actual RP³ model

This module develops the exact finite expansion and disconnected-component
cancellation used in a high-temperature argument. It does not assume a mixing
estimate. The bound at the end is a bound by the mass of connected active-edge
sets; independent-bond domination and path counting are separate steps.

The interaction may have either sign. Subtracting `min (b e) 0` from each edge
energy makes its activity nonnegative without changing the Gibbs probability.
-/

namespace RP3.HighTemperature

noncomputable section
open MeasureTheory Finset
open scoped BigOperators InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

@[expose] def edgeActivity (edge : E → V × V) (b : E → ℝ) (e : E) :
    C(Configuration V, ℝ) :=
  ⟨fun σ => Real.exp (b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2
    - min (b e) 0) - 1, by fun_prop⟩

@[expose] def activeWeight (edge : E → V × V) (b : E → ℝ) (A : Finset E) :
    C(Configuration V, ℝ) := ∏ e ∈ A, edgeActivity edge b e

@[expose] def expandedWeight (edge : E → V × V) (b : E → ℝ) :
    C(Configuration V, ℝ) := ∏ e : E, (1 + edgeActivity edge b e)

/-- A cut separates the endpoints and no selected edge crosses it. -/
@[expose] def ActiveSeparated (edge : E → V × V) (A : Finset E) (x y : V) : Prop :=
  ∃ cut : Finset V, x ∈ cut ∧ y ∉ cut ∧
    ∀ e ∈ A, ((edge e).1 ∈ cut ↔ (edge e).2 ∈ cut)

/-- The cut characterization of connectivity avoids choosing a path. -/
@[expose] def ActiveConnected (edge : E → V × V) (A : Finset E) (x y : V) : Prop :=
  ¬ ActiveSeparated edge A x y

@[expose] def connectedMass (edge : E → V × V) (b : E → ℝ) (x y : V) : ℝ := by
  classical
  exact ∑ A ∈ (univ : Finset E).powerset,
    if ActiveConnected edge A x y then
      (integralOnCompact (referenceLaw (V := V))).linear (activeWeight edge b A)
    else 0

theorem edge_energy_nonneg (edge : E → V × V) (b : E → ℝ) (e : E)
    (σ : Configuration V) :
    0 ≤ b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2 - min (b e) 0 := by
  have hn := sq_nonneg ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ
  have ha := abs_real_inner_le_norm (σ (edge e).1).val (σ (edge e).2).val
  simp only [spin_norm, one_mul] at ha
  have hu := (sq_le_one_iff_abs_le_one _).mpr ha
  by_cases hb : 0 ≤ b e
  · rw [min_eq_right hb, sub_zero]
    exact mul_nonneg hb hn
  · have hb' : b e ≤ 0 := le_of_not_ge hb
    rw [min_eq_left hb']
    have hm := mul_le_mul_of_nonpos_left hu hb'
    nlinarith

theorem edgeActivity_nonneg (edge : E → V × V) (b : E → ℝ) (e : E)
    (σ : Configuration V) : 0 ≤ edgeActivity edge b e σ := by
  change 0 ≤ Real.exp _ - 1
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (edge_energy_nonneg edge b e σ))

theorem edge_energy_le_abs (edge : E → V × V) (b : E → ℝ) (e : E)
    (σ : Configuration V) :
    b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2 - min (b e) 0 ≤
      |b e| := by
  have hn := sq_nonneg ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ
  have ha := abs_real_inner_le_norm (σ (edge e).1).val (σ (edge e).2).val
  simp only [spin_norm, one_mul] at ha
  have hu := (sq_le_one_iff_abs_le_one _).mpr ha
  by_cases hb : 0 ≤ b e
  · rw [min_eq_right hb, sub_zero, abs_of_nonneg hb]
    simpa using mul_le_mul_of_nonneg_left hu hb
  · have hb' : b e ≤ 0 := le_of_not_ge hb
    rw [min_eq_left hb', abs_of_nonpos hb']
    have hm := mul_nonpos_of_nonpos_of_nonneg hb' hn
    linarith

/-- The elementary opening coefficient is valid pointwise, before integration. -/
theorem edgeActivity_le_opening_coefficient (edge : E → V × V) (b : E → ℝ)
    (e : E) (β : ℝ) (hb : |b e| ≤ β) (σ : Configuration V) :
    edgeActivity edge b e σ ≤
      (1 - Real.exp (-β)) * (1 + edgeActivity edge b e σ) := by
  have he := (edge_energy_le_abs edge b e σ).trans hb
  have hp : Real.exp (-β) *
      Real.exp (b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2 -
        min (b e) 0) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr (by linarith)
  change Real.exp _ - 1 ≤ (1 - Real.exp (-β)) * (1 + (Real.exp _ - 1))
  nlinarith

theorem activeWeight_nonneg (edge : E → V × V) (b : E → ℝ) (A : Finset E)
    (σ : Configuration V) : 0 ≤ activeWeight edge b A σ := by
  simp only [activeWeight, ContinuousMap.prod_apply]
  exact prod_nonneg (fun e _ => edgeActivity_nonneg edge b e σ)

theorem expandedWeight_eq_sum (edge : E → V × V) (b : E → ℝ) :
    expandedWeight edge b =
      ∑ A ∈ (univ : Finset E).powerset, activeWeight edge b A := by
  exact prod_one_add (f := edgeActivity edge b) univ

theorem expandedWeight_eq_smul_weight (edge : E → V × V) (b : E → ℝ) :
    expandedWeight edge b =
      Real.exp (-∑ e : E, min (b e) 0) • weight edge b := by
  ext σ
  simp only [expandedWeight, ContinuousMap.prod_apply, ContinuousMap.add_apply,
    ContinuousMap.one_apply, edgeActivity, ContinuousMap.coe_mk,
    ContinuousMap.smul_apply, smul_eq_mul, weight]
  simp only [← add_sub_assoc, add_sub_cancel_left]
  rw [← Real.exp_sum]
  rw [← Real.exp_add]
  congr 1
  simp only [sum_sub_distrib, interaction]
  ring

theorem quaternion_inner (g : Quaternion) (s t : Spin) :
    ⟪(quaternionAction.move g s).val, (quaternionAction.move g t).val⟫_ℝ =
      ⟪s.val, t.val⟫_ℝ :=
  (quaternionLinearIsometry g).inner_map_map s.val t.val

theorem edgeActivity_onCut (edge : E → V × V) (b : E → ℝ) (e : E)
    (cut : Finset V) (hcut : (edge e).1 ∈ cut ↔ (edge e).2 ∈ cut)
    (g : Quaternion) (σ : Configuration V) :
    edgeActivity edge b e ((quaternionAction.onCut cut).move g σ) =
      edgeActivity edge b e σ := by
  by_cases hleft : (edge e).1 ∈ cut
  · have hright := hcut.mp hleft
    simp only [edgeActivity, ContinuousMap.coe_mk, FiniteAction.onCut_apply,
      hleft, hright, ite_true, quaternion_inner]
  · have hright : (edge e).2 ∉ cut := fun h => hleft (hcut.mpr h)
    simp only [edgeActivity, ContinuousMap.coe_mk, FiniteAction.onCut_apply,
      hleft, hright, ite_false]

theorem activeWeight_onCut (edge : E → V × V) (b : E → ℝ) (A : Finset E)
    (cut : Finset V)
    (hcut : ∀ e ∈ A, (edge e).1 ∈ cut ↔ (edge e).2 ∈ cut)
    (g : Quaternion) (σ : Configuration V) :
    activeWeight edge b A ((quaternionAction.onCut cut).move g σ) =
      activeWeight edge b A σ := by
  simp only [activeWeight, ContinuousMap.prod_apply]
  exact prod_congr rfl (fun e he => edgeActivity_onCut edge b e cut (hcut e he) g σ)

/-- Cancellation is proved separately in each disconnected expansion term. -/
theorem separated_numerator_zero (edge : E → V × V) (b : E → ℝ)
    (A : Finset E) (x y : V) (hsep : ActiveSeparated edge A x y) :
    (integralOnCompact (referenceLaw (V := V))).linear
      (observable x y * activeWeight edge b A) = 0 := by
  rcases hsep with ⟨cut, hx, hy, hcut⟩
  let I := integralOnCompact (referenceLaw (V := V))
  let action := quaternionAction.onCut cut
  have havg : action.average (activeWeight edge b A) = activeWeight edge b A :=
    action.average_of_invariant _ (activeWeight_onCut edge b A cut hcut)
  have hpres (f : C(Configuration V, ℝ)) : I.linear (action.average f) = I.linear f := by
    exact action.preserve_integral I (fun g f =>
      (quaternionAction.onCut_measurePreserving sphereProbability
        quaternionAction_measurePreserving cut g).integral_comp
        (action.toHomeomorph g).measurableEmbedding f) f
  calc
    _ = I.linear (activeWeight edge b A * observable x y) := by rw [mul_comm]
    _ = I.linear (action.average (activeWeight edge b A * observable x y)) :=
      (hpres _).symm
    _ = I.linear (activeWeight edge b A * action.average (observable x y)) := by
      rw [action.average_pull _ _ havg]
    _ = 0 := by
      rw [quaternionAction_cut_average_zero cut x y hx hy, mul_zero, map_zero]

theorem abs_expanded_numerator_le (edge : E → V × V) (b : E → ℝ) (x y : V) :
    |(integralOnCompact (referenceLaw (V := V))).linear
      (observable x y * expandedWeight edge b)| ≤
      (3 : ℝ) / 4 * connectedMass edge b x y := by
  classical
  let I := integralOnCompact (referenceLaw (V := V))
  rw [expandedWeight_eq_sum, mul_sum, map_sum]
  calc
    _ ≤ ∑ A ∈ (univ : Finset E).powerset,
        |I.linear (observable x y * activeWeight edge b A)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ (univ : Finset E).powerset,
        ((3 : ℝ) / 4) * (if ActiveConnected edge A x y then
          I.linear (activeWeight edge b A) else 0) := by
      apply sum_le_sum
      intro A hA
      by_cases h : ActiveConnected edge A x y
      · simp only [h, ite_true]
        exact I.abs_weighted_le _ _ (fun σ => abs_qPair_le (σ x) (σ y))
          (activeWeight_nonneg edge b A)
      · have hs : ActiveSeparated edge A x y := Classical.not_not.mp h
        rw [separated_numerator_zero edge b A x y hs]
        simp [h]
    _ = _ := by rw [← mul_sum]; rfl

theorem expanded_partition_pos (edge : E → V × V) (b : E → ℝ) :
    0 < (integralOnCompact (referenceLaw (V := V))).linear (expandedWeight edge b) := by
  rw [expandedWeight_eq_smul_weight, map_smul]
  exact mul_pos (Real.exp_pos _) (partition_pos edge b)

theorem correlation_eq_expanded (edge : E → V × V) (b : E → ℝ) (x y : V) :
    correlation edge b x y =
      (integralOnCompact (referenceLaw (V := V))).linear
          (observable x y * expandedWeight edge b) /
        (integralOnCompact (referenceLaw (V := V))).linear (expandedWeight edge b) := by
  rw [expandedWeight_eq_smul_weight, mul_smul_comm, map_smul, map_smul]
  simp only [smul_eq_mul, correlation, partition]
  rw [mul_div_mul_left _ _ (Real.exp_ne_zero _)]

/-- Exact bridge from the model to the mass of connected active-edge sets. -/
theorem abs_correlation_le_connected_mass (edge : E → V × V) (b : E → ℝ) (x y : V) :
    |correlation edge b x y| ≤
      ((3 : ℝ) / 4 * connectedMass edge b x y) /
        (integralOnCompact (referenceLaw (V := V))).linear (expandedWeight edge b) := by
  rw [correlation_eq_expanded, abs_div, abs_of_pos (expanded_partition_pos edge b)]
  exact div_le_div_of_nonneg_right (abs_expanded_numerator_le edge b x y)
    (expanded_partition_pos edge b).le

end
end RP3.HighTemperature
