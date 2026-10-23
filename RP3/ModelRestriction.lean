module

public import RP3.ModelAssembly

public section

/-!
# Restriction and relabeling of actual pinned RP³ partitions

Vertices with no active interaction can be discarded, even if they are
pinned. Coordinate projection pushes the full product reference law to the
restricted product law; the assertions are exact equalities.
-/
namespace RP3
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

section Restriction
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
variable (P : V → Prop) [DecidablePred P]

/-- Restricting an independent reference configuration to any set of sites
has the corresponding independent reference distribution. -/
theorem referenceLaw_restrict_measurePreserving :
    MeasurePreserving (fun σ : Configuration V => fun v : {v // P v} => σ v.val)
      (referenceLaw (V := V)) (referenceLaw (V := {v // P v})) := by
  have hp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : V => sphereProbability) P
  exact measurePreserving_fst.comp hp

@[expose] def inducedEdge (edge : E → V × V) :
    {e : E // P (edge e).1 ∧ P (edge e).2} → {v // P v} × {v // P v} :=
  fun e => (⟨(edge e.val).1, e.property.1⟩, ⟨(edge e.val).2, e.property.2⟩)

@[expose] def inducedPins (pins : Finset V) : Finset {v // P v} :=
  Finset.univ.filter (fun v => v.val ∈ pins)

@[simp] theorem mem_inducedPins (pins : Finset V) (v : {v // P v}) :
    v ∈ inducedPins P pins ↔ v.val ∈ pins := by simp [inducedPins]

/-- Removing zero-strength edges and irrelevant vertices does not change
an interaction evaluated at the remaining spins. -/
theorem interaction_restrict (edge : E → V × V) (b : E → ℝ)
    (hb : ∀ e, ¬ (P (edge e).1 ∧ P (edge e).2) → b e = 0)
    (σ : Configuration V) :
    interaction edge b σ =
      interaction (inducedEdge P edge) (fun e => b e.val) (fun v => σ v.val) := by
  let q : E → Prop := fun e => P (edge e).1 ∧ P (edge e).2
  let f : E → ℝ := fun e => b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2
  have hsum := Fintype.sum_subtype_add_sum_subtype q f
  have hz : (∑ e : {e // ¬ q e}, f e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    simp only [f, hb e.val e.property, zero_mul]
  rw [hz, add_zero] at hsum
  exact hsum.symm

/-- Exact identification with a smaller pinned finite-volume system. -/
theorem pinnedPartition_restrict (edge : E → V × V) (b : E → ℝ)
    (hb : ∀ e, ¬ (P (edge e).1 ∧ P (edge e).2) → b e = 0)
    (pins : Finset V) (τ : Configuration V) :
    pinnedPartition edge b pins τ =
      pinnedPartition (inducedEdge P edge) (fun e => b e.val)
        (inducedPins P pins) (fun v => τ v.val) := by
  have hfill (σ : Configuration V) :
      (fun v : {v // P v} => fillPins pins τ σ v.val) =
      fillPins (inducedPins P pins) (fun v => τ v.val) (fun v => σ v.val) := by
    funext v
    simp only [fillPins, ContinuousMap.coe_mk, mem_inducedPins]
  change (∫ σ, Real.exp (interaction edge b (fillPins pins τ σ)) ∂referenceLaw) = _
  simp_rw [interaction_restrict P edge b hb, hfill]
  have hm := referenceLaw_restrict_measurePreserving P
  have hi := integral_map_of_stronglyMeasurable
    (μ := referenceLaw (V := V)) hm.measurable
    (pinnedWeight (inducedEdge P edge) (fun e => b e.val)
      (inducedPins P pins) (fun v => τ v.val)).continuous.stronglyMeasurable
  rw [hm.map_eq] at hi
  exact hi.symm
end Restriction

section Reindex
variable {V E W F : Type*} [Fintype V] [Fintype E] [Fintype W] [Fintype F]
  [DecidableEq V] [DecidableEq W]

/-- The same finite interaction in relabeled vertex and edge coordinates. -/
theorem interaction_reindex (ev : V ≃ W) (ee : E ≃ F)
    (edge : E → V × V) (edge' : F → W × W) (b : E → ℝ)
    (hl : ∀ e, (edge' (ee e)).1 = ev (edge e).1)
    (hr : ∀ e, (edge' (ee e)).2 = ev (edge e).2)
    (σ : Configuration V) :
    interaction edge b σ = interaction edge' (fun e => b (ee.symm e))
      (fun v => σ (ev.symm v)) := by
  apply Fintype.sum_equiv ee
  intro e
  simp only [ee.symm_apply_apply, hl, hr, ev.symm_apply_apply]

/-- Relabeling vertices, edges, pins, and boundary arrays leaves the actual
pinned partition function unchanged. -/
theorem pinnedPartition_reindex (ev : V ≃ W) (ee : E ≃ F)
    (edge : E → V × V) (edge' : F → W × W) (b : E → ℝ)
    (hl : ∀ e, (edge' (ee e)).1 = ev (edge e).1)
    (hr : ∀ e, (edge' (ee e)).2 = ev (edge e).2)
    (pins : Finset V) (pins' : Finset W)
    (hp : ∀ v, ev v ∈ pins' ↔ v ∈ pins)
    (τ : Configuration V) :
    pinnedPartition edge b pins τ =
      pinnedPartition edge' (fun e => b (ee.symm e)) pins' (fun v => τ (ev.symm v)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : W => Spin) ev
  have hm : MeasurePreserving e (referenceLaw (V := V)) (referenceLaw (V := W)) :=
    measurePreserving_piCongrLeft (fun _ : W => sphereProbability) ev
  have hfill (σ : Configuration V) :
      (fun v : W => fillPins pins τ σ (ev.symm v)) =
      fillPins pins' (fun v => τ (ev.symm v)) (e σ) := by
    funext v
    have hv : v ∈ pins' ↔ ev.symm v ∈ pins := by simpa using hp (ev.symm v)
    have heval : e σ v = σ (ev.symm v) := by
      have hh := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : W => Spin) ev σ (ev.symm v)
      simpa only [Equiv.apply_symm_apply] using hh
    simp only [fillPins, ContinuousMap.coe_mk, hv, heval]
  change (∫ σ, Real.exp (interaction edge b (fillPins pins τ σ)) ∂referenceLaw) = _
  simp_rw [interaction_reindex ev ee edge edge' b hl hr, hfill]
  exact hm.integral_comp e.measurableEmbedding
    (fun σ => Real.exp (interaction edge' (fun e => b (ee.symm e))
      (fillPins pins' (fun v => τ (ev.symm v)) σ)))
end Reindex
end
end RP3
