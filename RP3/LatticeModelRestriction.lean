import RP3.ModelRestriction
import RP3.LatticeAnnuli

/-! Exact restriction of annular kernels and translation of lattice Gibbs systems. -/
namespace RP3.Fourier.LatticeGraph
noncomputable section
open scoped Classical
open RP3

/-- Pins inherited by a restricted retained graph. -/
def restrictionPins (G : LatticeGraph) (P : Site → Prop) (pins : Finset G.vertices) :
    Finset (G.restrict P).vertices :=
  Finset.univ.filter (fun v => G.restrictVertex P v ∈ pins)

/-- Discarding all vertices and zero-strength edges outside a site predicate
identifies the actual pinned partition with the retained subgraph. -/
theorem pinnedPartition_restrict_graph (G : LatticeGraph) (P : Site → Prop)
    (b : G.edges → ℝ)
    (hb : ∀ e, ¬ (P e.val.1.val ∧ P e.val.2.val) → b e = 0)
    (pins : Finset G.vertices) (τ : Configuration G.vertices) :
    pinnedPartition (fun e : G.edges => e.val) b pins τ =
      pinnedPartition (fun e : (G.restrict P).edges => e.val)
        (fun e => b (G.restrictEdge P e)) (G.restrictionPins P pins)
        (fun v => τ (G.restrictVertex P v)) := by
  let Pv : G.vertices → Prop := fun v => P v.val
  have h1 := RP3.pinnedPartition_restrict Pv (fun e : G.edges => e.val) b hb pins τ
  have h2 := RP3.pinnedPartition_reindex (G.restrictVertexEquiv P)
    (G.restrictEdgeEquiv P) (inducedEdge Pv (fun e : G.edges => e.val))
    (fun e : (G.restrict P).edges => e.val) (fun e => b e.val)
    (fun _ => rfl) (fun _ => rfl)
    (inducedPins Pv pins) (G.restrictionPins P pins)
    (by
      intro v
      simp only [restrictionPins, Finset.mem_filter, Finset.mem_univ, true_and,
        mem_inducedPins]
      try rfl)
    (fun v => τ v.val)
  exact h1.trans h2

/-- The finite pin set on the two boundary layers of the restricted annulus. -/
def annulusPinFinset (G : LatticeGraph) (N : ℤ) (z : Site) :
    Finset (G.annulusGraph N z).vertices :=
  Finset.univ.filter (fun v => v ∈ G.annulusPins N z)

set_option backward.isDefEq.respectTransparency false in
/-- Outside the strict annular interior, the remaining vertices of the
restricted annulus are exactly its two boundary layers. -/
theorem restrictionPins_strictLayer_compl (G : LatticeGraph) (N : ℤ) (z : Site) :
    G.restrictionPins (· ∈ annulusSites N z) (G.strictLayer N z)ᶜ =
      G.annulusPinFinset N z := by
  classical
  ext v
  have hv : N ≤ siteRadius z v.val ∧ siteRadius z v.val ≤ 2*N :=
    (Finset.mem_filter.mp v.property).2
  simp only [restrictionPins, annulusPinFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_compl, mem_strictLayer, restrictVertex,
    Set.mem_ofPred_eq, annulusPins, annulusInner, annulusOuter, Set.mem_union]
  change ¬ (N < siteRadius z v.val ∧ siteRadius z v.val < 2*N) ↔
    siteRadius z v.val = N ∨ siteRadius z v.val = 2*N
  omega

/-- The full-graph masked pinned kernel equals the actual annular partition
with its boundary-only couplings set to zero. -/
theorem pinnedKernel_annulus_restrict (G : LatticeGraph) (N : ℤ) (z : Site)
    (b : G.edges → ℝ) (τ : Configuration G.vertices) :
    pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.kernelEdges N z) b) (G.strictLayer N z)ᶜ τ =
    pinnedPartition (fun e : (G.annulusGraph N z).edges => e.val)
      (fun e => maskedCoupling (G.kernelEdges N z) b
        (G.restrictEdge (· ∈ annulusSites N z) e))
      (G.annulusPinFinset N z)
      (fun v => τ (G.restrictVertex (· ∈ annulusSites N z) v)) := by
  have hb : ∀ e : G.edges,
      ¬ (e.val.1.val ∈ annulusSites N z ∧ e.val.2.val ∈ annulusSites N z) →
      maskedCoupling (G.kernelEdges N z) b e = 0 := by
    intro e he
    by_cases hm : e ∈ G.kernelEdges N z
    · exact False.elim (he (G.kernelEdges_endpoints N z e hm))
    · simp only [maskedCoupling, hm, ite_false]
  have h := G.pinnedPartition_restrict_graph (· ∈ annulusSites N z)
    (maskedCoupling (G.kernelEdges N z) b) hb (G.strictLayer N z)ᶜ τ
  rw [restrictionPins_strictLayer_compl] at h
  exact h

/-- Pins transported along a lattice translation. -/
def translatePins (G : LatticeGraph) (z : Site) (pins : Finset G.vertices) :
    Finset (G.translate z).vertices :=
  Finset.univ.filter (fun v => (G.translateVertexEquiv z).symm v ∈ pins)

set_option backward.isDefEq.respectTransparency false in
/-- Translation is only a relabeling of the pinned RP³ integral. -/
theorem pinnedPartition_translate (G : LatticeGraph) (z : Site) (b : G.edges → ℝ)
    (pins : Finset G.vertices) (τ : Configuration G.vertices) :
    pinnedPartition (fun e : G.edges => e.val) b pins τ =
      pinnedPartition (fun e : (G.translate z).edges => e.val)
        (fun e => b ((G.translateEdgeEquiv z).symm e)) (G.translatePins z pins)
        (fun v => τ ((G.translateVertexEquiv z).symm v)) := by
  classical
  apply RP3.pinnedPartition_reindex (G.translateVertexEquiv z)
    (G.translateEdgeEquiv z) (fun e : G.edges => e.val)
    (fun e : (G.translate z).edges => e.val) b
    (G.translateEdgeEquiv_left z) (G.translateEdgeEquiv_right z)
    pins (G.translatePins z pins)
  intro v
  have hm (w : (G.translate z).vertices) :
      w ∈ G.translatePins z pins ↔ (G.translateVertexEquiv z).symm w ∈ pins := by
    exact (@Finset.mem_filter (G.translate z).vertices
      (fun a => (G.translateVertexEquiv z).symm a ∈ pins)
      (fun a => Classical.propDecidable _) Finset.univ w).trans
      (and_iff_right (Finset.mem_univ w))
  exact (hm ((G.translateVertexEquiv z) v)).trans
    (by rw [Equiv.symm_apply_apply])

/-- The original vertex corresponding to a site of the centered annulus. -/
def annulusOriginalVertex (G : LatticeGraph) (N : ℤ) (z : Site)
    (v : ((G.annulusGraph N z).translate z).vertices) : G.vertices :=
  G.restrictVertex (· ∈ annulusSites N z)
    (((G.annulusGraph N z).translateVertexEquiv z).symm v)

theorem annulusOriginalVertex_radius (G : LatticeGraph) (N : ℤ) (z : Site)
    (v : ((G.annulusGraph N z).translate z).vertices) :
    siteRadius z (G.annulusOriginalVertex N z v).val = siteRadius 0 v.val := by
  have h := (G.annulusGraph N z).translateVertexEquiv_val z
    (((G.annulusGraph N z).translateVertexEquiv z).symm v)
  have hc := congrArg (fun w => w.val)
    (((G.annulusGraph N z).translateVertexEquiv z).apply_symm_apply v)
  have h' : v.val = (((G.annulusGraph N z).translateVertexEquiv z).symm v).val - z :=
    hc.symm.trans h
  calc
    _ = siteRadius 0 ((((G.annulusGraph N z).translateVertexEquiv z).symm v).val - z) := by
      simp only [annulusOriginalVertex, restrictVertex, siteRadius,
        Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero]
    _ = _ := congrArg (siteRadius 0) h'.symm

theorem translated_annulus_within_box (G : LatticeGraph) (k : ℕ) (z : Site) :
    ((G.annulusGraph (2^k) z).translate z).WithinDyadicBox k := by
  intro v
  let w := (((G.annulusGraph (2^k) z).translateVertexEquiv z).symm v)
  have hv : (2:ℤ)^k ≤ siteRadius z w.val ∧ siteRadius z w.val ≤ 2*(2:ℤ)^k :=
    (Finset.mem_filter.mp w.property).2
  have hr := G.annulusOriginalVertex_radius (2^k) z v
  have hbound : siteRadius 0 v.val ≤ 2*(2:ℤ)^k := by
    rw [← hr]
    exact hv.2
  simpa only [siteRadius, Prod.fst_zero, Prod.snd_zero, sub_zero,
    max_le_iff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hbound

theorem translated_annulus_pin_radius (G : LatticeGraph) (N : ℤ) (z : Site)
    (v : ((G.annulusGraph N z).translate z).vertices)
    (hv : v ∈ (G.annulusGraph N z).translatePins z (G.annulusPinFinset N z)) :
    siteRadius 0 v.val = N ∨ siteRadius 0 v.val = 2*N := by
  have hr := G.annulusOriginalVertex_radius N z v
  simp only [translatePins, Finset.mem_filter, Finset.mem_univ, true_and,
    annulusPinFinset] at hv
  change siteRadius z (G.annulusOriginalVertex N z v).val = N ∨
    siteRadius z (G.annulusOriginalVertex N z v).val = 2*N at hv
  rwa [hr] at hv

/-- An inner cut on the original graph becomes the radial inner cut after
restriction and translation. This identity holds for every boundary array. -/
theorem annulusOriginalVertex_cut (G : LatticeGraph) (N : ℤ) (z : Site)
    {H : Type*} [Group H] (A : FiniteAction H Spin) (g : H)
    (τ : Configuration G.vertices)
    (v : ((G.annulusGraph N z).translate z).vertices) :
    (A.onCut (G.innerCut N z)).move g τ (G.annulusOriginalVertex N z v) =
      if siteRadius 0 v.val ≤ N then A.move g (τ (G.annulusOriginalVertex N z v))
      else τ (G.annulusOriginalVertex N z v) := by
  simp only [FiniteAction.onCut_apply, mem_innerCut, annulusOriginalVertex_radius]

/-- A single exact equality from the full-graph kernel to the origin-centered
annular pinned model used by the Fourier estimates. -/
theorem pinnedKernel_centered_annulus (G : LatticeGraph) (N : ℤ) (z : Site)
    (b : G.edges → ℝ) (τ : Configuration G.vertices) :
    pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.kernelEdges N z) b) (G.strictLayer N z)ᶜ τ =
    pinnedPartition (fun e : ((G.annulusGraph N z).translate z).edges => e.val)
      (fun e => maskedCoupling (G.kernelEdges N z) b
        (G.restrictEdge (· ∈ annulusSites N z)
          (((G.annulusGraph N z).translateEdgeEquiv z).symm e)))
      ((G.annulusGraph N z).translatePins z (G.annulusPinFinset N z))
      (fun v => τ (G.annulusOriginalVertex N z v)) := by
  exact (G.pinnedKernel_annulus_restrict N z b τ).trans
    ((G.annulusGraph N z).pinnedPartition_translate z _ _ _)
end
end RP3.Fourier.LatticeGraph
