import RP3.ThinAnnuli
import RP3.KernelEstimate

/-! Exact restriction and centering of arbitrary-width annular kernels. -/
namespace RP3.Fourier.LatticeGraph
noncomputable section
open scoped Classical
open RP3

def thinAnnulusGraph (G : LatticeGraph) (R S : ℤ) (z : Site) :=
  G.restrict (· ∈ thinAnnulusSites R S z)

def thinAnnulusInner (G : LatticeGraph) (R S : ℤ) (z : Site) :
    Set (G.thinAnnulusGraph R S z).vertices := {v | siteRadius z v.val = R}

def thinAnnulusOuter (G : LatticeGraph) (R S : ℤ) (z : Site) :
    Set (G.thinAnnulusGraph R S z).vertices := {v | siteRadius z v.val = S}

def thinAnnulusPins (G : LatticeGraph) (R S : ℤ) (z : Site) :
    Set (G.thinAnnulusGraph R S z).vertices :=
  G.thinAnnulusInner R S z ∪ G.thinAnnulusOuter R S z

/-- The finite pin set on the two boundary layers of the restricted annulus. -/
def thinAnnulusPinFinset (G : LatticeGraph) (R S : ℤ) (z : Site) :
    Finset (G.thinAnnulusGraph R S z).vertices :=
  Finset.univ.filter (fun v => v ∈ G.thinAnnulusPins R S z)

set_option backward.isDefEq.respectTransparency false in
/-- Outside the strict annular interior, the remaining vertices of the
restricted annulus are exactly its two boundary layers. -/
theorem restrictionPins_thinLayer_compl (G : LatticeGraph) (R S : ℤ) (z : Site) :
    G.restrictionPins (· ∈ thinAnnulusSites R S z) (G.thinLayer R S z)ᶜ =
      G.thinAnnulusPinFinset R S z := by
  classical
  ext v
  have hv : R ≤ siteRadius z v.val ∧ siteRadius z v.val ≤ S :=
    (Finset.mem_filter.mp v.property).2
  simp only [restrictionPins, thinAnnulusPinFinset, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_compl, mem_thinLayer, restrictVertex,
    Set.mem_ofPred_eq, thinAnnulusPins, thinAnnulusInner, thinAnnulusOuter, Set.mem_union]
  change ¬ (R < siteRadius z v.val ∧ siteRadius z v.val < S) ↔
    siteRadius z v.val = R ∨ siteRadius z v.val = S
  omega

/-- The full-graph masked pinned kernel equals the actual annular partition
with its boundary-only couplings set to zero. -/
theorem pinnedKernel_thinAnnulus_restrict (G : LatticeGraph) (R S : ℤ) (z : Site)
    (b : G.edges → ℝ) (τ : Configuration G.vertices) :
    pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.thinKernelEdges R S z) b) (G.thinLayer R S z)ᶜ τ =
    pinnedPartition (fun e : (G.thinAnnulusGraph R S z).edges => e.val)
      (fun e => maskedCoupling (G.thinKernelEdges R S z) b
        (G.restrictEdge (· ∈ thinAnnulusSites R S z) e))
      (G.thinAnnulusPinFinset R S z)
      (fun v => τ (G.restrictVertex (· ∈ thinAnnulusSites R S z) v)) := by
  have hb : ∀ e : G.edges,
      ¬ (e.val.1.val ∈ thinAnnulusSites R S z ∧ e.val.2.val ∈ thinAnnulusSites R S z) →
      maskedCoupling (G.thinKernelEdges R S z) b e = 0 := by
    intro e he
    by_cases hm : e ∈ G.thinKernelEdges R S z
    · exact False.elim (he (G.thinKernelEdges_endpoints R S z e hm))
    · simp only [maskedCoupling, hm, ite_false]
  have h := G.pinnedPartition_restrict_graph (· ∈ thinAnnulusSites R S z)
    (maskedCoupling (G.thinKernelEdges R S z) b) hb (G.thinLayer R S z)ᶜ τ
  rw [restrictionPins_thinLayer_compl] at h
  exact h

/-- The original vertex corresponding to a site of the centered annulus. -/
def thinAnnulusOriginalVertex (G : LatticeGraph) (R S : ℤ) (z : Site)
    (v : ((G.thinAnnulusGraph R S z).translate z).vertices) : G.vertices :=
  G.restrictVertex (· ∈ thinAnnulusSites R S z)
    (((G.thinAnnulusGraph R S z).translateVertexEquiv z).symm v)

theorem thinAnnulusOriginalVertex_radius (G : LatticeGraph) (R S : ℤ) (z : Site)
    (v : ((G.thinAnnulusGraph R S z).translate z).vertices) :
    siteRadius z (G.thinAnnulusOriginalVertex R S z v).val = siteRadius 0 v.val := by
  have h := (G.thinAnnulusGraph R S z).translateVertexEquiv_val z
    (((G.thinAnnulusGraph R S z).translateVertexEquiv z).symm v)
  have hc := congrArg (fun w => w.val)
    (((G.thinAnnulusGraph R S z).translateVertexEquiv z).apply_symm_apply v)
  have h' : v.val = (((G.thinAnnulusGraph R S z).translateVertexEquiv z).symm v).val - z :=
    hc.symm.trans h
  calc
    _ = siteRadius 0 ((((G.thinAnnulusGraph R S z).translateVertexEquiv z).symm v).val - z) := by
      simp only [thinAnnulusOriginalVertex, restrictVertex, siteRadius,
        Prod.fst_sub, Prod.snd_sub, Prod.fst_zero, Prod.snd_zero, sub_zero]
    _ = _ := congrArg (siteRadius 0) h'.symm

theorem translated_thinAnnulus_within_box (G : LatticeGraph) (R S : ℤ)
    (k : ℕ) (z : Site) (hS : S ≤ 2*(2:ℤ)^k) :
    ((G.thinAnnulusGraph R S z).translate z).WithinDyadicBox k := by
  intro v
  let w := (((G.thinAnnulusGraph R S z).translateVertexEquiv z).symm v)
  have hv : R ≤ siteRadius z w.val ∧ siteRadius z w.val ≤ S :=
    (Finset.mem_filter.mp w.property).2
  have hr := G.thinAnnulusOriginalVertex_radius R S z v
  have hbound : siteRadius 0 v.val ≤ 2*(2:ℤ)^k := by
    rw [← hr]
    exact hv.2.trans hS
  simpa only [siteRadius, Prod.fst_zero, Prod.snd_zero, sub_zero,
    max_le_iff, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hbound

theorem translated_thinAnnulus_pin_radius (G : LatticeGraph) (R S : ℤ) (z : Site)
    (v : ((G.thinAnnulusGraph R S z).translate z).vertices)
    (hv : v ∈ (G.thinAnnulusGraph R S z).translatePins z (G.thinAnnulusPinFinset R S z)) :
    siteRadius 0 v.val = R ∨ siteRadius 0 v.val = S := by
  have hr := G.thinAnnulusOriginalVertex_radius R S z v
  simp only [translatePins, Finset.mem_filter, Finset.mem_univ, true_and,
    thinAnnulusPinFinset] at hv
  change siteRadius z (G.thinAnnulusOriginalVertex R S z v).val = R ∨
    siteRadius z (G.thinAnnulusOriginalVertex R S z v).val = S at hv
  rwa [hr] at hv

/-- An inner cut on the original graph becomes the radial inner cut after
restriction and translation. This identity holds for every boundary array. -/
theorem thinAnnulusOriginalVertex_cut (G : LatticeGraph) (R S : ℤ) (z : Site)
    {H : Type*} [Group H] (A : FiniteAction H Spin) (g : H)
    (τ : Configuration G.vertices)
    (v : ((G.thinAnnulusGraph R S z).translate z).vertices) :
    (A.onCut (G.innerCut R z)).move g τ (G.thinAnnulusOriginalVertex R S z v) =
      if siteRadius 0 v.val ≤ R then A.move g (τ (G.thinAnnulusOriginalVertex R S z v))
      else τ (G.thinAnnulusOriginalVertex R S z v) := by
  simp only [FiniteAction.onCut_apply, mem_innerCut, thinAnnulusOriginalVertex_radius]

/-- A single exact equality from the full-graph kernel to the origin-centered
annular pinned model used by the Fourier estimates. -/
theorem pinnedKernel_centered_thinAnnulus (G : LatticeGraph) (R S : ℤ) (z : Site)
    (b : G.edges → ℝ) (τ : Configuration G.vertices) :
    pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.thinKernelEdges R S z) b) (G.thinLayer R S z)ᶜ τ =
    pinnedPartition (fun e : ((G.thinAnnulusGraph R S z).translate z).edges => e.val)
      (fun e => maskedCoupling (G.thinKernelEdges R S z) b
        (G.restrictEdge (· ∈ thinAnnulusSites R S z)
          (((G.thinAnnulusGraph R S z).translateEdgeEquiv z).symm e)))
      ((G.thinAnnulusGraph R S z).translatePins z (G.thinAnnulusPinFinset R S z))
      (fun v => τ (G.thinAnnulusOriginalVertex R S z v)) := by
  exact (G.pinnedKernel_thinAnnulus_restrict R S z b τ).trans
    ((G.thinAnnulusGraph R S z).pinnedPartition_translate z _ _ _)

/-- Cut rotations commute with the restriction-and-translation map. -/
theorem thinAnnulusOriginalVertex_cut_array (G : LatticeGraph) (R S : ℤ) (z : Site)
    {H : Type*} [Group H] (A : FiniteAction H Spin) (g : H)
    (τ : Configuration G.vertices) :
    (fun v => (A.onCut (G.innerCut R z)).move g τ
      (G.thinAnnulusOriginalVertex R S z v)) =
      (A.onCut (((G.thinAnnulusGraph R S z).translate z).innerCut R 0)).move g
        (fun v => τ (G.thinAnnulusOriginalVertex R S z v)) := by
  funext v
  simp only [FiniteAction.onCut_apply, mem_innerCut, thinAnnulusOriginalVertex_radius]

/-- The same exact identification for a rotated inner boundary. -/
theorem pinnedKernel_centered_thinAnnulus_cut (G : LatticeGraph)
    (R S : ℤ) (z : Site) (b : G.edges → ℝ)
    {H : Type*} [Group H] (A : FiniteAction H Spin) (g : H)
    (τ : Configuration G.vertices) :
    pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.thinKernelEdges R S z) b) (G.thinLayer R S z)ᶜ
      ((A.onCut (G.innerCut R z)).move g τ) =
    pinnedPartition (fun e : ((G.thinAnnulusGraph R S z).translate z).edges => e.val)
      (fun e => maskedCoupling (G.thinKernelEdges R S z) b
        (G.restrictEdge (· ∈ thinAnnulusSites R S z)
          (((G.thinAnnulusGraph R S z).translateEdgeEquiv z).symm e)))
      ((G.thinAnnulusGraph R S z).translatePins z (G.thinAnnulusPinFinset R S z))
      ((A.onCut (((G.thinAnnulusGraph R S z).translate z).innerCut R 0)).move g
        (fun v => τ (G.thinAnnulusOriginalVertex R S z v))) := by
  rw [pinnedKernel_centered_thinAnnulus, thinAnnulusOriginalVertex_cut_array]

end
end RP3.Fourier.LatticeGraph

namespace RP3
noncomputable section
open Rotation hiding Spin
open Quadratic
open scoped Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- An arbitrary interpolation potential gives the prescribed cut rotation
whenever it is the cut indicator at the pinned vertices. -/
theorem pinnedSystem_rotatePotential_eq_cut
    (edge : E → V × V) (b : E → ℝ) (pins cut : Finset V)
    (θ : V → ℝ) (hθ : ∀ v ∈ pins, θ v = if v ∈ cut then 1 else 0)
    (τ : Configuration V) (t : ℝ) :
    (pinnedSystem edge b pins τ).rotatePotential θ t =
      pinnedSystem edge b pins (coordinateCut cut 2 t τ) := by
  have hp : ((pinnedSystem edge b pins τ).rotatePotential θ t).pin =
      (pinnedSystem edge b pins (coordinateCut cut 2 t τ)).pin := by
    funext v
    by_cases hv : v ∈ pins
    · simp only [SpinSystem.rotatePotential, SpinSystem.rotatePins, pinnedSystem,
        hv, ite_true, Option.map_some]
      apply congrArg some
      apply Subtype.ext
      have hh := hθ v hv
      by_cases hc : v ∈ cut
      · simp only [hc, ite_true] at hh
        simp only [coordinateCut, rotateCut, hc, ite_true, spinRotation_val,
          SpinSystem.potentialRotation, hh, mul_one,
          coordinateRotation_apply, coordinateAxis, rotationExp_apply]
        try rfl
      · simp only [hc, ite_false] at hh
        simp only [coordinateCut, rotateCut, hc, ite_false, spinRotation_val,
          SpinSystem.potentialRotation, hh, mul_zero, zero_smul ℝ axisC,
          rotationExp_apply, NormedSpace.exp_zero, one_apply_eq_self]
    · simp only [SpinSystem.rotatePotential, SpinSystem.rotatePins, pinnedSystem,
        hv, ite_false, Option.map_none]
  exact congrArg (fun p => SpinSystem.mk (fun e => (edge e).1)
    (fun e => (edge e).2) b p) hp

/-- The generic periodic-ODE argument, expressed directly for the actual
pinned partition. The sole analytic premise is the model's second response. -/
theorem pinnedKernel_axisC_of_response
    (edge : E → V × V) (b : E → ℝ) (pins cut : Finset V)
    (θ : V → ℝ) (hθ : ∀ v ∈ pins, θ v = if v ∈ cut then 1 else 0)
    (B : ℝ) (hB : 0 ≤ B) (τ : Configuration V)
    (hresponse : ∀ t : ℝ,
      -((pinnedSystem edge b pins τ).rotatePotential θ t).secondAxisResponse
        ((pinnedSystem edge b pins τ).edgeGradient θ)
        ((pinnedSystem edge b pins τ).edgeGradient θ) ≤ B)
    (t : ℝ) :
    (1-B*(4*Real.pi)^2/2) * pinnedKernel edge b pins (coordinateCut cut 2 t τ) ≤
      pinnedKernel edge b pins τ := by
  have hbinary : ∀ v s, (pinnedSystem edge b pins τ).pin v = some s →
      θ v = 0 ∨ θ v = 1 := by
    intro v s hs
    by_cases hv : v ∈ pins
    · rw [hθ v hv]
      split_ifs <;> simp
    · simp [pinnedSystem, hv] at hs
  have h := (pinnedSystem edge b pins τ).potential_partition_ratio θ B hB
    hbinary hresponse 0 t
  rw [pinnedSystem_rotatePotential_eq_cut edge b pins cut θ hθ τ 0,
    pinnedSystem_rotatePotential_eq_cut edge b pins cut θ hθ τ t,
    coordinateCut_zero, pinnedSystem_partition, pinnedSystem_partition] at h
  exact (le_div_iff₀ (pinnedPartition_pos edge b pins _)).mp h

/-- Convert a uniform response estimate into the quaternion comparison
required by the exact product bound. -/
theorem pinnedKernel_quaternion_of_response
    (edge : E → V × V) (b : E → ℝ) (pins cut : Finset V)
    (θ : V → ℝ) (hθ : ∀ v ∈ pins, θ v = if v ∈ cut then 1 else 0)
    (B : ℝ) (hB : 0 ≤ B) (hsmall : B*(4*Real.pi)^2/2 ≤ 1)
    (hresponse : ∀ (τ : Configuration V) (t : ℝ),
      -((pinnedSystem edge b pins τ).rotatePotential θ t).secondAxisResponse
        ((pinnedSystem edge b pins τ).edgeGradient θ)
        ((pinnedSystem edge b pins τ).edgeGradient θ) ≤ B)
    (g : Quaternion) (τ : Configuration V) :
    (1-3*(B*(4*Real.pi)^2/2)) * pinnedKernel edge b pins
      ((quaternionAction.onCut cut).move g τ) ≤ pinnedKernel edge b pins τ := by
  let K := fun υ => pinnedKernel edge b pins υ
  have hnonneg : ∀ υ, 0 ≤ K υ := fun υ => (pinnedPartition_pos _ _ _ υ).le
  have hglobal : ∀ h υ, K (globalMove h υ) = K υ := by
    intro h υ
    exact pinnedPartition_globalRotation _ _ _ h υ
  exact quaternionCut_comparison_of_axisC K hnonneg hglobal cut (by positivity) hsmall
    (fun t υ => pinnedKernel_axisC_of_response edge b pins cut θ hθ B hB υ
      (hresponse υ) t) g τ

end
end RP3
