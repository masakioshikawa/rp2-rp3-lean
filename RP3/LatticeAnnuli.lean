module

public import RP3.FourierAll
public import RP3.Model

public section

/-!
# Edge allocation for nested square annuli

Annular edges are exactly those having at least one endpoint in the strict
interior.  Boundary-only edges stay in the ordinary weight.  These definitions
allow missing vertices, missing edges, and empty annuli.
-/

namespace RP3
noncomputable section
open Finset
open RP3.Fourier
open scoped Classical

namespace Fourier.LatticeGraph

@[expose] def strictLayer (G : LatticeGraph) (N : ℤ) (z : Site) : Finset G.vertices :=
  univ.filter (fun v => N < siteRadius z v.val ∧ siteRadius z v.val < 2*N)

@[expose] def innerCut (G : LatticeGraph) (N : ℤ) (z : Site) : Finset G.vertices :=
  univ.filter (fun v => siteRadius z v.val ≤ N)

@[expose] def kernelEdges (G : LatticeGraph) (N : ℤ) (z : Site) : Finset G.edges :=
  univ.filter (fun e => e.val.1 ∈ G.strictLayer N z ∨ e.val.2 ∈ G.strictLayer N z)

@[simp] theorem mem_strictLayer (G : LatticeGraph) (N : ℤ) (z : Site) (v : G.vertices) :
    v ∈ G.strictLayer N z ↔ N < siteRadius z v.val ∧ siteRadius z v.val < 2*N := by
  simp [strictLayer]

@[simp] theorem mem_innerCut (G : LatticeGraph) (N : ℤ) (z : Site) (v : G.vertices) :
    v ∈ G.innerCut N z ↔ siteRadius z v.val ≤ N := by
  simp [innerCut]

@[simp] theorem mem_kernelEdges (G : LatticeGraph) (N : ℤ) (z : Site) (e : G.edges) :
    e ∈ G.kernelEdges N z ↔
      e.val.1 ∈ G.strictLayer N z ∨ e.val.2 ∈ G.strictLayer N z := by
  simp [kernelEdges]

theorem kernelEdges_endpoints (G : LatticeGraph) (N : ℤ) (z : Site) (e : G.edges)
    (he : e ∈ G.kernelEdges N z) :
    (N ≤ siteRadius z e.val.1.val ∧ siteRadius z e.val.1.val ≤ 2*N) ∧
    (N ≤ siteRadius z e.val.2.val ∧ siteRadius z e.val.2.val ≤ 2*N) := by
  have hn := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  simp only [mem_kernelEdges, mem_strictLayer] at he
  omega

theorem innerCut_mono (G : LatticeGraph) {N M : ℤ} (z : Site) (h : N ≤ M) :
    G.innerCut N z ⊆ G.innerCut M z := by
  intro v hv
  exact (mem_innerCut G M z v).mpr (((mem_innerCut G N z v).mp hv).trans h)

theorem separated_kernelEdges (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N < M) : Disjoint (G.kernelEdges N z) (G.kernelEdges M z) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hn := G.kernelEdges_endpoints N z e he
  have hm := G.kernelEdges_endpoints M z e hf
  omega

theorem kernelEdges_avoid_smaller_interior (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N < M) (e : G.edges) (he : e ∈ G.kernelEdges M z) :
    e.val.1 ∉ G.strictLayer N z ∧ e.val.2 ∉ G.strictLayer N z := by
  have hm := G.kernelEdges_endpoints M z e he
  simp only [mem_strictLayer]
  omega

theorem kernelEdges_avoid_larger_interior (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N < M) (e : G.edges) (he : e ∈ G.kernelEdges N z) :
    e.val.1 ∉ G.strictLayer M z ∧ e.val.2 ∉ G.strictLayer M z := by
  have hn := G.kernelEdges_endpoints N z e he
  simp only [mem_strictLayer]
  omega

theorem kernelEdges_inside_larger_cut (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N < M) (e : G.edges) (he : e ∈ G.kernelEdges N z) :
    e.val.1 ∈ G.innerCut M z ∧ e.val.2 ∈ G.innerCut M z := by
  have hn := G.kernelEdges_endpoints N z e he
  simp only [mem_innerCut]
  omega

theorem kernelEdges_outside_smaller_cut (G : LatticeGraph) {N M : ℤ} (hN : 0 ≤ N)
    (z : Site) (hNM : 2*N < M) (e : G.edges) (he : e ∈ G.kernelEdges M z) :
    e.val.1 ∉ G.innerCut N z ∧ e.val.2 ∉ G.innerCut N z := by
  have hm := G.kernelEdges_endpoints M z e he
  simp only [mem_innerCut]
  omega

/-- Adjacent dyadic annuli may share their boundary: nearest-neighbor edges
cannot meet both strict interiors across that boundary. -/
theorem separated_kernelEdges_le (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N ≤ M) : Disjoint (G.kernelEdges N z) (G.kernelEdges M z) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hn := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  simp only [mem_kernelEdges, mem_strictLayer] at he hf
  omega

theorem kernelEdges_avoid_smaller_interior_le (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N ≤ M) (e : G.edges) (he : e ∈ G.kernelEdges M z) :
    e.val.1 ∉ G.strictLayer N z ∧ e.val.2 ∉ G.strictLayer N z := by
  have hm := G.kernelEdges_endpoints M z e he
  simp only [mem_strictLayer]
  omega

theorem kernelEdges_avoid_larger_interior_le (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N ≤ M) (e : G.edges) (he : e ∈ G.kernelEdges N z) :
    e.val.1 ∉ G.strictLayer M z ∧ e.val.2 ∉ G.strictLayer M z := by
  have hn := G.kernelEdges_endpoints N z e he
  simp only [mem_strictLayer]
  omega

theorem kernelEdges_inside_larger_cut_le (G : LatticeGraph) {N M : ℤ} (z : Site)
    (hNM : 2*N ≤ M) (e : G.edges) (he : e ∈ G.kernelEdges N z) :
    e.val.1 ∈ G.innerCut M z ∧ e.val.2 ∈ G.innerCut M z := by
  have hn := G.kernelEdges_endpoints N z e he
  simp only [mem_innerCut]
  omega

theorem kernelEdges_outside_smaller_cut_le (G : LatticeGraph) {N M : ℤ} (hN : 0 < N)
    (z : Site) (hNM : 2*N ≤ M) (e : G.edges) (he : e ∈ G.kernelEdges M z) :
    e.val.1 ∉ G.innerCut N z ∧ e.val.2 ∉ G.innerCut N z := by
  have hm := G.kernelEdges_endpoints M z e he
  simp only [mem_innerCut]
  omega

/-- An edge that crosses the inner cut belongs to that annular kernel. -/
theorem crossing_mem_kernelEdges (G : LatticeGraph) (N : ℤ) (hN : 2 ≤ N)
    (z : Site) (e : G.edges)
    (he : ¬(e.val.1 ∈ G.innerCut N z ↔ e.val.2 ∈ G.innerCut N z)) :
    e ∈ G.kernelEdges N z := by
  have hn := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  simp only [mem_kernelEdges, mem_strictLayer]
  simp only [mem_innerCut] at he
  omega

/-- A boundary-only edge omitted from an annulus cannot cross its inner cut. -/
theorem nonkernel_same_side (G : LatticeGraph) (N : ℤ) (hN : 2 ≤ N)
    (z : Site) (e : G.edges) (he : e ∉ G.kernelEdges N z) :
    e.val.1 ∈ G.innerCut N z ↔ e.val.2 ∈ G.innerCut N z := by
  by_contra h
  exact he (G.crossing_mem_kernelEdges N hN z e h)

end Fourier.LatticeGraph

section MaskedInteractions
variable {V E J : Type*} [Fintype V] [Fintype E] [Fintype J]

@[expose] def maskedCoupling (s : Finset E) (b : E → ℝ) : E → ℝ :=
  fun e => if e ∈ s then b e else 0

@[expose] def remainingCoupling (sets : J → Finset E) (b : E → ℝ) : E → ℝ :=
  fun e => if ∃ j, e ∈ sets j then 0 else b e

theorem coupling_partition (sets : J → Finset E)
    (hd : Pairwise (fun i j => Disjoint (sets i) (sets j))) (b : E → ℝ) (e : E) :
    b e = remainingCoupling sets b e + ∑ j, maskedCoupling (sets j) b e := by
  classical
  by_cases he : ∃ j, e ∈ sets j
  · obtain ⟨i, hi⟩ := he
    have hz (j : J) (hji : j ≠ i) : maskedCoupling (sets j) b e = 0 := by
      have hn : e ∉ sets j := by
        intro hj
        exact Finset.disjoint_left.mp (hd hji) hj hi
      simp [maskedCoupling, hn]
    rw [Finset.sum_eq_single i (fun j _ hji => hz j hji) (by simp)]
    simp [remainingCoupling, maskedCoupling, hi, show ∃ j, e ∈ sets j from ⟨i, hi⟩]
  · have hn (j : J) : e ∉ sets j := fun h => he ⟨j,h⟩
    simp [remainingCoupling, maskedCoupling, he, hn]

/-- Exact allocation of the squared interaction, with no lost boundary edges. -/
theorem interaction_partition (edge : E → V × V) (sets : J → Finset E)
    (hd : Pairwise (fun i j => Disjoint (sets i) (sets j)))
    (b : E → ℝ) (σ : Configuration V) :
    interaction edge b σ = interaction edge (remainingCoupling sets b) σ +
      ∑ j, interaction edge (maskedCoupling (sets j) b) σ := by
  classical
  unfold interaction
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_mul, ← add_mul, ← coupling_partition sets hd b e]

/-- The raw Gibbs weight is a product before the interiors are integrated. -/
theorem weight_partition (edge : E → V × V) (sets : J → Finset E)
    (hd : Pairwise (fun i j => Disjoint (sets i) (sets j))) (b : E → ℝ) :
    weight edge b = weight edge (remainingCoupling sets b) *
      ∏ j, weight edge (maskedCoupling (sets j) b) := by
  classical
  ext σ
  change Real.exp (interaction edge b σ) = _
  rw [interaction_partition edge sets hd b σ, Real.exp_add, Real.exp_sum]
  simp [weight]

end MaskedInteractions
end
end RP3
