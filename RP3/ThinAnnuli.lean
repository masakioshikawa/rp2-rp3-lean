module

public import RP3.ConcreteAnnuli

public section

/-! Integer square annuli with independently chosen inner and outer radii.
Every kernel edge has an endpoint in the strict interior. Boundary-only
edges remain in the base weight. No fixed ratio between radii is assumed. -/
namespace RP3
noncomputable section
open Finset MeasureTheory
open RP3.Fourier
open scoped Classical

namespace Fourier

@[expose] def thinAnnulusSites (R S : ℤ) (z : Site) : Set Site :=
  {v | R ≤ siteRadius z v ∧ siteRadius z v ≤ S}

namespace LatticeGraph

@[expose] def thinLayer (G : LatticeGraph) (R S : ℤ) (z : Site) : Finset G.vertices :=
  univ.filter (fun v => R < siteRadius z v.val ∧ siteRadius z v.val < S)

@[expose] def thinKernelEdges (G : LatticeGraph) (R S : ℤ) (z : Site) : Finset G.edges :=
  univ.filter (fun e => e.val.1 ∈ G.thinLayer R S z ∨ e.val.2 ∈ G.thinLayer R S z)

@[simp] theorem mem_thinLayer (G : LatticeGraph) (R S : ℤ) (z : Site) (v : G.vertices) :
    v ∈ G.thinLayer R S z ↔ R < siteRadius z v.val ∧ siteRadius z v.val < S := by
  simp [thinLayer]

@[simp] theorem mem_thinKernelEdges (G : LatticeGraph) (R S : ℤ) (z : Site) (e : G.edges) :
    e ∈ G.thinKernelEdges R S z ↔
      e.val.1 ∈ G.thinLayer R S z ∨ e.val.2 ∈ G.thinLayer R S z := by
  simp [thinKernelEdges]

theorem thinKernelEdges_endpoints (G : LatticeGraph) (R S : ℤ) (z : Site) (e : G.edges)
    (he : e ∈ G.thinKernelEdges R S z) :
    (R ≤ siteRadius z e.val.1.val ∧ siteRadius z e.val.1.val ≤ S) ∧
    (R ≤ siteRadius z e.val.2.val ∧ siteRadius z e.val.2.val ≤ S) := by
  have hn := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  simp only [mem_thinKernelEdges, mem_thinLayer] at he
  omega

theorem separated_thinKernelEdges (G : LatticeGraph) {R S T U : ℤ} (z : Site)
    (hsep : S ≤ T) : Disjoint (G.thinKernelEdges R S z) (G.thinKernelEdges T U z) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hn := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  simp only [mem_thinKernelEdges, mem_thinLayer] at he hf
  omega

theorem thinKernelEdges_avoid_smaller_interior (G : LatticeGraph) {R S T U : ℤ}
    (z : Site) (hsep : S ≤ T) (e : G.edges) (he : e ∈ G.thinKernelEdges T U z) :
    e.val.1 ∉ G.thinLayer R S z ∧ e.val.2 ∉ G.thinLayer R S z := by
  have hm := G.thinKernelEdges_endpoints T U z e he
  simp only [mem_thinLayer]
  omega

theorem thinKernelEdges_avoid_larger_interior (G : LatticeGraph) {R S T U : ℤ}
    (z : Site) (hsep : S ≤ T) (e : G.edges) (he : e ∈ G.thinKernelEdges R S z) :
    e.val.1 ∉ G.thinLayer T U z ∧ e.val.2 ∉ G.thinLayer T U z := by
  have hn := G.thinKernelEdges_endpoints R S z e he
  simp only [mem_thinLayer]
  omega

theorem thinKernelEdges_inside_larger_cut (G : LatticeGraph) {R S T : ℤ}
    (z : Site) (hsep : S ≤ T) (e : G.edges) (he : e ∈ G.thinKernelEdges R S z) :
    e.val.1 ∈ G.innerCut T z ∧ e.val.2 ∈ G.innerCut T z := by
  have hn := G.thinKernelEdges_endpoints R S z e he
  simp only [mem_innerCut]
  omega

theorem thinKernelEdges_outside_smaller_cut (G : LatticeGraph) {R S T U : ℤ}
    (z : Site) (hwidth : R < S) (hsep : S ≤ T)
    (e : G.edges) (he : e ∈ G.thinKernelEdges T U z) :
    e.val.1 ∉ G.innerCut R z ∧ e.val.2 ∉ G.innerCut R z := by
  have hm := G.thinKernelEdges_endpoints T U z e he
  simp only [mem_innerCut]
  omega

/-- Width two is enough: a nearest-neighbor edge crossing the inner cut has
an endpoint at radius `R+1`, in the strict interior. -/
theorem crossing_mem_thinKernelEdges (G : LatticeGraph) (R S : ℤ)
    (hwidth : R+2 ≤ S) (z : Site) (e : G.edges)
    (he : ¬(e.val.1 ∈ G.innerCut R z ↔ e.val.2 ∈ G.innerCut R z)) :
    e ∈ G.thinKernelEdges R S z := by
  have hn := siteRadius_neighbor_step z (Or.inl (G.nearest e.val e.property))
  simp only [mem_thinKernelEdges, mem_thinLayer]
  simp only [mem_innerCut] at he
  omega

theorem nonthinKernel_same_side (G : LatticeGraph) (R S : ℤ)
    (hwidth : R+2 ≤ S) (z : Site) (e : G.edges)
    (he : e ∉ G.thinKernelEdges R S z) :
    e.val.1 ∈ G.innerCut R z ↔ e.val.2 ∈ G.innerCut R z := by
  by_contra h
  exact he (G.crossing_mem_thinKernelEdges R S hwidth z e h)

/-- The annular product estimate remains valid when consecutive annuli share
only their pinned boundary. -/
theorem thin_square_annuli_product_bound {J : Type*} [Fintype J] [LinearOrder J]
    (G : LatticeGraph) (b : G.edges → ℝ) (R S : J → ℤ) (hR : ∀ i, 0 ≤ R i)
    (hwidth : ∀ i, R i+2 ≤ S i)
    (hsep : ∀ i j, i < j → S i ≤ R j)
    (x y : G.vertices) (hy : ∀ i, S i < siteRadius x.val y.val)
    (ε : J → ℝ) (hε : ∀ i, 0 < ε i)
    (hcompare : ∀ i (g : Quaternion) τ,
      (1 - ε i) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (R i) (S i) x.val) b) (G.thinLayer (R i) (S i) x.val)ᶜ
        ((quaternionAction.onCut (G.innerCut (R i) x.val)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (R i) (S i) x.val) b) (G.thinLayer (R i) (S i) x.val)ᶜ τ) :
    |correlation (fun e : G.edges => e.val) b x y| ≤ (3 : ℝ) / 4 * ∏ i, ε i := by
  classical
  let sets := fun i => G.thinKernelEdges (R i) (S i) x.val
  let pins := fun i => (G.thinLayer (R i) (S i) x.val)ᶜ
  let cuts := fun i => G.innerCut (R i) x.val
  have hleft (i : J) : x ∈ pins i := by
    simp only [pins, mem_compl, mem_thinLayer, siteRadius_self]
    have := hR i
    have := hwidth i
    omega
  have hright (i : J) : y ∈ pins i := by
    simp only [pins, mem_compl, mem_thinLayer]
    have := hy i
    omega
  apply concrete_kernel_product_bound (fun e : G.edges => e.val) b sets pins cuts
    x y ε
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact G.separated_thinKernelEdges x.val (hsep i j hij)
    · exact (G.separated_thinKernelEdges x.val (hsep j i hji)).symm
  · intro i j
    rcases le_total i j with hij | hji
    · left
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hij with rfl | hij
      · exact le_rfl
      · have := hsep i j hij
        have := hR i
        have := hwidth i
        omega
    · right
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hji with rfl | hji
      · exact le_rfl
      · have := hsep j i hji
        have := hR j
        have := hwidth j
        omega
  · intro i e
    by_cases he : ∃ j, e ∈ sets j
    · left
      simp [remainingCoupling, he]
    · right
      have hn : e ∉ sets i := fun hi => he ⟨i, hi⟩
      simpa only [sets, pins, mem_thinKernelEdges, not_or, mem_compl] using hn
  · intro i j hij e
    by_cases he : e ∈ sets j
    · right
      simp only [pins, mem_compl]
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact G.thinKernelEdges_avoid_smaller_interior x.val (hsep i j hij) e he
      · exact G.thinKernelEdges_avoid_larger_interior x.val (hsep j i hji) e he
    · left
      simp [maskedCoupling, he]
  · exact fun i => ⟨hleft i, hright i⟩
  · intro i e
    by_cases he : ∃ j, e ∈ sets j
    · left
      simp [remainingCoupling, he]
    · right
      exact G.nonthinKernel_same_side (R i) (S i) (hwidth i) x.val e (fun hi => he ⟨i,hi⟩)
  · intro i j hij e
    by_cases he : e ∈ sets j
    · right
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hn := G.thinKernelEdges_outside_smaller_cut (R := R i) (S := S i)
          (T := R j) (U := S j) x.val (by have := hwidth i; omega) (hsep i j hij) e he
        exact iff_of_false hn.1 hn.2
      · have hn := G.thinKernelEdges_inside_larger_cut x.val (hsep j i hji) e he
        exact iff_of_true hn.1 hn.2
    · left
      simp [maskedCoupling, he]
  · intro i
    simp only [cuts, mem_innerCut, siteRadius_self]
    have := hR i
    have := hwidth i
    have := hy i
    omega
  · exact hε
  · exact hcompare



end LatticeGraph
end Fourier
end
end RP3
