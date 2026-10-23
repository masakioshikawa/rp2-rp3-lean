module

public import RP2.ActivePaths
public import RP2.DenseLimits

public section

/-! Unconditional exponential decay by elementary active-edge path counting.
This module does not use the sharper, external square-lattice FK theorem. -/
namespace RP2.HighTemperature
noncomputable section
open Finset
open RP2.Fourier
open scoped BigOperators Classical

namespace Lattice

@[expose] def edge (G : LatticeGraph) : G.edges → G.vertices × G.vertices := fun e => e.val

theorem edgeSym_injective (G : LatticeGraph) :
    Function.Injective (fun e : G.edges => s((edge G e).1, (edge G e).2)) := by
  intro e f h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have he := G.nearest e.val e.property
    have hf := G.nearest f.val f.property
    have h1 : e.val.1.val = f.val.2.val := congrArg Subtype.val h.1
    have h2 : e.val.2.val = f.val.1.val := congrArg Subtype.val h.2
    simp only [PositiveNeighbor] at he hf
    rcases he with he | he <;> rcases hf with hf | hf <;>
      have hx := congrArg Prod.fst h1 <;> have hy := congrArg Prod.snd h1 <;>
      have hx' := congrArg Prod.fst h2 <;> have hy' := congrArg Prod.snd h2 <;>
      omega

theorem adjacency_neighbor (G : LatticeGraph) {x y : G.vertices}
    (h : (fullGraph (edge G)).Adj x y) :
    PositiveNeighbor x.val y.val ∨ PositiveNeighbor y.val x.val := by
  obtain ⟨_,e,_,he⟩ := h
  have hn := G.nearest e.val e.property
  rcases Sym2.eq_iff.mp he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · left
    change e.val.1 = _ at hl
    change e.val.2 = _ at hr
    simpa only [hl, hr] using hn
  · right
    change e.val.1 = _ at hl
    change e.val.2 = _ at hr
    simpa only [hl, hr] using hn

@[expose] def fourNeighbors (x : Site) : Finset Site :=
  {(x.1+1,x.2), (x.1-1,x.2), (x.1,x.2+1), (x.1,x.2-1)}

theorem mem_fourNeighbors {x y : Site}
    (h : PositiveNeighbor x y ∨ PositiveNeighbor y x) : y ∈ fourNeighbors x := by
  simp only [fourNeighbors, mem_insert, mem_singleton]
  rcases h with h | h <;> rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Or.inr (Or.inl (Prod.ext h1 h2)))
  · exact Or.inr (Or.inl (Prod.ext (by omega) (by omega)))
  · exact Or.inr (Or.inr (Or.inr (Prod.ext (by omega) (by omega))))

theorem card_fourNeighbors_le (x : Site) : (fourNeighbors x).card ≤ 4 := by
  unfold fourNeighbors
  exact (card_insert_le _ _).trans (Nat.succ_le_succ ((card_insert_le _ _).trans
    (Nat.succ_le_succ ((card_insert_le _ _).trans (by simp)))))

theorem degree_le_four (G : LatticeGraph) (x : G.vertices) :
    Fintype.card ((fullGraph (edge G)).neighborSet x) ≤ 4 := by
  let f : (fullGraph (edge G)).neighborSet x → fourNeighbors x.val := fun y =>
    ⟨y.val.val, mem_fourNeighbors (adjacency_neighbor G y.property)⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    have hv := congrArg (fun z : fourNeighbors x.val => z.val) h
    exact hv
  have hc := Fintype.card_le_of_injective f hi
  exact hc.trans (by simpa only [Fintype.card_coe] using card_fourNeighbors_le x.val)

theorem radius_le_walk_length (G : LatticeGraph) {x y : G.vertices}
    (p : (fullGraph (edge G)).Walk x y) : siteRadius x.val y.val ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    have ht := siteRadius_triangle u.val v.val w.val
    have hn : siteRadius u.val v.val = 1 := by
      rcases adjacency_neighbor G h with h | h
      · exact siteRadius_neighbor h
      · rw [siteRadius_symm]; exact siteRadius_neighbor h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

/-- Signed finite-volume bound, uniform over all retained square-lattice graphs. -/
theorem abs_correlation_le_four_opening_pow (G : LatticeGraph) (b : G.edges → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ e, |b e| ≤ β) (x y : G.vertices) :
    |correlation (edge G) b x y| ≤ (2 : ℝ) / 3 *
      (4 * (1 - Real.exp (-β))) ^ (siteRadius x.val y.val).toNat := by
  apply abs_correlation_le_degree_pow (edge G) (edgeSym_injective G) 4
    (degree_le_four G) b β hβ hb (siteRadius x.val y.val).toNat x y
  intro p
  exact Int.toNat_le.mpr (radius_le_walk_length G p)

end Lattice

/-- A harmless floor keeps the displayed mass finite also at zero coupling. -/
@[expose] def elementaryDecayBase (β : ℝ) : ℝ := max (1 / 2) (3 * (1 - Real.exp (-β)))

@[expose] def elementaryMass (β : ℝ) : ℝ := -Real.log (elementaryDecayBase β)

theorem elementaryDecayBase_pos (β : ℝ) : 0 < elementaryDecayBase β :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem three_opening_lt_one (β : ℝ) (hβ : β < Real.log ((3 : ℝ) / 2)) :
    3 * (1 - Real.exp (-β)) < 1 := by
  have hexp : Real.exp β < (3 : ℝ) / 2 := by
    have h := Real.exp_lt_exp.mpr hβ
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] using h
  have hprod : Real.exp β * Real.exp (-β) = 1 := by rw [← Real.exp_add]; simp
  have hp := Real.exp_pos (-β)
  nlinarith

theorem elementaryDecayBase_lt_one (β : ℝ) (hβ : β < Real.log ((3 : ℝ) / 2)) :
    elementaryDecayBase β < 1 := by
  exact max_lt (by norm_num) (three_opening_lt_one β hβ)

theorem elementaryMass_pos (β : ℝ) (hβ : β < Real.log ((3 : ℝ) / 2)) :
    0 < elementaryMass β := by
  exact neg_pos.mpr (Real.log_neg (elementaryDecayBase_pos β)
    (elementaryDecayBase_lt_one β hβ))

theorem elementaryDecayBase_pow (β : ℝ) (n : ℕ) :
    elementaryDecayBase β ^ n = Real.exp (-elementaryMass β * n) := by
  simp only [elementaryMass, neg_neg]
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (elementaryDecayBase_pos β)]

end
end RP2.HighTemperature
