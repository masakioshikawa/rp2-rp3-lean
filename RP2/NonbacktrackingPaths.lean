module

public import RP2.ActivePaths

public section

/-! Sharper path counting: after the first step a simple path has at most
three choices on a graph of maximum degree four. -/
namespace RP2.HighTemperature
noncomputable section
open Finset
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Simple paths of a fixed length avoiding one specified vertex. -/
@[expose] def avoidingPaths (H : SimpleGraph V) (prev : V) (n : ℕ) (x y : V) :
    Finset (H.Walk x y) :=
  (H.finsetWalkLength n x y).filter (fun p => p.IsPath ∧ prev ∉ p.support)

theorem avoidingPaths_step_subset (H : SimpleGraph V) (prev : V) (n : ℕ) (x y : V) :
    avoidingPaths H prev (n+1) x y ⊆
      (univ.filter (fun z : H.neighborSet x => z.val ≠ prev)).biUnion
        (fun z => (avoidingPaths H x n z y).map
          ⟨fun p => SimpleGraph.Walk.cons z.property p, fun _ _ => by intro h; cases h; rfl⟩) := by
  intro p hp
  obtain ⟨hlen, hpath, hprev⟩ := mem_filter.mp hp
  rw [SimpleGraph.mem_finsetWalkLength_iff] at hlen
  cases p with
  | nil => simp at hlen
  | cons h p =>
    rename_i z
    have hp' := (SimpleGraph.Walk.cons_isPath_iff h p).mp hpath
    have hz : z ≠ prev := by
      intro hz
      apply hprev
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
      exact Or.inr (hz ▸ p.start_mem_support)
    apply mem_biUnion.mpr
    refine ⟨⟨z, h⟩, by simpa using hz, ?_⟩
    apply mem_map.mpr
    refine ⟨p, ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨?_, hp'⟩
    rw [SimpleGraph.mem_finsetWalkLength_iff]
    simpa using hlen

theorem simplePaths_step_subset (H : SimpleGraph V) (n : ℕ) (x y : V) :
    ((H.finsetWalkLength (n+1) x y).filter SimpleGraph.Walk.IsPath) ⊆
      univ.biUnion (fun z : H.neighborSet x =>
        (avoidingPaths H x n z y).map
          ⟨fun p => SimpleGraph.Walk.cons z.property p, fun _ _ => by intro h; cases h; rfl⟩) := by
  intro p hp
  obtain ⟨hlen, hpath⟩ := mem_filter.mp hp
  rw [SimpleGraph.mem_finsetWalkLength_iff] at hlen
  cases p with
  | nil => simp at hlen
  | cons h p =>
    rename_i z
    apply mem_biUnion.mpr
    refine ⟨⟨z,h⟩, mem_univ _, ?_⟩
    apply mem_map.mpr
    refine ⟨p, ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨?_, (SimpleGraph.Walk.cons_isPath_iff h p).mp hpath⟩
    rw [SimpleGraph.mem_finsetWalkLength_iff]
    simpa using hlen

/-- One neighbor is unavailable after arriving from `prev`. -/
theorem next_neighbors_card_le (H : SimpleGraph V)
    (hd : ∀ v, Fintype.card (H.neighborSet v) ≤ 4) (x prev : V)
    (hprev : H.Adj x prev) :
    (univ.filter (fun z : H.neighborSet x => z.val ≠ prev)).card ≤ 3 := by
  have heq : univ.filter (fun z : H.neighborSet x => z.val ≠ prev) =
      (univ : Finset (H.neighborSet x)).erase ⟨prev,hprev⟩ := by
    ext z
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    exact not_congr (show (z.val = prev) ↔ z = ⟨prev,hprev⟩ from
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩)
  rw [heq, card_erase_of_mem (mem_univ _), card_univ]
  have := hd x
  omega

/-- Number of continuations after an incoming edge, summed over all endpoints. -/
theorem avoidingPaths_count_le (H : SimpleGraph V)
    (hd : ∀ v, Fintype.card (H.neighborSet v) ≤ 4) (n : ℕ) (x prev : V)
    (hprev : H.Adj x prev) :
    ∑ y : V, (avoidingPaths H prev n x y).card ≤ 3^n := by
  induction n generalizing x prev with
  | zero =>
    calc
      _ ≤ ∑ y : V, (H.finsetWalkLength 0 x y).card := by
        exact sum_le_sum (fun y _ => card_filter_le _ _)
      _ ≤ 3^0 := by simpa using total_walk_count_le H 4 hd 0 x
  | succ n ih =>
    let Z := univ.filter (fun z : H.neighborSet x => z.val ≠ prev)
    calc
      _ ≤ ∑ y : V, ∑ z ∈ Z, (avoidingPaths H x n z y).card := by
        apply sum_le_sum
        intro y _
        apply (card_le_card (avoidingPaths_step_subset H prev n x y)).trans
        exact card_biUnion_le |>.trans_eq (by simp only [card_map, Z])
      _ = ∑ z ∈ Z, ∑ y : V, (avoidingPaths H x n z y).card := sum_comm
      _ ≤ ∑ z ∈ Z, 3^n := by
        apply sum_le_sum
        intro z hz
        exact ih z x z.property.symm
      _ ≤ 3^(n+1) := by
        simp only [sum_const, smul_eq_mul, pow_succ]
        have hc : Z.card ≤ 3 := next_neighbors_card_le H hd x prev hprev
        exact (Nat.mul_le_mul_right _ hc).trans_eq (Nat.mul_comm _ _)

/-- At most four first steps and three choices at each later step. -/
theorem simplePaths_count_le (H : SimpleGraph V)
    (hd : ∀ v, Fintype.card (H.neighborSet v) ≤ 4) (n : ℕ) (x : V) :
    ∑ y : V, ((H.finsetWalkLength (n+1) x y).filter SimpleGraph.Walk.IsPath).card ≤
      4*3^n := by
  calc
    _ ≤ ∑ y : V, ∑ z : H.neighborSet x, (avoidingPaths H x n z y).card := by
      apply sum_le_sum
      intro y _
      apply (card_le_card (simplePaths_step_subset H n x y)).trans
      exact card_biUnion_le |>.trans_eq (by simp only [card_map])
    _ = ∑ z : H.neighborSet x, ∑ y : V, (avoidingPaths H x n z y).card := sum_comm
    _ ≤ ∑ z : H.neighborSet x, 3^n := by
      exact sum_le_sum (fun z _ => avoidingPaths_count_le H hd n z x z.property.symm)
    _ ≤ 4*3^n := by
      simp only [sum_const, card_univ, smul_eq_mul]
      exact Nat.mul_le_mul_right _ (hd x)

/-- Refined finite witness count on graphs of maximum degree four. -/
theorem pathWitnesses_card_le_nonbacktracking (edge : E → V × V)
    (hd : ∀ v, Fintype.card ((fullGraph edge).neighborSet v) ≤ 4)
    (n : ℕ) (x : V) :
    (pathWitnesses edge (n+1) x).card ≤ 4*3^n := by
  apply (card_biUnion_le).trans
  apply le_trans (sum_le_sum (fun y _ => card_image_le))
  exact simplePaths_count_le (fullGraph edge) hd n x

/-- Version indexed by a positive path length. -/
theorem pathWitnesses_card_le_nonbacktracking_pos (edge : E → V × V)
    (hd : ∀ v, Fintype.card ((fullGraph edge).neighborSet v) ≤ 4)
    (n : ℕ) (hn : 0 < n) (x : V) :
    (pathWitnesses edge n x).card ≤ 4*3^(n-1) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa using pathWitnesses_card_le_nonbacktracking edge hd m x

end
end RP2.HighTemperature
