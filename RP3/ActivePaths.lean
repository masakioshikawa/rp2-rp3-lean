module

public import RP3.ActiveEdgeBounds
public import RP3.FourierAll

public section

/-! Finite simple-path witnesses for the positive active-edge expansion. -/
namespace RP3.HighTemperature
noncomputable section
open Finset
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

@[expose] def activeGraph (edge : E → V × V) (A : Finset E) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ∃ e ∈ A, s((edge e).1, (edge e).2) = s(x,y)
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    obtain ⟨e, he, hp⟩ := h.2
    exact ⟨e, he, hp.trans Sym2.eq_swap⟩⟩
  loopless := ⟨by intro x; simp⟩

@[expose] def fullGraph (edge : E → V × V) : SimpleGraph V := activeGraph edge univ

theorem activeGraph_le_full (edge : E → V × V) (A : Finset E) :
    activeGraph edge A ≤ fullGraph edge := by
  rintro x y ⟨hne,e,he,hpair⟩
  exact ⟨hne,e,mem_univ _,hpair⟩

theorem activeConnected_reachable (edge : E → V × V) (A : Finset E) (x y : V)
    (hc : ActiveConnected edge A x y) : (activeGraph edge A).Reachable x y := by
  by_contra hn
  apply hc
  refine ⟨univ.filter (fun v => (activeGraph edge A).Reachable x v), ?_, ?_, ?_⟩
  · simp
  · simpa using hn
  · intro e he
    have hr : (activeGraph edge A).Reachable (edge e).1 (edge e).2 := by
      by_cases hd : (edge e).1 = (edge e).2
      · rw [hd]
      · exact SimpleGraph.Adj.reachable ⟨hd,e,he,rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => h.trans hr, fun h => h.trans hr.symm⟩

@[expose] def adjacencyEdge (edge : E → V × V) {x y : V} (h : (fullGraph edge).Adj x y) : E :=
  Classical.choose h.2

theorem adjacencyEdge_spec (edge : E → V × V) {x y : V}
    (h : (fullGraph edge).Adj x y) :
    s((edge (adjacencyEdge edge h)).1, (edge (adjacencyEdge edge h)).2) = s(x,y) :=
  (Classical.choose_spec h.2).2

@[expose] def walkEdgeSet (edge : E → V × V) {x y : V} : (fullGraph edge).Walk x y → Finset E
  | .nil => ∅
  | .cons h p => insert (adjacencyEdge edge h) (walkEdgeSet edge p)

theorem mem_walkEdgeSet_iff (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2)))
    {x y : V} (p : (fullGraph edge).Walk x y) (e : E) :
    e ∈ walkEdgeSet edge p ↔ s((edge e).1, (edge e).2) ∈ p.edges := by
  induction p with
  | nil => simp [walkEdgeSet]
  | @cons u v w h p ih =>
    simp only [walkEdgeSet, mem_insert, SimpleGraph.Walk.edges_cons, List.mem_cons, ih]
    rw [← adjacencyEdge_spec edge h]
    exact or_congr hi.eq_iff.symm Iff.rfl

theorem card_walkEdgeSet (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2)))
    {x y : V} (p : (fullGraph edge).Walk x y) (hp : p.IsTrail) :
    (walkEdgeSet edge p).card = p.length := by
  induction p with
  | nil => simp [walkEdgeSet]
  | cons h p ih =>
    obtain ⟨hp, hn⟩ := (SimpleGraph.Walk.isTrail_cons h p).mp hp
    have he : adjacencyEdge edge h ∉ walkEdgeSet edge p := by
      rw [mem_walkEdgeSet_iff edge hi p, adjacencyEdge_spec]
      exact hn
    simp [walkEdgeSet, he, ih hp]

theorem walkEdgeSet_subset_of_active (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2))) (A : Finset E)
    {x y : V} (p : (activeGraph edge A).Walk x y) :
    walkEdgeSet edge (p.mapLe (activeGraph_le_full edge A)) ⊆ A := by
  intro e he
  rw [mem_walkEdgeSet_iff edge hi, SimpleGraph.Walk.edges_mapLe_eq_edges] at he
  have hAdj := p.adj_of_mem_edges he
  obtain ⟨_, f, hf, hsym⟩ := hAdj
  have hef : e = f := hi hsym.symm
  simpa only [hef] using hf

/-- The total number of length-n walks is bounded by the maximum degree to power n. -/
theorem total_walk_count_le (H : SimpleGraph V) [DecidableRel H.Adj]
    (D : ℕ) (hd : ∀ v, Fintype.card (H.neighborSet v) ≤ D) (n : ℕ) (x : V) :
    ∑ y : V, (H.finsetWalkLength n x y).card ≤ D ^ n := by
  induction n generalizing x with
  | zero =>
    have heq (y : V) : (H.finsetWalkLength 0 x y).card = if y = x then 1 else 0 := by
      by_cases h : x = y
      · subst y; simp [SimpleGraph.finsetWalkLength]
      · simp [SimpleGraph.finsetWalkLength, h, Ne.symm h]
    simp [heq]
  | succ n ih =>
    calc
      _ ≤ ∑ y : V, ∑ z : H.neighborSet x, (H.finsetWalkLength n z y).card := by
        apply sum_le_sum
        intro y _
        simp only [SimpleGraph.finsetWalkLength]
        apply (card_biUnion_le).trans
        simp only [card_map]
        rfl
      _ = ∑ z : H.neighborSet x, ∑ y : V, (H.finsetWalkLength n z y).card := sum_comm
      _ ≤ ∑ z : H.neighborSet x, D ^ n := sum_le_sum (fun z _ => ih z)
      _ ≤ D ^ (n+1) := by
        simp only [sum_const, card_univ, smul_eq_mul, pow_succ]
        exact Nat.mul_le_mul_right _ (hd x) |>.trans_eq (Nat.mul_comm _ _)

@[expose] def pathWitnesses (edge : E → V × V) (n : ℕ) (x : V) : Finset (Finset E) :=
  univ.biUnion (fun y => ((fullGraph edge).finsetWalkLength n x y).filter
    SimpleGraph.Walk.IsPath |>.image (walkEdgeSet edge))

theorem mem_pathWitnesses (edge : E → V × V) (n : ℕ) (x : V) (S : Finset E) :
    S ∈ pathWitnesses edge n x ↔
      ∃ y, ∃ p : (fullGraph edge).Walk x y, p.length = n ∧ p.IsPath ∧ walkEdgeSet edge p = S := by
  simp only [pathWitnesses, mem_biUnion, mem_univ, true_and, mem_image,
    mem_filter, SimpleGraph.mem_finsetWalkLength_iff]
  tauto

theorem pathWitnesses_card_le (edge : E → V × V) (D : ℕ)
    (hd : ∀ v, Fintype.card ((fullGraph edge).neighborSet v) ≤ D) (n : ℕ) (x : V) :
    (pathWitnesses edge n x).card ≤ D ^ n := by
  apply (card_biUnion_le).trans
  apply le_trans (sum_le_sum (fun y _ => (card_image_le).trans (card_filter_le _ _)))
  exact total_walk_count_le (fullGraph edge) D hd n x

theorem card_mem_pathWitnesses (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2)))
    (n : ℕ) (x : V) (S : Finset E) (hS : S ∈ pathWitnesses edge n x) : S.card = n := by
  obtain ⟨y,p,hlen,hpath,rfl⟩ := (mem_pathWitnesses edge n x S).mp hS
  exact (card_walkEdgeSet edge hi p hpath.isTrail).trans hlen

theorem connected_has_pathWitness (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2)))
    (n : ℕ) (x y : V)
    (hlen : ∀ p : (fullGraph edge).Walk x y, n ≤ p.length)
    (A : Finset E) (hc : ActiveConnected edge A x y) :
    ∃ S ∈ pathWitnesses edge n x, S ⊆ A := by
  obtain ⟨p, hp⟩ := (activeConnected_reachable edge A x y hc).exists_isPath
  let q := p.take n
  let q' := q.mapLe (activeGraph_le_full edge A)
  have hnp : n ≤ p.length := by simpa using hlen (p.mapLe (activeGraph_le_full edge A))
  refine ⟨walkEdgeSet edge q', ?_, walkEdgeSet_subset_of_active edge hi A q⟩
  apply (mem_pathWitnesses edge n x _).mpr
  refine ⟨p.getVert n, q', ?_, (hp.take n).mapLe _, rfl⟩
  simp [q', q, SimpleGraph.Walk.take_length, Nat.min_eq_left hnp]

/-- A complete exponential bound in graph distance, using at most D choices per step. -/
theorem abs_correlation_le_degree_pow (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2)))
    (D : ℕ) (hd : ∀ v, Fintype.card ((fullGraph edge).neighborSet v) ≤ D)
    (b : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ e, |b e| ≤ β) (n : ℕ) (x y : V)
    (hlen : ∀ p : (fullGraph edge).Walk x y, n ≤ p.length) :
    |correlation edge b x y| ≤ (3 : ℝ) / 4 * (D * (1 - Real.exp (-β))) ^ n := by
  have hp : 0 ≤ 1 - Real.exp (-β) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  apply (abs_correlation_le_witness_sum edge b β hβ hb x y (pathWitnesses edge n x)
    (connected_has_pathWitness edge hi n x y hlen)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ = (pathWitnesses edge n x).card * (1 - Real.exp (-β)) ^ n := by
      rw [sum_congr rfl (fun S hS => by rw [card_mem_pathWitnesses edge hi n x S hS])]
      simp
    _ ≤ (D ^ n : ℕ) * (1 - Real.exp (-β)) ^ n := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
      exact_mod_cast pathWitnesses_card_le edge D hd n x
    _ = _ := by simp only [Nat.cast_pow, mul_pow]

end
end RP3.HighTemperature
