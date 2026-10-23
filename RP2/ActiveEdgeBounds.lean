import RP2.HighTemperature

/-! Elementary upper bounds for prescribed open edges and finite witness families.
No FKG property or stochastic-domination theorem is assumed. -/

namespace RP2.HighTemperature
noncomputable section
open Finset MeasureTheory
open scoped BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem sum_supersets_prod (f : E → ℝ) (S : Finset E) :
    (∑ A ∈ (univ : Finset E).powerset, if S ⊆ A then ∏ e ∈ A, f e else 0) =
      ∏ e : E, (f e + if e ∈ S then 0 else 1) := by
  classical
  rw [prod_add]
  apply sum_congr rfl
  intro A hA
  have hprod : (∏ e ∈ (univ : Finset E) \ A, (if e ∈ S then (0 : ℝ) else 1)) =
      if S ⊆ A then 1 else 0 := by
    simp_rw [show (fun e : E => if e ∈ S then (0 : ℝ) else 1) =
      (fun e => if e ∉ S then 1 else 0) by funext e; split_ifs <;> simp_all]
    rw [prod_boole]
    congr 1
    simp only [mem_sdiff, mem_univ, true_and]
    apply propext
    constructor
    · intro h e he
      by_contra hn
      exact h e hn he
    · intro h e hn he
      exact hn (h he)
  rw [hprod]
  split_ifs <;> simp

theorem sum_supersets_prod_le (f : E → ℝ) (S : Finset E) (p : ℝ)
    (hf : ∀ e, 0 ≤ f e) (hp : 0 ≤ p)
    (hopen : ∀ e, f e ≤ p * (1 + f e)) :
    (∑ A ∈ (univ : Finset E).powerset, if S ⊆ A then ∏ e ∈ A, f e else 0) ≤
      p ^ S.card * ∏ e : E, (1 + f e) := by
  classical
  rw [sum_supersets_prod]
  calc
    _ ≤ ∏ e : E, (if e ∈ S then p else 1) * (1 + f e) := by
      apply prod_le_prod₀
      · intro e _
        split_ifs <;> linarith [hf e]
      · intro e _
        by_cases he : e ∈ S
        · simpa [he] using hopen e
        · simp [he, add_comm]
    _ = _ := by
      rw [prod_mul_distrib]
      congr 1
      rw [prod_ite]
      simp

def prescribedMass (edge : E → V × V) (b : E → ℝ) (S : Finset E) : ℝ :=
  ∑ A ∈ (univ : Finset E).powerset, if S ⊆ A then
    (integralOnCompact (referenceLaw (V := V))).linear (activeWeight edge b A) else 0

theorem prescribedMass_le (edge : E → V × V) (b : E → ℝ) (β : ℝ)
    (hβ : 0 ≤ β) (hb : ∀ e, |b e| ≤ β) (S : Finset E) :
    prescribedMass edge b S ≤ (1 - Real.exp (-β)) ^ S.card *
      (integralOnCompact (referenceLaw (V := V))).linear (expandedWeight edge b) := by
  classical
  let I := integralOnCompact (referenceLaw (V := V))
  have hp : 0 ≤ 1 - Real.exp (-β) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  have hpoint := I.mono (f := ∑ A ∈ (univ : Finset E).powerset,
      if S ⊆ A then activeWeight edge b A else 0)
    (g := ((1 - Real.exp (-β)) ^ S.card) • expandedWeight edge b) (fun σ => by
      simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
        expandedWeight, ContinuousMap.prod_apply, ContinuousMap.add_apply,
        ContinuousMap.one_apply]
      have h := sum_supersets_prod_le (fun e => edgeActivity edge b e σ) S
        (1 - Real.exp (-β)) (fun e => edgeActivity_nonneg edge b e σ) hp
        (fun e => edgeActivity_le_opening_coefficient edge b e β (hb e) σ)
      simpa only [apply_ite (fun f : C(Configuration V, ℝ) => f σ),
        ContinuousMap.zero_apply, activeWeight, ContinuousMap.prod_apply] using h)
  simpa only [prescribedMass, map_sum, map_smul, smul_eq_mul, apply_ite I.linear, map_zero] using hpoint

theorem connectedMass_le_witness_sum (edge : E → V × V) (b : E → ℝ) (x y : V)
    (W : Finset (Finset E))
    (hW : ∀ A : Finset E, ActiveConnected edge A x y → ∃ S ∈ W, S ⊆ A) :
    connectedMass edge b x y ≤ ∑ S ∈ W, prescribedMass edge b S := by
  classical
  let I := integralOnCompact (referenceLaw (V := V))
  unfold connectedMass prescribedMass
  rw [sum_comm]
  apply sum_le_sum
  intro A hA
  have hn := I.nonneg (activeWeight edge b A) (activeWeight_nonneg edge b A)
  by_cases hc : ActiveConnected edge A x y
  · obtain ⟨S, hS, hSA⟩ := hW A hc
    simp only [hc, ite_true]
    apply le_trans ?_ (single_le_sum (fun T _ => by split_ifs <;> positivity) hS)
    simp [hSA]
  · simp only [hc, ite_false]
    exact sum_nonneg (fun S _ => by split_ifs <;> positivity)

theorem abs_correlation_le_witness_sum (edge : E → V × V) (b : E → ℝ)
    (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ e, |b e| ≤ β) (x y : V)
    (W : Finset (Finset E))
    (hW : ∀ A : Finset E, ActiveConnected edge A x y → ∃ S ∈ W, S ⊆ A) :
    |correlation edge b x y| ≤ (2 : ℝ) / 3 *
      ∑ S ∈ W, (1 - Real.exp (-β)) ^ S.card := by
  let Z := (integralOnCompact (referenceLaw (V := V))).linear (expandedWeight edge b)
  have hZ : 0 < Z := expanded_partition_pos edge b
  have hw := connectedMass_le_witness_sum edge b x y W hW
  have hs := sum_le_sum (fun S (_ : S ∈ W) => prescribedMass_le edge b β hβ hb S)
  rw [← sum_mul] at hs
  have hc := abs_correlation_le_connected_mass edge b x y
  apply hc.trans
  apply (div_le_iff₀ hZ).mpr
  nlinarith [hw.trans hs]

end
end RP2.HighTemperature
