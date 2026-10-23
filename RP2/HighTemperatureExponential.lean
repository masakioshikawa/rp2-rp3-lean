module

public import RP2.HighTemperatureDecay
public import RP2.NonbacktrackingPaths

public section

/-! Genuine, unconditional exponential decay for bounded signed couplings
at `β < log (3/2)`, with the same finite-volume constants in free local limits.
The proof is the positive active-edge expansion and simple-path prefix counting.
No two-dimensional percolation theorem or stochastic-domination axiom is used. -/

namespace RP2.HighTemperature
noncomputable section
open Finset
open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Prefix counting avoids a geometric-series loss in the prefactor. -/
theorem abs_correlation_le_nonbacktracking_pow (edge : E → V × V)
    (hi : Function.Injective (fun e => s((edge e).1, (edge e).2)))
    (hd : ∀ v, Fintype.card ((fullGraph edge).neighborSet v) ≤ 4)
    (b : E → ℝ) (β : ℝ) (hβ : 0 ≤ β) (hb : ∀ e, |b e| ≤ β)
    (n : ℕ) (x y : V)
    (hlen : ∀ p : (fullGraph edge).Walk x y, n ≤ p.length) :
    |correlation edge b x y| ≤ (8 : ℝ) / 9 * (3 * (1 - Real.exp (-β))) ^ n := by
  cases n with
  | zero =>
    simpa only [pow_zero, mul_one] using
      (abs_correlation_le edge b x y).trans (by norm_num : (2 : ℝ) / 3 ≤ 8 / 9)
  | succ n =>
    let p := 1 - Real.exp (-β)
    have hp : 0 ≤ p := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
    have hsum : (∑ S ∈ pathWitnesses edge (n+1) x, p ^ S.card) =
        (pathWitnesses edge (n+1) x).card * p ^ (n+1) := by
      rw [sum_congr rfl (fun S hS => by rw [card_mem_pathWitnesses edge hi (n+1) x S hS])]
      simp
    have hcard : ((pathWitnesses edge (n+1) x).card : ℝ) ≤ 4 * (3 : ℝ) ^ n := by
      exact_mod_cast pathWitnesses_card_le_nonbacktracking edge hd n x
    have hc := abs_correlation_le_witness_sum edge b β hβ hb x y
      (pathWitnesses edge (n+1) x) (connected_has_pathWitness edge hi (n+1) x y hlen)
    change |correlation edge b x y| ≤ (2 : ℝ) / 3 *
      (∑ S ∈ pathWitnesses edge (n+1) x, p ^ S.card) at hc
    rw [hsum] at hc
    apply hc.trans
    change (2 : ℝ) / 3 * ((pathWitnesses edge (n+1) x).card * p ^ (n+1)) ≤
      (8 : ℝ) / 9 * (3 * p) ^ (n+1)
    calc
      _ ≤ (2 : ℝ) / 3 * ((4 * (3 : ℝ) ^ n) * p ^ (n+1)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcard (pow_nonneg hp _)) (by norm_num)
      _ = _ := by rw [mul_pow, pow_succ (3 : ℝ)]; ring

end
end RP2.HighTemperature

namespace RP2
noncomputable section
open MeasureTheory Finset
open scoped BigOperators Classical

/-- The elementary nonbacktracking estimate holds even outside its decay regime. -/
theorem nonbacktracking_quadrupolar_bound_signed (β : ℝ) (hβ : 0 ≤ β)
    (G : Fourier.LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (x y : G.vertices) :
    |correlation (fun e : G.edges => e.val) b x y| ≤ (8 : ℝ) / 9 *
      (3 * (1 - Real.exp (-β))) ^ (Fourier.siteRadius x.val y.val).toNat := by
  apply HighTemperature.abs_correlation_le_nonbacktracking_pow
    (HighTemperature.Lattice.edge G) (HighTemperature.Lattice.edgeSym_injective G)
    (HighTemperature.Lattice.degree_le_four G) b β hβ hb
    (Fourier.siteRadius x.val y.val).toNat x y
  intro p
  exact Int.toNat_le.mpr (HighTemperature.Lattice.radius_le_walk_length G p)

/-- A positive, explicit mass and a uniform exponential bound for the actual
signed RP² model. The harmless floor in the mass includes β=0. -/
theorem elementary_exponential_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β)
    (hhigh : β < Real.log ((3 : ℝ) / 2)) :
    0 < HighTemperature.elementaryMass β ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (8 : ℝ) / 9 * Real.exp (-HighTemperature.elementaryMass β *
          (Fourier.siteRadius x.val y.val : ℝ)) := by
  refine ⟨HighTemperature.elementaryMass_pos β hhigh, ?_⟩
  intro G b hb x y
  have hp : 0 ≤ 3 * (1 - Real.exp (-β)) := by
    have h := Real.exp_le_one_iff.mpr (show -β ≤ 0 by linarith)
    positivity
  have hr : ((Fourier.siteRadius x.val y.val).toNat : ℝ) =
      (Fourier.siteRadius x.val y.val : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Fourier.siteRadius_nonneg x.val y.val)
  apply (nonbacktracking_quadrupolar_bound_signed β hβ G b hb x y).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    _ ≤ HighTemperature.elementaryDecayBase β ^ (Fourier.siteRadius x.val y.val).toNat :=
      pow_le_pow_left₀ hp (le_max_right _ _) _
    _ = _ := by rw [HighTemperature.elementaryDecayBase_pow, hr]

/-- Ferromagnetic specialization of the elementary exponential theorem. -/
theorem elementary_exponential_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β)
    (hhigh : β < Real.log ((3 : ℝ) / 2)) :
    0 < HighTemperature.elementaryMass β ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (8 : ℝ) / 9 * Real.exp (-HighTemperature.elementaryMass β *
          (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨hm, hbound⟩ := elementary_exponential_quadrupolar_decay_signed β hβ hhigh
  refine ⟨hm, fun G b hb => hbound G b ?_⟩
  intro e
  rw [abs_of_nonneg (hb e).1]
  exact (hb e).2

/-- The direct prefix bound passes to every stated signed free-boundary local limit. -/
theorem nonbacktracking_quadrupolar_bound_local_limit_signed (β : ℝ) (hβ : 0 ≤ β)
    (μ : ProbabilityMeasure InfiniteConfiguration) (hμ : IsSignedFreeBoundaryLocalLimit β μ)
    (x y : Fourier.Site) :
    |infiniteCorrelation μ x y| ≤ (8 : ℝ) / 9 *
      (3 * (1 - Real.exp (-β))) ^ (Fourier.siteRadius x y).toNat := by
  obtain ⟨G,b,hb,hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => (8 : ℝ) / 9 * (3 * (1 - Real.exp (-β))) ^ (Fourier.siteRadius x y).toNat)
    (fun n u v _ => nonbacktracking_quadrupolar_bound_signed β hβ (G n) (b n) (hb n) u v)
    x y trivial

/-- The exponential mass is unchanged in every signed free-boundary local limit. -/
theorem elementary_exponential_quadrupolar_decay_local_limit_signed
    (β : ℝ) (hβ : 0 ≤ β) (hhigh : β < Real.log ((3 : ℝ) / 2)) :
    0 < HighTemperature.elementaryMass β ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsSignedFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      |infiniteCorrelation μ x y| ≤ (8 : ℝ) / 9 *
        Real.exp (-HighTemperature.elementaryMass β * (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨hm,hbound⟩ := elementary_exponential_quadrupolar_decay_signed β hβ hhigh
  refine ⟨hm, ?_⟩
  intro μ hμ x y
  obtain ⟨G,b,hb,hlocal⟩ := hμ
  exact hlocal.correlation_bound (fun _ _ => True)
    (fun x y => (8 : ℝ) / 9 * Real.exp (-HighTemperature.elementaryMass β *
      (Fourier.siteRadius x y : ℝ)))
    (fun n u v _ => hbound (G n) (b n) (hb n) u v) x y trivial

/-- Ferromagnetic local limits obey the same elementary exponential bound. -/
theorem elementary_exponential_quadrupolar_decay_local_limit
    (β : ℝ) (hβ : 0 ≤ β) (hhigh : β < Real.log ((3 : ℝ) / 2)) :
    0 < HighTemperature.elementaryMass β ∧
      ∀ μ : ProbabilityMeasure InfiniteConfiguration,
      IsFreeBoundaryLocalLimit β μ → ∀ x y : Fourier.Site,
      |infiniteCorrelation μ x y| ≤ (8 : ℝ) / 9 *
        Real.exp (-HighTemperature.elementaryMass β * (Fourier.siteRadius x y : ℝ)) := by
  obtain ⟨hm,hbound⟩ := elementary_exponential_quadrupolar_decay_local_limit_signed β hβ hhigh
  exact ⟨hm, fun μ hμ => hbound μ hμ.signed⟩

end
end RP2
