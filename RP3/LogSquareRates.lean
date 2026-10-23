module

public import RP3.DenseRates

public section

/-!
# From linearly many shells per scale to log-square decay

This file contains the arithmetic part of the thin-annulus argument.  Its
interfaces explicitly record the finite-volume shell bound; no comparison
estimate is postulated as an axiom.  In particular, the conversion from a
quadratic exponent in the number of dyadic bands to a log-square distance
bound holds at every distance, including zero.
-/
namespace RP3
noncomputable section
open Finset

/-- Number of thin annuli retained in the first `k` bands starting at `a`. -/
@[expose] def packedAnnulusCount (m : ℕ → ℕ) (a k : ℕ) : ℕ :=
  ∑ j ∈ range k, m (a+j)

private theorem sum_range_real_index (k : ℕ) :
    (∑ j ∈ range k, (j : ℝ)) = (k : ℝ) * (k-1) / 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- A linear number of shells in each band gives a quadratic cumulative
count.  The fixed loss `γ/4` makes the statement valid also for `k = 0,1`. -/
theorem packedAnnulusCount_quadratic (m : ℕ → ℕ) (a : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) (hm : ∀ j : ℕ, γ * (j : ℝ) ≤ m (a+j)) (k : ℕ) :
    γ * (k : ℝ)^2 / 4 - γ/4 ≤ (packedAnnulusCount m a k : ℝ) := by
  have hsum : γ * ((k : ℝ) * (k-1) / 2) ≤
      (packedAnnulusCount m a k : ℝ) := by
    calc
      _ = ∑ j ∈ range k, γ * (j : ℝ) := by
        rw [← mul_sum, sum_range_real_index]
      _ ≤ ∑ j ∈ range k, (m (a+j) : ℝ) :=
        sum_le_sum (fun j _ => hm j)
      _ = _ := by simp [packedAnnulusCount]
  have hsq := mul_nonneg hγ (sq_nonneg ((k : ℝ)-1))
  nlinarith

/-- The product of a common contraction `1/2` over the packed shells has a
Gaussian bound in the number of dyadic bands. -/
theorem packed_half_power_le (m : ℕ → ℕ) (a : ℕ) {γ : ℝ}
    (hγ : 0 ≤ γ) (hm : ∀ j : ℕ, γ * (j : ℝ) ≤ m (a+j)) (k : ℕ) :
    (1/2 : ℝ) ^ packedAnnulusCount m a k ≤
      Real.exp (Real.log 2 * γ / 4) *
        Real.exp (-(Real.log 2 * γ / 4) * (k : ℝ)^2) := by
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcount := packedAnnulusCount_quadratic m a hγ hm k
  have heq : (1/2 : ℝ) ^ packedAnnulusCount m a k =
      Real.exp (-(Real.log 2) * (packedAnnulusCount m a k : ℝ)) := by
    rw [← Real.exp_log (pow_pos (by norm_num : (0:ℝ)<1/2) _), Real.log_pow,
      Real.log_div (by norm_num) (by norm_num), Real.log_one]
    congr 1
    ring
  rw [heq, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hcount hq.le
  nlinarith

/-- The dyadic covering count controls `log (2+r)` uniformly at all
distances. -/
theorem denseAnnulusCount_log_distance (N r : ℕ) (hN : 0 < N) :
    Real.log (2+(r:ℝ)) ≤ Real.log (2*(N:ℝ)+2) +
      (denseAnnulusCount N r hN : ℝ) * Real.log 2 := by
  let k := denseAnnulusCount N r hN
  have hc : (r:ℝ) ≤ 2*(N:ℝ)*(2:ℝ)^k := by
    exact_mod_cast denseAnnulusCount_cover N r hN
  have hp : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num)
  have hb : 2+(r:ℝ) ≤ (2*(N:ℝ)+2)*(2:ℝ)^k := by nlinarith
  have hl := Real.log_le_log (by positivity : (0:ℝ)<2+r) hb
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
  exact hl

/-- A Gaussian in the dyadic covering count gives a log-square envelope.
The constants depend only on `N`, `B`, and `d`, and no distance threshold
is needed. -/
theorem gaussian_annulus_log_square_bound (N : ℕ) (hN : 0 < N)
    (B d : ℝ) (hB : 0 < B) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      B * Real.exp (-d * (denseAnnulusCount N r hN : ℝ)^2) ≤
        C * Real.exp (-c * (Real.log (2+(r:ℝ)))^2) := by
  let q := Real.log 2
  let a := Real.log (2*(N:ℝ)+2)
  let c := d/(2*q^2)
  let C := B*Real.exp (2*c*a^2)
  have hq : 0 < q := Real.log_pos (by norm_num)
  have ha : 0 ≤ a := Real.log_nonneg (by have hn := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hc : 0 < c := by dsimp [c]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, c, hc, ?_⟩
  intro r
  let k := denseAnnulusCount N r hN
  let L := Real.log (2+(r:ℝ))
  have hL : 0 ≤ L := Real.log_nonneg (by have hr := Nat.cast_nonneg (α := ℝ) r; linarith)
  have hLa : L ≤ a+(k:ℝ)*q := denseAnnulusCount_log_distance N r hN
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hs : L^2 ≤ 2*a^2+2*(k:ℝ)^2*q^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hLa)
      (show 0 ≤ a+(k:ℝ)*q+L by positivity)
    have hsq := sq_nonneg (a-(k:ℝ)*q)
    nlinarith
  have hcq : c * (2*q^2) = d := by
    dsimp [c]
    field_simp [ne_of_gt hq]
  have hs' := mul_le_mul_of_nonneg_left hs hc.le
  have he : -d*(k:ℝ)^2 ≤ 2*c*a^2-c*L^2 := by
    have hmul := congrArg (fun t : ℝ => t*(k:ℝ)^2) hcq
    nlinarith
  change B*Real.exp (-d*(k:ℝ)^2) ≤ C*Real.exp (-c*L^2)
  dsimp only [C]
  rw [mul_assoc, ← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using he)) hB.le

/-- Direct all-distance conversion for products of `1/2`, when the number
of shells in successive bands grows at least linearly. -/
theorem packed_annulus_log_square_bound (m : ℕ → ℕ) (a N : ℕ)
    (hN : 0 < N) {γ : ℝ} (hγ : 0 < γ)
    (hm : ∀ j : ℕ, γ * (j : ℝ) ≤ m (a+j)) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
      (3/4 : ℝ)*(1/2 : ℝ)^packedAnnulusCount m a (denseAnnulusCount N r hN) ≤
        C * Real.exp (-c * (Real.log (2+(r:ℝ)))^2) := by
  let d := Real.log 2 * γ / 4
  have hd : 0 < d := by
    dsimp [d]
    positivity
  obtain ⟨C, hC, c, hc, hbound⟩ := gaussian_annulus_log_square_bound N hN
    ((3/4)*Real.exp d) d (by positivity) hd
  refine ⟨C, hC, c, hc, ?_⟩
  intro r
  have hh := packed_half_power_le m a hγ.le hm (denseAnnulusCount N r hN)
  calc
    _ ≤ (3/4 : ℝ) * (Real.exp d *
          Real.exp (-d*(denseAnnulusCount N r hN : ℝ)^2)) := by
      exact mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = ((3/4)*Real.exp d) *
          Real.exp (-d*(denseAnnulusCount N r hN : ℝ)^2) := by ring
    _ ≤ _ := hbound r

end
end RP3
