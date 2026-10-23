module

public import Mathlib

public section

/-!
# From annular products to decay faster than every power

This module is independent of the spin model. All bounds are explicit.
-/

namespace RP2

open Finset

/-- The elementary factorial bound for logarithmically improving annular factors. -/
theorem annular_product_le_factorial (ε : ℕ → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hε : ∀ j, 0 ≤ ε j) (hbound : ∀ j, ε j ≤ B / (j + 1)) (k : ℕ) :
    (∏ j ∈ range k, ε j) ≤ B ^ k / k.factorial := by
  calc
    (∏ j ∈ range k, ε j) ≤ ∏ j ∈ range k, B / ((j : ℝ) + 1) :=
      prod_le_prod₀ (fun j _ => hε j) (fun j _ => hbound j)
    _ = B ^ k / k.factorial := by
      rw [prod_div_distrib]
      simp only [prod_const, card_range]
      congr 1
      norm_cast
      exact prod_range_add_one_eq_factorial k

/-- A factorial in the number of scales beats any prescribed power of distance.
The hypothesis `1 + r ≤ a * q^k` records only the geometry of the chosen scales. -/
theorem factorial_weighted_bound {B a q r : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (k p : ℕ) (hscale : 1 + r ≤ a * q ^ k) :
    (B ^ k / k.factorial) * (1 + r) ^ p ≤
      a ^ p * Real.exp (B * q ^ p) := by
  calc
    (B ^ k / k.factorial) * (1 + r) ^ p ≤
        (B ^ k / k.factorial) * (a * q ^ k) ^ p := by gcongr
    _ = a ^ p * ((B * q ^ p) ^ k / k.factorial) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      rw [Nat.mul_comm k p]
      ring
    _ ≤ a ^ p * Real.exp (B * q ^ p) := by
      gcongr
      exact Real.pow_div_factorial_le_exp (B * q ^ p) (mul_nonneg hB (pow_nonneg hq _)) k

/-- Logarithmic annular errors have the factorial bound used in the note. -/
theorem log_factor_le {D L : ℝ} (hD : 0 ≤ D) (hL : Real.log 4 ≤ L) (j : ℕ) :
    D / (L + j * Real.log 4) ≤ (D / Real.log 4) / (j + 1) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hden : (j + 1) * Real.log 4 ≤ L + j * Real.log 4 := by nlinarith
  calc
    D / (L + j * Real.log 4) ≤ D / ((j + 1) * Real.log 4) :=
      div_le_div_of_nonneg_left hD (mul_pos hj hlog) hden
    _ = (D / Real.log 4) / (j + 1) := by rw [div_div, mul_comm]

/-- Number of disjoint scales `N, 4N, ...` whose outer radius is strictly below `r`.
Using a least integer avoids any convention concerning logarithmic rounding. -/
@[expose] noncomputable def annulusCount (N r : ℕ) (hN : 0 < N) : ℕ :=
  Nat.find (show ∃ k : ℕ, r ≤ 2 * N * 4 ^ k from
    ⟨r, (Nat.lt_pow_self (by norm_num : 1 < (4 : ℕ))).le.trans
      (Nat.le_mul_of_pos_left _ (by omega))⟩)

theorem annulusCount_cover (N r : ℕ) (hN : 0 < N) :
    r ≤ 2 * N * 4 ^ annulusCount N r hN := by
  unfold annulusCount
  exact Nat.find_spec (p := fun k => r ≤ 2 * N * 4 ^ k) _

theorem annulusCount_inside (N r : ℕ) (hN : 0 < N) {j : ℕ}
    (hj : j < annulusCount N r hN) : 2 * N * 4 ^ j < r := by
  unfold annulusCount at hj
  exact Nat.lt_of_not_ge (Nat.find_min (p := fun k => r ≤ 2 * N * 4 ^ k) _ hj)

theorem annulusCount_distance (N r : ℕ) (hN : 0 < N) :
    1 + (r : ℝ) ≤ (2 * N + 1) * (4 : ℝ) ^ annulusCount N r hN := by
  have hc : (r : ℝ) ≤ 2 * N * (4 : ℝ) ^ annulusCount N r hN := by
    exact_mod_cast annulusCount_cover N r hN
  have hp : (1 : ℝ) ≤ 4 ^ annulusCount N r hN := one_le_pow₀ (by norm_num)
  nlinarith

/-- A natural-exponent formulation; the next theorem includes arbitrary real exponents. -/
@[expose] def SuperpolynomialDecay (C : ℕ → ℝ) : Prop :=
  ∀ p : ℕ, ∃ A > 0, ∀ r : ℕ, |C r| * (1 + (r : ℝ)) ^ p ≤ A

/-- A factorial bound at geometric scales implies superpolynomial decay. -/
theorem superpolynomial_of_factorial {C : ℕ → ℝ} {M B : ℝ} (hM : 0 ≤ M)
    (hB : 0 ≤ B) (N : ℕ) (hN : 0 < N)
    (hC : ∀ r, |C r| ≤ M * B ^ annulusCount N r hN /
      (annulusCount N r hN).factorial) : SuperpolynomialDecay C := by
  intro p
  let A := M * (2 * (N : ℝ) + 1) ^ p * Real.exp (B * (4 : ℝ) ^ p)
  refine ⟨A + 1, by dsimp [A]; positivity, ?_⟩
  intro r
  have hb := factorial_weighted_bound hB
    (show 0 ≤ 2 * (N : ℝ) + 1 by positivity) (by norm_num : (0 : ℝ) ≤ 4)
    (Nat.cast_nonneg r) (annulusCount N r hN) p (annulusCount_distance N r hN)
  calc
    |C r| * (1 + (r : ℝ)) ^ p ≤
        M * ((B ^ annulusCount N r hN /
          (annulusCount N r hN).factorial) * (1 + (r : ℝ)) ^ p) := by
      calc
        _ ≤ (M * B ^ annulusCount N r hN /
            (annulusCount N r hN).factorial) * (1 + (r : ℝ)) ^ p := by
          gcongr
          exact hC r
        _ = _ := by ring
    _ ≤ A := by dsimp [A]; nlinarith [mul_le_mul_of_nonneg_left hb hM]
    _ ≤ A + 1 := by linarith

/-- The same conclusion in the conventional `A (1+r)^(-p)` form, for real `p`. -/
theorem SuperpolynomialDecay.real_bound {C : ℕ → ℝ} (h : SuperpolynomialDecay C)
    (p : ℝ) : ∃ A > 0, ∀ r : ℕ, |C r| ≤ A * (1 + (r : ℝ)) ^ (-p) := by
  obtain ⟨A, hA, hbound⟩ := h ⌈p⌉₊
  refine ⟨A, hA, ?_⟩
  intro r
  have hx : (0 : ℝ) < 1 + r := by positivity
  have hexp : (1 + (r : ℝ)) ^ p ≤ (1 + (r : ℝ)) ^ ⌈p⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) r; linarith) (Nat.le_ceil p)
  have hw : |C r| * (1 + (r : ℝ)) ^ p ≤ A :=
    (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)).trans (hbound r)
  rw [Real.rpow_neg hx.le]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hx p)).2 hw

end RP2
