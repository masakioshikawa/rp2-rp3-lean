import RP2.Rates

/-! Scope of the decay conclusion: exclusion of nonzero algebraic lower
bounds for this observable. This makes no assertion about other observables,
uniqueness, or an exponential mass gap. -/

namespace RP2

/-- Faster-than-power decay excludes an eventual algebraic lower bound.
The exponent is any real number, so logarithmically modified algebraic
asymptotics with nonzero amplitude are excluded as well once they imply a
lower bound at a slightly larger exponent. -/
theorem SuperpolynomialDecay.no_algebraic_lower_bound {C : ℕ → ℝ}
    (hC : SuperpolynomialDecay C) (p a : ℝ) (ha : 0 < a) (R : ℕ) :
    ∃ r : ℕ, R ≤ r ∧ |C r| < a * (1 + (r : ℝ)) ^ (-p) := by
  obtain ⟨A, hA, hbound⟩ := hC (⌈p⌉₊ + 1)
  obtain ⟨n, hn⟩ := exists_nat_gt (A / a)
  let r := max R n
  have hnr : (n : ℝ) ≤ r := by exact_mod_cast le_max_right R n
  have hx : (0 : ℝ) < 1 + r := by positivity
  have hp : (1 + (r : ℝ)) ^ p ≤ (1 + (r : ℝ)) ^ ⌈p⌉₊ := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le
      (by have := Nat.cast_nonneg (α := ℝ) r; linarith) (Nat.le_ceil p)
  have hrA : A < a * (1 + (r : ℝ)) := by
    have hnA : A < (n : ℝ) * a := (div_lt_iff₀ ha).mp hn
    nlinarith
  refine ⟨r, le_max_left R n, ?_⟩
  by_contra hnot
  have hlower : a * (1 + (r : ℝ)) ^ (-p) ≤ |C r| := le_of_not_gt hnot
  rw [Real.rpow_neg hx.le] at hlower
  have haC : a ≤ |C r| * (1 + (r : ℝ)) ^ p := by
    exact (div_le_iff₀ (Real.rpow_pos_of_pos hx p)).mp hlower
  have haNat : a ≤ |C r| * (1 + (r : ℝ)) ^ ⌈p⌉₊ :=
    haC.trans (mul_le_mul_of_nonneg_left hp (abs_nonneg _))
  have hmul := mul_le_mul_of_nonneg_right haNat hx.le
  have hb := hbound r
  rw [pow_succ, ← mul_assoc] at hb
  linarith

end RP2
