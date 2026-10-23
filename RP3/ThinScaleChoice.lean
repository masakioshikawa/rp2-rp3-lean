import RP3.DenseRates

/-!
# An eventual dyadic choice for thin-annulus widths

All choices here are numerical.  The constants in the response estimate are
chosen before the lattice graph, its couplings, and its two marked sites.
-/

namespace RP3
noncomputable section
open Filter
open scoped Topology

/-- A polynomial remainder is eventually smaller than any positive tolerance. -/
theorem thin_polynomial_remainder_small (F : ℝ) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℕ, ∀ n : ℕ, a ≤ n → F * (n : ℝ)^p / (2 : ℝ)^n ≤ ε := by
  have ht : Tendsto (fun n : ℕ => F * (n : ℝ)^p / (2 : ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero, ← mul_div_assoc] using
      tendsto_const_nhds.mul (tendsto_pow_const_div_const_pow_of_one_lt p
        (by norm_num : (1 : ℝ) < 2))
  have he : ∀ᶠ n : ℕ in atTop, F * (n : ℝ)^p / (2 : ℝ)^n < ε :=
    ht.eventually (eventually_lt_nhds hε)
  obtain ⟨a, ha⟩ := eventually_atTop.1 he
  exact ⟨a, fun n hn => (ha n hn).le⟩

/-- The first dyadic scale reaching `n` has a matching strict lower bound. -/
theorem thin_scale_count_bounds (A n : ℕ) (hA : 0 < A) (hn : 2*A < n) :
    1 ≤ denseAnnulusCount A n hA ∧
      A * 2^denseAnnulusCount A n hA < n ∧
      n ≤ 2*A*2^denseAnnulusCount A n hA := by
  let h := denseAnnulusCount A n hA
  have hc : n ≤ 2*A*2^h := denseAnnulusCount_cover A n hA
  have hp : 1 ≤ h := by
    by_contra hp
    have hz : h = 0 := by omega
    simp only [hz, pow_zero, mul_one] at hc
    omega
  have hi := denseAnnulusCount_inside A n hA (j := h-1) (by dsimp [h] at hp ⊢; omega)
  have hh : h = h-1+1 := by omega
  have he : A*2^h = 2*A*2^(h-1) := by
    conv_lhs => rw [hh, pow_succ]
    ring
  exact ⟨hp, he.trans_lt hi, hc⟩

/-- The associated number `2^(h-1)` of disjoint layers is linear in `n`. -/
theorem thin_scale_layer_count (A n : ℕ) (hA : 0 < A) (hn : 2*A < n) :
    n ≤ 4*A*2^(denseAnnulusCount A n hA - 1) := by
  obtain ⟨hp, -, hc⟩ := thin_scale_count_bounds A n hA hn
  have hh : denseAnnulusCount A n hA = denseAnnulusCount A n hA-1+1 := by omega
  calc n ≤ 2*A*2^denseAnnulusCount A n hA := hc
    _ = 4*A*2^(denseAnnulusCount A n hA-1) := by
      conv_lhs => rw [hh, pow_succ]
      ring

/-- Choose dyadic widths so that the full thin-annulus comparison error is at
most one half, retaining a number of layers proportional to the scale index.
The constants `E,F` may already include the periodic and quaternion factors. -/
theorem thin_scale_choice (E F : ℝ) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    ∃ A a : ℕ, ∃ hA : 4 ≤ A, 8 ≤ a ∧ ∀ n : ℕ, a ≤ n →
      let h := denseAnnulusCount A n (by omega)
      1 ≤ h ∧ 2*h ≤ n ∧ 4 ≤ n-h ∧ A*2^h < n ∧ n ≤ 2*A*2^h ∧
        E*(2 : ℝ)^h/(n-h : ℕ) + F*(2 : ℝ)^(6*h)/(2 : ℝ)^n ≤ 1/2 := by
  obtain ⟨A, hAr⟩ := exists_nat_ge (max (4 : ℝ) (8*E))
  have hA4r : (4 : ℝ) ≤ A := (le_max_left _ _).trans hAr
  have hA4 : 4 ≤ A := by exact_mod_cast hA4r
  have hA8 : 8*E ≤ A := (le_max_right _ _).trans hAr
  have hA : 0 < A := by omega
  have hAp : (0 : ℝ) < A := by exact_mod_cast hA
  obtain ⟨a₀, ha₀⟩ := thin_polynomial_remainder_small F 6 (by norm_num : (0 : ℝ) < 1/4)
  let a := max (2*A+1) (max 8 a₀)
  refine ⟨A, a, hA4, ?_, ?_⟩
  · exact (le_max_left 8 a₀).trans (le_max_right _ _)
  intro n hn
  dsimp only
  let h := denseAnnulusCount A n hA
  have hnA : 2*A < n := by have := (le_max_left (2*A+1) (max 8 a₀)).trans hn; omega
  have hn8 : 8 ≤ n := ((le_max_left 8 a₀).trans (le_max_right (2*A+1) _)).trans hn
  have hna₀ : a₀ ≤ n := ((le_max_right 8 a₀).trans (le_max_right (2*A+1) _)).trans hn
  obtain ⟨hh1, hlow, hhigh⟩ := thin_scale_count_bounds A n hA hnA
  change 1 ≤ h at hh1
  change A*2^h < n at hlow
  change n ≤ 2*A*2^h at hhigh
  have hhpow : h < 2^h := Nat.lt_two_pow_self
  have hh2 : 2*h ≤ n := by
    have hm : 2*2^h ≤ A*2^h := Nat.mul_le_mul_right _ (by omega : 2 ≤ A)
    omega
  have hnh : 4 ≤ n-h := by omega
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnhp : (0 : ℝ) < (n-h : ℕ) := by exact_mod_cast (by omega : 0 < n-h)
  have hlowr : (A : ℝ)*(2 : ℝ)^h ≤ n := by exact_mod_cast hlow.le
  have hhalfr : (n : ℝ)/2 ≤ (n-h : ℕ) := by
    have hh2r : 2*(h : ℝ) ≤ n := by exact_mod_cast hh2
    rw [Nat.cast_sub (by omega : h ≤ n)]
    linarith
  have hfirst : E*(2 : ℝ)^h/(n-h : ℕ) ≤ 1/4 := by
    calc E*(2 : ℝ)^h/(n-h : ℕ) ≤ E*(2 : ℝ)^h/((n : ℝ)/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hhalfr
      _ ≤ 1/4 := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ)/2)).2
        have hm := mul_le_mul_of_nonneg_right hA8 (by positivity : 0 ≤ (2 : ℝ)^h)
        nlinarith
  have hpn : (2 : ℝ)^h ≤ n := by
    have hA1 : (1 : ℝ) ≤ A := by linarith
    exact (le_mul_of_one_le_left (by positivity) hA1).trans hlowr
  have hpower : (2 : ℝ)^(6*h) ≤ (n : ℝ)^6 := by
    rw [Nat.mul_comm 6 h, pow_mul]
    exact pow_le_pow_left₀ (by positivity) hpn 6
  have hsecond : F*(2 : ℝ)^(6*h)/(2 : ℝ)^n ≤ 1/4 := by
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpower hF)
      (by positivity)).trans (ha₀ n hna₀)
  refine ⟨hh1, hh2, hnh, hlow, hhigh, ?_⟩
  linarith

end
end RP3
