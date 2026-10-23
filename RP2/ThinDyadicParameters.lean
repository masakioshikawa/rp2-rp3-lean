import RP2.FourierAll

/-! Numerical conversion between integer dyadic shell widths and normalized
thin-annulus parameters. -/
namespace RP2.Fourier
noncomputable section

/-- The normalized width `2⁻ʰ` corresponds to the integer width `2^(n-h)`. -/
theorem thin_dyadic_width (n h : ℕ) (hh : h ≤ n) :
    (2:ℝ)^(n-h) = (1/(2:ℝ)^h)*(2:ℝ)^n := by
  have hp : (2:ℝ)^n = (2:ℝ)^h*(2:ℝ)^(n-h) := by
    rw [←pow_add, Nat.add_sub_of_le hh]
  rw [hp]
  field_simp

/-- All geometric and mesh hypotheses for a shell in a dyadic band. -/
theorem thin_dyadic_parameters (n h : ℕ) (hh : 2*h ≤ n) (hm : 4 ≤ n-h)
    (R : ℤ) (hR : (2:ℤ)^n ≤ R)
    (hS : R+(2:ℤ)^(n-h) ≤ 2*(2:ℤ)^n) :
    let a := (R:ℝ)/(2:ℝ)^n
    let δ := 1/(2:ℝ)^h
    let S := R+(2:ℤ)^(n-h)
    0 < δ ∧ δ ≤ 1 ∧ 1 ≤ a ∧ δ ≤ a ∧ a+δ ≤ 2 ∧
      1/(2:ℝ)^n ≤ δ/16 ∧ R < S ∧
      (R:ℝ) = a*(2:ℝ)^n ∧ (S:ℝ) = (a+δ)*(2:ℝ)^n := by
  dsimp only
  have hh' : h ≤ n := by omega
  have hN : 0 < (2:ℝ)^n := by positivity
  have hH : 0 < (2:ℝ)^h := by positivity
  have hδ : 0 < 1/(2:ℝ)^h := by positivity
  have hδ1 : 1/(2:ℝ)^h ≤ 1 := by
    exact (div_le_one hH).mpr (one_le_pow₀ (by norm_num))
  have hR' : (2:ℝ)^n ≤ (R:ℝ) := by exact_mod_cast hR
  have ha : 1 ≤ (R:ℝ)/(2:ℝ)^n := by rwa [le_div_iff₀ hN, one_mul]
  have hr : (R:ℝ) = (R:ℝ)/(2:ℝ)^n*(2:ℝ)^n := by field_simp
  have hw := thin_dyadic_width n h hh'
  have hs : ((R+(2:ℤ)^(n-h):ℤ):ℝ) =
      ((R:ℝ)/(2:ℝ)^n+1/(2:ℝ)^h)*(2:ℝ)^n := by
    push_cast
    rw [hw]
    calc _ = (R:ℝ)/(2:ℝ)^n*(2:ℝ)^n+(1/(2:ℝ)^h)*(2:ℝ)^n := by rw [←hr]
         _ = _ := by ring
  have htop : (R:ℝ)/(2:ℝ)^n+1/(2:ℝ)^h ≤ 2 := by
    apply (mul_le_mul_iff_left₀ hN).mp
    rw [←hs]
    have ht : ((R+(2:ℤ)^(n-h):ℤ):ℝ) ≤ 2*(2:ℝ)^n := by exact_mod_cast hS
    exact ht
  have h16 : (16:ℝ) ≤ (2:ℝ)^(n-h) := by
    calc (16:ℝ) = (2:ℝ)^4 := by norm_num
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) hm
  have hp : (2:ℝ)^n = (2:ℝ)^h*(2:ℝ)^(n-h) := by
    rw [←pow_add, Nat.add_sub_of_le hh']
  have hmesh : 1/(2:ℝ)^n ≤ (1/(2:ℝ)^h)/16 := by
    rw [div_div]
    apply one_div_le_one_div_of_le (by positivity)
    rw [hp]
    nlinarith
  refine ⟨hδ,hδ1,ha,hδ1.trans ha,htop,hmesh,?_,hr,hs⟩
  have hwpos : (0:ℤ) < 2^(n-h) := by positivity
  omega

/-- Convert the response estimate to the form used by dyadic scale selection. -/
theorem thin_dyadic_response_cost (n h : ℕ) (hm : 0 < n-h)
    (K V : ℝ) (hK : 0 ≤ K) (hV : 0 ≤ V) :
    K/(1/(2:ℝ)^h)/(n:ℝ) + V/(1/(2:ℝ)^h)^6/(2:ℝ)^n ≤
      K*(2:ℝ)^h/((n-h:ℕ):ℝ) + V*(2:ℝ)^(6*h)/(2:ℝ)^n := by
  have hnh : (0:ℝ) < (n-h:ℕ) := by exact_mod_cast hm
  have hn : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hle : ((n-h:ℕ):ℝ) ≤ n := by exact_mod_cast Nat.sub_le n h
  have hfirst : K/(1/(2:ℝ)^h)/(n:ℝ) ≤ K*(2:ℝ)^h/((n-h:ℕ):ℝ) := by
    rw [div_div_eq_mul_div, div_one]
    exact div_le_div_of_nonneg_left (by positivity) hnh hle
  have hsecond : V/(1/(2:ℝ)^h)^6/(2:ℝ)^n = V*(2:ℝ)^(6*h)/(2:ℝ)^n := by
    rw [div_pow, one_pow, div_div_eq_mul_div, div_one, Nat.mul_comm 6 h, pow_mul]
  exact add_le_add hfirst hsecond.le

end
end RP2.Fourier
