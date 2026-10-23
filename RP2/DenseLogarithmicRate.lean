import RP2.DenseRates

/-!
# The explicit logarithmic decay envelope

The factorial annular estimate has leading logarithm
`-log r * log (log r) / log 2`, with a uniform error bounded by a constant
times `log r`. This proves the quantitative clause of the decay theorem.
-/
namespace RP2

private theorem dense_log_factorial_lower (k : ℕ) (hk : 0 < k) :
    (k : ℝ) * Real.log k - k ≤ Real.log (k.factorial : ℝ) := by
  have h := Stirling.le_log_factorial_stirling (ne_of_gt hk)
  have hn := Real.log_natCast_nonneg k
  have hp : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  linarith

/-- The factorial annular envelope has the leading logarithmic term
with adjacent dyadic scales; `C` and the threshold may depend on `N` and `B` only. -/
theorem dense_factorial_annulus_logarithmic_bound (N : ℕ) (hN : 0 < N)
    (B : ℝ) (hB : 0 < B) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      (2 / 3 : ℝ) * B ^ denseAnnulusCount N r hN / (denseAnnulusCount N r hN).factorial ≤
        Real.exp (-Real.log (r : ℝ) * Real.log (Real.log (r : ℝ)) / Real.log 2 +
          C * Real.log (r : ℝ)) := by
  let q := Real.log 2
  let a := Real.log (2 * (N : ℝ))
  let d := |Real.log (2*q)|
  let t := |Real.log B| + 1
  let C := (t + d + a + t*q) / q
  let H := 2*a + 2*q + Real.exp d + 1
  have hq : 0 < q := Real.log_pos (by norm_num)
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have ha : 0 ≤ a := Real.log_nonneg (by nlinarith [hN1])
  have hd : 0 ≤ d := abs_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hC : 0 ≤ C := div_nonneg (by positivity) hq.le
  obtain ⟨R, hR⟩ := exists_nat_gt (Real.exp H)
  refine ⟨C, hC, R, ?_⟩
  intro r hr
  have hr' : Real.exp H < (r : ℝ) := hR.trans_le (Nat.cast_le.mpr hr)
  have hrpos : 0 < (r : ℝ) := (Real.exp_pos H).trans hr'
  let L := Real.log (r : ℝ)
  let k := denseAnnulusCount N r hN
  have hLH : H ≤ L := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos H) hr'.le
  have hL1 : 1 ≤ L := by dsimp [H] at hLH; nlinarith [Real.exp_pos d]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hLa : 2*a ≤ L := by dsimp [H] at hLH; nlinarith [Real.exp_pos d]
  have hLe : Real.exp d ≤ L := by dsimp [H] at hLH; linarith
  have hLloga : 0 ≤ Real.log L - d := by
    have h := Real.log_le_log (Real.exp_pos d) hLe
    rw [Real.log_exp] at h
    linarith
  have hcover : L ≤ a + (k : ℝ)*q := by
    have hc : (r : ℝ) ≤ 2 * (N : ℝ) * (2 : ℝ)^k := by
      exact_mod_cast denseAnnulusCount_cover N r hN
    have h := Real.log_le_log hrpos hc
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at h
    exact h
  have hkreal : 0 < (k : ℝ) := by
    have hLa' : a < L := by dsimp [H] at hLH; nlinarith [Real.exp_pos d]
    nlinarith
  have hk : 0 < k := by exact_mod_cast hkreal
  have hupper : (k : ℝ)*q ≤ L + q := by
    have hs : 2 * N * 2^(k-1) < r := denseAnnulusCount_inside N r hN (by omega)
    have hs' : 2 * (N : ℝ) * (2 : ℝ)^(k-1) < r := by exact_mod_cast hs
    have hl := Real.log_lt_log (by positivity) hs'
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hl
    have hc : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hc] at hl
    change a + ((k : ℝ)-1)*q < L at hl
    linarith
  have hlow : L / (2*q) ≤ (k : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*q)).2
    nlinarith
  have hklog : Real.log L - d ≤ Real.log (k : ℝ) := by
    have h := Real.log_le_log (div_pos hLpos (by positivity : 0 < 2*q)) hlow
    rw [Real.log_div hLpos.ne' (by positivity)] at h
    have hd' : Real.log (2*q) ≤ d := le_abs_self _
    linarith
  have hprod : (L-a)*(Real.log L-d) ≤ q * (k : ℝ) * Real.log (k : ℝ) := by
    calc
      _ ≤ (q*(k : ℝ)) * (Real.log L-d) :=
        mul_le_mul_of_nonneg_right (by nlinarith [hcover]) hLloga
      _ ≤ _ := mul_le_mul_of_nonneg_left hklog (by positivity)
  have hup : t * (q*(k : ℝ)) ≤ t * (L+q) :=
    mul_le_mul_of_nonneg_left (by nlinarith [hupper]) ht
  have hlogL : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    linarith
  have habsorb : a * Real.log L ≤ a * L := mul_le_mul_of_nonneg_left hlogL ha
  have hconstant : t*q ≤ t*q*L :=
    le_mul_of_one_le_right (mul_nonneg ht hq.le) hL1
  have hxpos : 0 < (2 / 3 : ℝ) * B^k / (k.factorial : ℝ) := by positivity
  apply (Real.log_le_iff_le_exp hxpos).1
  have hx : Real.log ((2 / 3 : ℝ) * B^k / (k.factorial : ℝ)) ≤
      t * (k : ℝ) - (k : ℝ)*Real.log (k : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have hf := dense_log_factorial_lower k hk
    have hb := mul_le_mul_of_nonneg_left (le_abs_self (Real.log B)) hkreal.le
    have h23 : Real.log (2 / 3 : ℝ) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    dsimp [t]
    linarith
  have he : -L * Real.log L / q + C*L =
      (-L * Real.log L + (t+d+a+t*q)*L) / q := by
    dsimp [C]
    ring
  change Real.log ((2 / 3 : ℝ) * B^k / (k.factorial : ℝ)) ≤ -L * Real.log L / q + C*L
  rw [he]
  apply (le_div_iff₀ hq).2
  have hqx := mul_le_mul_of_nonneg_left hx hq.le
  have had : 0 ≤ a*d := mul_nonneg ha hd
  nlinarith only [hqx, hprod, hup, habsorb, hconstant, had]


/-- Stronger unconditional factorial bound: every dyadic scale contributes. -/
theorem dense_factorial_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      let r := (Fourier.siteRadius x.val y.val).toNat
      let k := denseAnnulusCount (2^a) r (by positivity)
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (2:ℝ)/3 * D^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hcomparison⟩ :=
    Fourier.LatticeGraph.dyadic_kernel_comparison_signed β hβ
  exact ⟨D, hD, a, ha, fun G b hb x y =>
    Fourier.LatticeGraph.dense_factorial_of_dyadic_comparison_signed
      hD a ha hcomparison G b hb x y⟩

/-- The leading `log r * log (log r)` coefficient is doubled by retaining
adjacent annuli. The constants remain uniform over graph and signed couplings. -/
theorem dense_logarithmic_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      R ≤ (Fourier.siteRadius x.val y.val).toNat →
      |correlation (fun e : G.edges => e.val) b x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x.val y.val : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x.val y.val : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨D, hD, a, ha, hfactorial⟩ := dense_factorial_quadrupolar_decay_signed β hβ
  obtain ⟨C, hC, R, hlog⟩ := dense_factorial_annulus_logarithmic_bound
    (2^a) (by positivity) D hD
  refine ⟨C, hC, R, ?_⟩
  intro G b hb x y hr
  have hn : (((Fourier.siteRadius x.val y.val).toNat : ℕ) : ℝ) =
      (Fourier.siteRadius x.val y.val : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Fourier.siteRadius_nonneg x.val y.val)
  have h := (hfactorial G b hb x y).trans (hlog _ hr)
  simpa only [hn] using h

/-- Ferromagnetic specialization of the stronger factorial estimate. -/
theorem dense_factorial_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      let r := (Fourier.siteRadius x.val y.val).toNat
      let k := denseAnnulusCount (2^a) r (by positivity)
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (2:ℝ)/3 * D^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hbound⟩ := dense_factorial_quadrupolar_decay_signed β hβ
  exact ⟨D, hD, a, ha, fun G b hb x y => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y⟩

/-- Ferromagnetic specialization of the stronger logarithmic envelope. -/
theorem dense_logarithmic_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      R ≤ (Fourier.siteRadius x.val y.val).toNat →
      |correlation (fun e : G.edges => e.val) b x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x.val y.val : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x.val y.val : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := dense_logarithmic_quadrupolar_decay_signed β hβ
  exact ⟨C, hC, R, fun G b hb x y hr => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y hr⟩

end RP2
