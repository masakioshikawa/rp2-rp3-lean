import RP2.SquareRates

/-! Uniform real-exponent decay from the concrete dyadic kernel estimate. -/
namespace RP2.Fourier.LatticeGraph
noncomputable section

/-- A uniform factorial estimate gives decay of every real polynomial order.
The admissibility predicate is arbitrary: this step uses no coupling sign. -/
theorem uniform_decay_of_factorial_bound
    {P : (G : LatticeGraph) → (G.edges → ℝ) → Prop} {D : ℝ} (hD : 0 < D)
    (a : ℕ)
    (hfactorial : ∀ (G : LatticeGraph) (b : G.edges → ℝ), P G b →
      ∀ (x y : G.vertices),
      let r := (siteRadius x.val y.val).toNat
      let k := annulusCount (2^a) r (by positivity)
      |RP2.correlation (fun e : G.edges => e.val) b x y| ≤
        (2:ℝ)/3 * (D/2)^k/k.factorial) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),
      P G b → ∀ (x y : G.vertices),
      |RP2.correlation (fun e : G.edges => e.val) b x y| ≤
        A * (1 + (siteRadius x.val y.val : ℝ))^(-p) := by
  let q := ⌈p⌉₊
  let B := D/2
  let c := 2*(2^a:ℕ)+1
  let A := (2:ℝ)/3 * (c:ℝ)^q * Real.exp (B*(4:ℝ)^q)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1, by linarith, ?_⟩
  intro G b hb x y
  let r := (siteRadius x.val y.val).toNat
  let k := annulusCount (2^a) r (by positivity)
  have hbound := hfactorial G b hb x y
  change |RP2.correlation (fun e : G.edges => e.val) b x y| ≤
    (2:ℝ)/3 * B^k/k.factorial at hbound
  have hscale : 1+(r:ℝ) ≤ (c:ℝ)*(4:ℝ)^k := by
    simpa only [c, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
      annulusCount_distance (2^a) r (by positivity)
  have hw := factorial_weighted_bound (B := B) (a := (c:ℝ)) (q := (4:ℝ))
    (r := (r:ℝ)) (by dsimp [B]; positivity) (by positivity) (by norm_num)
    (Nat.cast_nonneg r) k q hscale
  have hnat : |RP2.correlation (fun e : G.edges => e.val) b x y| *
      (1+(r:ℝ))^q ≤ A := by
    calc
      _ ≤ ((2:ℝ)/3 * B^k/k.factorial) * (1+(r:ℝ))^q := by
        gcongr
      _ = (2:ℝ)/3 * ((B^k/k.factorial)*(1+(r:ℝ))^q) := by ring
      _ ≤ (2:ℝ)/3 * ((c:ℝ)^q * Real.exp (B*(4:ℝ)^q)) := by gcongr
      _ = A := by dsimp [A]; ring
  have hx : (0:ℝ) < 1+r := by positivity
  have hexp : (1+(r:ℝ))^p ≤ (1+(r:ℝ))^q := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le
      (by have := Nat.cast_nonneg (α := ℝ) r; linarith) (Nat.le_ceil p)
  have hreal : |RP2.correlation (fun e : G.edges => e.val) b x y| *
      (1+(r:ℝ))^p ≤ A+1 := by
    apply (mul_le_mul_of_nonneg_left hexp (abs_nonneg _)).trans
    linarith
  have hr : (r:ℝ) = (siteRadius x.val y.val:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (siteRadius_nonneg x.val y.val)
  rw [← hr, Real.rpow_neg hx.le]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hx p)).2 hreal


/-- Uniformity is in the order of the quantifiers: the constant is selected
before the graph, all its couplings, and both sites. -/
theorem uniform_decay_of_dyadic_comparison_signed {β D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (hcomp : SignedDyadicKernelComparison β D a) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |RP2.correlation (fun e : G.edges => e.val) b x y| ≤
        A * (1 + (siteRadius x.val y.val : ℝ))^(-p) := by
  exact uniform_decay_of_factorial_bound hD a
    (fun G b hb x y => factorial_of_dyadic_comparison_signed hD a ha hcomp G b hb x y) p

/-- Uniformity is in the order of the quantifiers: the constant is selected
before the graph, all its couplings, and both sites. -/
theorem uniform_decay_of_dyadic_comparison {β D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (hcomp : DyadicKernelComparison β D a) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      |RP2.correlation (fun e : G.edges => e.val) b x y| ≤
        A * (1 + (siteRadius x.val y.val : ℝ))^(-p) := by
  exact uniform_decay_of_factorial_bound hD a
    (fun G b hb x y => factorial_of_dyadic_comparison hD a ha hcomp G b hb x y) p

end
end RP2.Fourier.LatticeGraph
