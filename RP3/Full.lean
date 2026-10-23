module

public import RP3.KernelEstimate
public import RP3.UniformDecay
public import RP3.LogarithmicRate

public section

/-!
# Superpolynomial quadrupolar decay in the planar RP³ model

This entry point quantifies over every finite retained nearest-neighbor graph,
all real couplings with |bₑ| ≤ β, and both observation sites.  No annular estimate,
factorization certificate, or representation identity is a theorem parameter.
The observable is (nₓ·nᵧ)²−1/4, with normalized spherical reference measure.
-/
namespace RP3
noncomputable section

/-- The finite-volume superpolynomial bound, uniform in volume and couplings.
The integer radius is exactly the ℓ∞ distance of the lattice sites. -/
theorem superpolynomial_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        A * (1 + (Fourier.siteRadius x.val y.val : ℝ))^(-p) := by
  obtain ⟨D, hD, a, ha, hcomparison⟩ :=
    Fourier.LatticeGraph.dyadic_kernel_comparison_signed β hβ
  exact Fourier.LatticeGraph.uniform_decay_of_dyadic_comparison_signed hD a ha hcomparison p

/-- The stronger factorial estimate in the number of separated annuli. -/
theorem factorial_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      let r := (Fourier.siteRadius x.val y.val).toNat
      let k := annulusCount (2^a) r (by positivity)
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (3 : ℝ) / 4 * (D/2)^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hcomparison⟩ :=
    Fourier.LatticeGraph.dyadic_kernel_comparison_signed β hβ
  exact ⟨D, hD, a, ha, fun G b hb x y =>
    Fourier.LatticeGraph.factorial_of_dyadic_comparison_signed hD a ha hcomparison G b hb x y⟩

/-- The explicit uniform version of the logarithmic asymptotic (1.7). -/
theorem logarithmic_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      R ≤ (Fourier.siteRadius x.val y.val).toNat →
      |correlation (fun e : G.edges => e.val) b x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x.val y.val : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x.val y.val : ℝ)) / Real.log 4 +
          C * Real.log (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨D, hD, a, ha, hfactorial⟩ := factorial_quadrupolar_decay_signed β hβ
  obtain ⟨C, hC, R, hlog⟩ := factorial_annulus_logarithmic_bound
    (2^a) (by positivity) (D/2) (by positivity)
  refine ⟨C, hC, R, ?_⟩
  intro G b hb x y hr
  have hn : (((Fourier.siteRadius x.val y.val).toNat : ℕ) : ℝ) =
      (Fourier.siteRadius x.val y.val : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Fourier.siteRadius_nonneg x.val y.val)
  have h := (hfactorial G b hb x y).trans (hlog _ hr)
  simpa only [hn] using h


/-- Backwards-compatible ferromagnetic specialization of the signed theorem. -/
theorem superpolynomial_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        A * (1 + (Fourier.siteRadius x.val y.val : ℝ))^(-p) := by
  obtain ⟨A, hA, hbound⟩ := superpolynomial_quadrupolar_decay_signed β hβ p
  exact ⟨A, hA, fun G b hb x y => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y⟩

/-- Backwards-compatible ferromagnetic specialization of the signed theorem. -/
theorem factorial_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      let r := (Fourier.siteRadius x.val y.val).toNat
      let k := annulusCount (2^a) r (by positivity)
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (3 : ℝ) / 4 * (D/2)^k/k.factorial := by
  obtain ⟨D, hD, a, ha, hbound⟩ := factorial_quadrupolar_decay_signed β hβ
  exact ⟨D, hD, a, ha, fun G b hb x y => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y⟩

/-- Backwards-compatible ferromagnetic specialization of the signed theorem. -/
theorem logarithmic_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      R ≤ (Fourier.siteRadius x.val y.val).toNat →
      |correlation (fun e : G.edges => e.val) b x y| ≤
        Real.exp (-Real.log (Fourier.siteRadius x.val y.val : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x.val y.val : ℝ)) / Real.log 4 +
          C * Real.log (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := logarithmic_quadrupolar_decay_signed β hβ
  exact ⟨C, hC, R, fun G b hb x y hr => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y hr⟩
end
end RP3
