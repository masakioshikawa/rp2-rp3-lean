import RP3.Averaging
import RP3.Rates

/-!
# Conditional conclusion of the annular argument

`AnnularData` is an explicit certificate for the factorised model. Its fields
are proof obligations, not axioms.  In particular, `lower` is the analytic
annular estimate, and `cross`/`base_fixed` are the locality/symmetry obligations.
This file does not claim those fields have been constructed for RP³.
-/

namespace RP3

open Finset

variable {Ω : Type*} [TopologicalSpace Ω]

/-- Data after integrating out the strict interiors of `k` annuli. -/
structure AnnularData (Ω : Type*) [TopologicalSpace Ω] (k : ℕ) (D L : ℝ) where
  integral : PositiveIntegral Ω
  system : AveragingSystem integral ℕ
  kernels : ℕ → C(Ω, ℝ)
  base : C(Ω, ℝ)
  obs : C(Ω, ℝ)
  kernel_nonneg : ∀ i ∈ range k, ∀ x, 0 ≤ kernels i x
  base_nonneg : ∀ x, 0 ≤ base x
  lower : ∀ i ∈ range k, ∀ x,
    (1 - D / (L + i * Real.log 4)) * system.avg i (kernels i) x ≤ kernels i x
  cross : ∀ i ∈ range k, ∀ j ∈ range k, i ≠ j → system.avg i (kernels j) = kernels j
  base_fixed : ∀ i ∈ range k, system.avg i base = base
  obs_zero : ∀ i ∈ range k, system.avg i obs = 0
  obs_bound : ∀ x, |obs x| ≤ (3 : ℝ) / 4
  partition_pos : 0 < integral.linear (base * ∏ i ∈ range k, kernels i)

namespace AnnularData

variable {k : ℕ} {D L : ℝ} (A : AnnularData Ω k D L)

noncomputable def correlation : ℝ :=
  A.integral.linear (A.obs * A.base * ∏ i ∈ range k, A.kernels i) /
    A.integral.linear (A.base * ∏ i ∈ range k, A.kernels i)

theorem product_bound (hD : 0 < D) (hL : Real.log 4 ≤ L) :
    |A.correlation| ≤ (3 : ℝ) / 4 * ∏ j ∈ range k, D / (L + j * Real.log 4) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  apply A.system.correlation_bound
  · intro j _
    apply div_pos hD
    have hLj : 0 ≤ (j : ℝ) * Real.log 4 := mul_nonneg (Nat.cast_nonneg j) hlog.le
    linarith
  · exact A.kernel_nonneg
  · exact A.lower
  · exact A.cross
  · exact A.obs_zero
  · exact A.obs_bound
  · exact A.base_nonneg
  · exact A.base_fixed
  · exact A.partition_pos

theorem factorial_bound (hD : 0 < D) (hL : Real.log 4 ≤ L) :
    |A.correlation| ≤ (3 : ℝ) / 4 * (D / Real.log 4) ^ k / k.factorial := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hL0 : 0 ≤ L := hlog.le.trans hL
  have hp := annular_product_le_factorial (fun j => D / (L + j * Real.log 4))
    (D / Real.log 4) (div_nonneg hD.le hlog.le)
    (fun j => div_nonneg hD.le (by positivity)) (log_factor_le hD.le hL) k
  calc
    |A.correlation| ≤ (3 : ℝ) / 4 * ∏ j ∈ range k, D / (L + j * Real.log 4) :=
      A.product_bound hD hL
    _ ≤ (3 : ℝ) / 4 * ((D / Real.log 4) ^ k / k.factorial) := by gcongr
    _ = _ := by ring

/-- A uniform explicit estimate: the constant does not depend on the graph,
its volume, the sites, or the represented correlation. -/
theorem weighted_bound (hD : 0 < D) (hL : Real.log 4 ≤ L)
    {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (hscale : 1 + r ≤ a * (4 : ℝ) ^ k)
    (p : ℕ) :
    |A.correlation| * (1 + r) ^ p ≤
      (3 : ℝ) / 4 * a ^ p * Real.exp ((D / Real.log 4) * (4 : ℝ) ^ p) := by
  have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hf := factorial_weighted_bound (div_nonneg hD.le hlog.le) ha
    (by norm_num : (0 : ℝ) ≤ 4) hr k p hscale
  calc
    |A.correlation| * (1 + r) ^ p ≤
        ((3 : ℝ) / 4 * (D / Real.log 4) ^ k / k.factorial) * (1 + r) ^ p := by
      gcongr
      exact A.factorial_bound hD hL
    _ = (3 : ℝ) / 4 * (((D / Real.log 4) ^ k / k.factorial) * (1 + r) ^ p) := by ring
    _ ≤ (3 : ℝ) / 4 * (a ^ p * Real.exp ((D / Real.log 4) * (4 : ℝ) ^ p)) := by
      gcongr
    _ = _ := by ring

end AnnularData

/-- Precise conditional statement: a correlation sequence with certified
annular factorizations has superpolynomial decay. -/
theorem superpolynomial_of_annular_data {C : ℕ → ℝ} {D L : ℝ}
    (spaces : ℕ → Type*) [∀ r, TopologicalSpace (spaces r)]
    (hD : 0 < D) (hL : Real.log 4 ≤ L) (N : ℕ) (hN : 0 < N)
    (data : ∀ r, AnnularData (spaces r) (annulusCount N r hN) D L)
    (represents : ∀ r, (data r).correlation = C r) : SuperpolynomialDecay C := by
  apply superpolynomial_of_factorial (M := (3 : ℝ) / 4)
    (B := D / Real.log 4) (by norm_num)
    (div_nonneg hD.le (Real.log_pos (by norm_num)).le) N hN
  intro r
  rw [← represents r]
  exact (data r).factorial_bound hD hL

end RP3
