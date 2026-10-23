module

public import RP2.ConcreteAnnuli

public section

/-! Quantitative assembly of the dyadic kernel estimate into a uniform bound
for actual square-lattice correlations. -/
namespace RP2
noncomputable section
open Finset
open RP2.Fourier

@[expose] def dyadicRadius (a j : ℕ) : ℕ := 2^(a+2*j)

theorem dyadicRadius_eq (a j : ℕ) : RP2.dyadicRadius a j = 2^a * 4^j := by
  simp only [dyadicRadius, pow_add, pow_mul]
  norm_num

theorem dyadicRadius_separated (a i j : ℕ) (hij : i < j) :
    2*RP2.dyadicRadius a i < RP2.dyadicRadius a j := by
  rw [dyadicRadius_eq, dyadicRadius_eq]
  have hp : 4^(i+1) ≤ (4:ℕ)^j := pow_le_pow_right₀ (by norm_num) hij
  have ha : 0 < (2:ℕ)^a := by positivity
  have hi : 0 < (4:ℕ)^i := by positivity
  rw [pow_succ] at hp
  nlinarith

theorem dyadic_factor_le {D : ℝ} (hD : 0 ≤ D) {a : ℕ} (ha : 2 ≤ a) (j : ℕ) :
    D / (a+2*(j:ℝ)) ≤ (D/2)/(j+1) := by
  have haR : (2:ℝ) ≤ a := by exact_mod_cast ha
  calc
    D / (a+2*(j:ℝ)) ≤ D / ((j+1)*2) :=
      div_le_div_of_nonneg_left hD (by positivity) (by linarith)
    _ = _ := by rw [div_div]; congr 1; ring

namespace Fourier.LatticeGraph

/-- The exact comparison proposition required at all large dyadic scales.
It refers to actual pinned RP² integrals, never abstract kernel certificates. -/
@[expose] def DyadicKernelComparison (β D : ℝ) (a : ℕ) : Prop :=
  ∀ n : ℕ, a ≤ n → ∀ (G : LatticeGraph) (b : G.edges → ℝ),
    (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (z : Site) (g : Tetrahedral) τ,
      (1-D/(n:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ
        ((tetraAction.onCut (G.innerCut (2^n:ℕ) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ τ

/-- The dyadic comparison for arbitrary real couplings bounded in absolute value. -/
@[expose] def SignedDyadicKernelComparison (β D : ℝ) (a : ℕ) : Prop :=
  ∀ n : ℕ, a ≤ n → ∀ (G : LatticeGraph) (b : G.edges → ℝ),
    (∀ e, |b e| ≤ β) → ∀ (z : Site) (g : Tetrahedral) τ,
      (1-D/(n:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ
        ((tetraAction.onCut (G.innerCut (2^n:ℕ) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ τ

/-- A comparison for signed couplings includes the ferromagnetic case. -/
theorem SignedDyadicKernelComparison.toNonnegative {β D : ℝ} {a : ℕ}
    (h : SignedDyadicKernelComparison β D a) : DyadicKernelComparison β D a := by
  intro n hn G b hb z g τ
  exact h n hn G b (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) z g τ

/-- Assembly uses only the comparisons for the chosen graph and couplings;
no sign condition on those couplings enters the positive-kernel argument. -/
theorem factorial_of_dyadic_kernel_bounds {D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (G : LatticeGraph) (b : G.edges → ℝ)
    (hcomp : ∀ n : ℕ, a ≤ n → ∀ (z : Site) (g : Tetrahedral) τ,
      (1-D/(n:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ
        ((tetraAction.onCut (G.innerCut (2^n:ℕ) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ τ)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := annulusCount (2^a) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤ (2:ℝ)/3 * (D/2)^k/k.factorial := by
  classical
  dsimp only
  let r := (siteRadius x.val y.val).toNat
  let k := annulusCount (2^a) r (by positivity)
  let N : Fin k → ℤ := fun i => RP2.dyadicRadius a i
  let ε : Fin k → ℝ := fun i => D/(a+2*(i.val:ℝ))
  have hN (i : Fin k) : 2 ≤ N i := by
    have hpow : 2^1 ≤ (2:ℕ)^(a+2*i.val) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [N, RP2.dyadicRadius]
    norm_num only [pow_one] at hpow
    exact_mod_cast hpow
  have hsep (i j : Fin k) (hij : i < j) : 2*N i < N j := by
    dsimp [N]
    exact_mod_cast dyadicRadius_separated a i.val j.val hij
  have hfar (i : Fin k) : 2*N i < siteRadius x.val y.val := by
    have hi := annulusCount_inside (2^a) r (by positivity) i.isLt
    have he : 2*(RP2.dyadicRadius a i.val) < r := by
      simpa only [dyadicRadius_eq, mul_assoc] using hi
    have hr : (r:ℤ) = siteRadius x.val y.val :=
      Int.toNat_of_nonneg (siteRadius_nonneg _ _)
    have hiR : 2*N i < (r:ℤ) := by
      dsimp [N]
      exact_mod_cast he
    rwa [hr] at hiR
  have hε (i : Fin k) : 0 < ε i := by
    apply div_pos hD
    have haR : (2:ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hc := G.square_annuli_product_bound b k N hN hsep x y hfar ε hε
    (by
      intro i g τ
      have h := hcomp (a+2*i.val) (by omega) x.val g τ
      simpa only [ε, N, RP2.dyadicRadius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h)
  have hp := annular_product_le_factorial (fun j => D/(a+2*(j:ℝ))) (D/2)
    (by positivity) (fun j => div_nonneg hD.le (by positivity)) (dyadic_factor_le hD.le ha) k
  have hprod : (∏ i : Fin k, ε i) = ∏ j ∈ range k, D/(a+2*(j:ℝ)) := by
    exact Fin.prod_univ_eq_prod_range (fun j => D/(a+2*(j:ℝ))) k
  rw [hprod] at hc
  calc
    _ ≤ (2:ℝ)/3 * ∏ j ∈ range k, D/(a+2*(j:ℝ)) := hc
    _ ≤ (2:ℝ)/3 * ((D/2)^k/k.factorial) := by gcongr
    _ = _ := by ring


/-- The factorial bound is uniform in the retained graph and admissible couplings. -/
theorem factorial_of_dyadic_comparison_signed {β D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (hcomp : SignedDyadicKernelComparison β D a)
    (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := annulusCount (2^a) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤ (2:ℝ)/3 * (D/2)^k/k.factorial := by
  exact factorial_of_dyadic_kernel_bounds hD a ha G b
    (fun n hn z g τ => hcomp n hn G b hb z g τ) x y

/-- The factorial bound is uniform in the retained graph and admissible couplings. -/
theorem factorial_of_dyadic_comparison {β D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (hcomp : DyadicKernelComparison β D a)
    (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e, 0 ≤ b e ∧ b e ≤ β)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := annulusCount (2^a) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤ (2:ℝ)/3 * (D/2)^k/k.factorial := by
  exact factorial_of_dyadic_kernel_bounds hD a ha G b
    (fun n hn z g τ => hcomp n hn G b hb z g τ) x y

end Fourier.LatticeGraph
end
end RP2
