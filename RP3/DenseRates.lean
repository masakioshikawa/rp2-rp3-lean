module

public import RP3.KernelEstimate

public section

/-!
# Sharper all-temperature decay from adjacent dyadic annuli

The strict annular interiors at radii `N` and `2*N` are disjoint; their
shared pinned boundary causes no overlap of integrated variables or edges.
This retains every dyadic scale instead of every other one. All hypotheses
remain uniform over finite retained graphs and signed bounded couplings.
-/
namespace RP3
noncomputable section
open Finset MeasureTheory
open RP3.Fourier

/-- Number of adjacent dyadic annuli whose outer radius is less than `r`. -/
@[expose] noncomputable def denseAnnulusCount (N r : ℕ) (hN : 0 < N) : ℕ :=
  Nat.find (show ∃ k : ℕ, r ≤ 2 * N * 2 ^ k from
    ⟨r, (Nat.lt_pow_self (by norm_num : 1 < (2 : ℕ))).le.trans
      (Nat.le_mul_of_pos_left _ (by omega))⟩)

theorem denseAnnulusCount_cover (N r : ℕ) (hN : 0 < N) :
    r ≤ 2 * N * 2 ^ denseAnnulusCount N r hN := by
  unfold denseAnnulusCount
  exact Nat.find_spec (p := fun k => r ≤ 2 * N * 2 ^ k) _

theorem denseAnnulusCount_inside (N r : ℕ) (hN : 0 < N) {j : ℕ}
    (hj : j < denseAnnulusCount N r hN) : 2 * N * 2 ^ j < r := by
  unfold denseAnnulusCount at hj
  exact Nat.lt_of_not_ge (Nat.find_min (p := fun k => r ≤ 2 * N * 2 ^ k) _ hj)

theorem denseAnnulusCount_distance (N r : ℕ) (hN : 0 < N) :
    1 + (r : ℝ) ≤ (2 * N + 1) * (2 : ℝ) ^ denseAnnulusCount N r hN := by
  have hc : (r : ℝ) ≤ 2 * N * (2 : ℝ) ^ denseAnnulusCount N r hN := by
    exact_mod_cast denseAnnulusCount_cover N r hN
  have hp : (1 : ℝ) ≤ 2 ^ denseAnnulusCount N r hN := one_le_pow₀ (by norm_num)
  nlinarith

@[expose] def adjacentDyadicRadius (a j : ℕ) : ℕ := 2^(a+j)

theorem adjacentDyadicRadius_eq (a j : ℕ) :
    adjacentDyadicRadius a j = 2^a * 2^j := by
  simp only [adjacentDyadicRadius, pow_add]

theorem adjacentDyadicRadius_separated (a i j : ℕ) (hij : i < j) :
    2 * adjacentDyadicRadius a i ≤ adjacentDyadicRadius a j := by
  have h : (2:ℕ)^(a+i+1) ≤ 2^(a+j) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  simpa only [adjacentDyadicRadius, pow_succ, Nat.mul_comm] using h

theorem dense_factor_le {D : ℝ} (hD : 0 ≤ D) {a : ℕ} (ha : 2 ≤ a) (j : ℕ) :
    D / (a+(j:ℝ)) ≤ D/(j+1) := by
  have haR : (2:ℝ) ≤ a := by exact_mod_cast ha
  exact div_le_div_of_nonneg_left hD (by positivity) (by linarith)

namespace Fourier.LatticeGraph

/-- The annular product estimate remains valid when consecutive annuli share
only their pinned boundary. -/
theorem adjacent_square_annuli_product_bound (G : LatticeGraph) (b : G.edges → ℝ)
    (k : ℕ) (N : Fin k → ℤ) (hN : ∀ i, 2 ≤ N i)
    (hsep : ∀ i j, i < j → 2*N i ≤ N j)
    (x y : G.vertices) (hy : ∀ i, 2*N i < siteRadius x.val y.val)
    (ε : Fin k → ℝ) (hε : ∀ i, 0 < ε i)
    (hcompare : ∀ i (g : Quaternion) τ,
      (1 - ε i) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (N i) x.val) b) (G.strictLayer (N i) x.val)ᶜ
        ((quaternionAction.onCut (G.innerCut (N i) x.val)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (N i) x.val) b) (G.strictLayer (N i) x.val)ᶜ τ) :
    |correlation (fun e : G.edges => e.val) b x y| ≤ (3 : ℝ) / 4 * ∏ i, ε i := by
  classical
  let sets := fun i => G.kernelEdges (N i) x.val
  let pins := fun i => (G.strictLayer (N i) x.val)ᶜ
  let cuts := fun i => G.innerCut (N i) x.val
  have hleft (i : Fin k) : x ∈ pins i := by
    simp only [pins, mem_compl, mem_strictLayer, siteRadius_self]
    have := hN i
    omega
  have hright (i : Fin k) : y ∈ pins i := by
    simp only [pins, mem_compl, mem_strictLayer]
    have := hy i
    omega
  apply concrete_kernel_product_bound (fun e : G.edges => e.val) b sets pins cuts
    x y ε
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact G.separated_kernelEdges_le x.val (hsep i j hij)
    · exact (G.separated_kernelEdges_le x.val (hsep j i hji)).symm
  · intro i j
    rcases le_total i j with hij | hji
    · left
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hij with rfl | hij
      · exact le_rfl
      · have := hsep i j hij
        have := hN i
        omega
    · right
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hji with rfl | hji
      · exact le_rfl
      · have := hsep j i hji
        have := hN j
        omega
  · intro i e
    by_cases he : ∃ j, e ∈ sets j
    · left
      simp [remainingCoupling, he]
    · right
      have hn : e ∉ sets i := fun hi => he ⟨i, hi⟩
      simpa only [sets, pins, mem_kernelEdges, not_or, mem_compl] using hn
  · intro i j hij e
    by_cases he : e ∈ sets j
    · right
      simp only [pins, mem_compl]
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact G.kernelEdges_avoid_smaller_interior_le x.val (hsep i j hij) e he
      · exact G.kernelEdges_avoid_larger_interior_le x.val (hsep j i hji) e he
    · left
      simp [maskedCoupling, he]
  · exact fun i => ⟨hleft i, hright i⟩
  · intro i e
    by_cases he : ∃ j, e ∈ sets j
    · left
      simp [remainingCoupling, he]
    · right
      exact G.nonkernel_same_side (N i) (hN i) x.val e (fun hi => he ⟨i,hi⟩)
  · intro i j hij e
    by_cases he : e ∈ sets j
    · right
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hn := G.kernelEdges_outside_smaller_cut_le (by have := hN i; omega)
          x.val (hsep i j hij) e he
        exact iff_of_false hn.1 hn.2
      · have hn := G.kernelEdges_inside_larger_cut_le x.val (hsep j i hji) e he
        exact iff_of_true hn.1 hn.2
    · left
      simp [maskedCoupling, he]
  · intro i
    simp only [cuts, mem_innerCut, siteRadius_self]
    have := hN i
    have := hy i
    omega
  · exact hε
  · exact hcompare


/-- Using every dyadic scale doubles the leading logarithmic decay coefficient. -/
theorem dense_factorial_of_dyadic_kernel_bounds {D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (G : LatticeGraph) (b : G.edges → ℝ)
    (hcomp : ∀ n : ℕ, a ≤ n → ∀ (z : Site) (g : Quaternion) τ,
      (1-D/(n:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ
        ((quaternionAction.onCut (G.innerCut (2^n:ℕ) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ τ)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := denseAnnulusCount (2^a) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤ (3 : ℝ) / 4 * D^k/k.factorial := by
  classical
  dsimp only
  let r := (siteRadius x.val y.val).toNat
  let k := denseAnnulusCount (2^a) r (by positivity)
  let N : Fin k → ℤ := fun i => RP3.adjacentDyadicRadius a i
  let ε : Fin k → ℝ := fun i => D/(a+(i.val:ℝ))
  have hN (i : Fin k) : 2 ≤ N i := by
    have hpow : 2^1 ≤ (2:ℕ)^(a+i.val) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [N, RP3.adjacentDyadicRadius]
    norm_num only [pow_one] at hpow
    exact_mod_cast hpow
  have hsep (i j : Fin k) (hij : i < j) : 2*N i ≤ N j := by
    dsimp [N]
    exact_mod_cast adjacentDyadicRadius_separated a i.val j.val hij
  have hfar (i : Fin k) : 2*N i < siteRadius x.val y.val := by
    have hi := denseAnnulusCount_inside (2^a) r (by positivity) i.isLt
    have he : 2*(RP3.adjacentDyadicRadius a i.val) < r := by
      simpa only [adjacentDyadicRadius_eq, mul_assoc] using hi
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
  have hc := G.adjacent_square_annuli_product_bound b k N hN hsep x y hfar ε hε
    (by
      intro i g τ
      have h := hcomp (a+i.val) (by omega) x.val g τ
      simpa only [ε, N, RP3.adjacentDyadicRadius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h)
  have hp := annular_product_le_factorial (fun j => D/(a+(j:ℝ))) D
    (by positivity) (fun j => div_nonneg hD.le (by positivity)) (dense_factor_le hD.le ha) k
  have hprod : (∏ i : Fin k, ε i) = ∏ j ∈ range k, D/(a+(j:ℝ)) := by
    exact Fin.prod_univ_eq_prod_range (fun j => D/(a+(j:ℝ))) k
  rw [hprod] at hc
  calc
    _ ≤ (3 : ℝ) / 4 * ∏ j ∈ range k, D/(a+(j:ℝ)) := hc
    _ ≤ (3 : ℝ) / 4 * (D^k/k.factorial) := by gcongr
    _ = _ := by ring


/-- Uniform adjacent-scale factorial bound for signed couplings. -/
theorem dense_factorial_of_dyadic_comparison_signed {β D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (hcomp : SignedDyadicKernelComparison β D a)
    (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := denseAnnulusCount (2^a) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤ (3 : ℝ) / 4 * D^k/k.factorial := by
  exact dense_factorial_of_dyadic_kernel_bounds hD a ha G b
    (fun n hn z g τ => hcomp n hn G b hb z g τ) x y


end Fourier.LatticeGraph
end
end RP3
