module

public import RP2.DenseLogarithmicRate

public section

/-! Sharper annular products obtained by screening both observation sites.
The second chain uses complementary cuts; global rotation invariance converts
its comparison to the already proved inner-boundary comparison. -/
namespace RP2
noncomputable section
open Finset MeasureTheory
open RP2.Fourier

/-- Rotating the complement of a cut is equivalent, for a globally invariant
pinned kernel, to rotating the cut by the inverse group element. -/
theorem pinnedKernel_tetra_complement {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (edge : E → V × V) (b : E → ℝ) (pins cut : Finset V)
    (g : Tetrahedral) (τ : Configuration V) :
    pinnedKernel edge b pins ((tetraAction.onCut cutᶜ).move g τ) =
      pinnedKernel edge b pins ((tetraAction.onCut cut).move g⁻¹ τ) := by
  have h := pinnedKernel_cut_invariant_of_edges tetraAction tetraLinearIsometry
    tetraAction_eq_spinRotation edge b pins univ
    (by intro e; right; simp) g ((tetraAction.onCut cut).move g⁻¹ τ)
  have he : (tetraAction.onCut (univ : Finset V)).move g
      ((tetraAction.onCut cut).move g⁻¹ τ) =
      (tetraAction.onCut cutᶜ).move g τ := by
    funext v
    by_cases hv : v ∈ cut
    · simp only [FiniteAction.onCut_apply, mem_univ, mem_compl, hv,
        not_true_eq_false, ite_true, ite_false]
      rw [← tetraAction.mul_apply, mul_inv_cancel, tetraAction.one_apply]
    · simp [FiniteAction.onCut_apply, hv]
  rw [he] at h
  exact h

namespace Fourier.LatticeGraph

/-- Triangle inequality in the form used for two disjoint endpoint balls. -/
theorem radius_other_gt {z w v : Site} {A B : ℤ}
    (hv : siteRadius z v ≤ A) (h : A+B < siteRadius z w) :
    B < siteRadius w v := by
  have ht := siteRadius_triangle z v w
  rw [siteRadius_symm v w] at ht
  omega

theorem kernelEdges_other_radius (G : LatticeGraph) {N M : ℤ} {z w : Site}
    (h : 2*N+M < siteRadius z w) (e : G.edges) (he : e ∈ G.kernelEdges N z) :
    M < siteRadius w e.val.1.val ∧ M < siteRadius w e.val.2.val := by
  have hn := G.kernelEdges_endpoints N z e he
  exact ⟨radius_other_gt hn.1.2 h, radius_other_gt hn.2.2 h⟩

theorem kernelEdges_disjoint_other (G : LatticeGraph) {N M : ℤ} {z w : Site}
    (h : 2*N+2*M < siteRadius z w) :
    Disjoint (G.kernelEdges N z) (G.kernelEdges M w) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  have hn := G.kernelEdges_other_radius h e he
  have hm := G.kernelEdges_endpoints M w e hf
  omega

theorem adjacent_kernelEdges_disjoint (G : LatticeGraph) {k : ℕ}
    (N : Fin k → ℤ) (hsep : ∀ i j, i < j → 2*N i ≤ N j) (z : Site)
    {i j : Fin k} (hij : i ≠ j) :
    Disjoint (G.kernelEdges (N i) z) (G.kernelEdges (N j) z) := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact G.separated_kernelEdges_le z (hsep i j hij)
  · exact (G.separated_kernelEdges_le z (hsep j i hji)).symm

theorem adjacent_kernelEdges_avoid (G : LatticeGraph) {k : ℕ}
    (N : Fin k → ℤ) (hsep : ∀ i j, i < j → 2*N i ≤ N j) (z : Site)
    {i j : Fin k} (hij : i ≠ j) (e : G.edges) (he : e ∈ G.kernelEdges (N j) z) :
    e.val.1 ∉ G.strictLayer (N i) z ∧ e.val.2 ∉ G.strictLayer (N i) z := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact G.kernelEdges_avoid_smaller_interior_le z (hsep i j hij) e he
  · exact G.kernelEdges_avoid_larger_interior_le z (hsep j i hji) e he

theorem adjacent_kernelEdges_same_side (G : LatticeGraph) {k : ℕ}
    (N : Fin k → ℤ) (hN : ∀ i, 2 ≤ N i)
    (hsep : ∀ i j, i < j → 2*N i ≤ N j) (z : Site)
    {i j : Fin k} (hij : i ≠ j) (e : G.edges) (he : e ∈ G.kernelEdges (N j) z) :
    e.val.1 ∈ G.innerCut (N i) z ↔ e.val.2 ∈ G.innerCut (N i) z := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hn := G.kernelEdges_outside_smaller_cut_le (by have := hN i; omega)
      z (hsep i j hij) e he
    exact iff_of_false hn.1 hn.2
  · have hn := G.kernelEdges_inside_larger_cut_le z (hsep j i hji) e he
    exact iff_of_true hn.1 hn.2

/-- Product bounds from disjoint families around both endpoints. -/
theorem two_endpoint_annuli_product_bound (G : LatticeGraph) (b : G.edges → ℝ)
    (k : ℕ) (N : Fin k → ℤ) (hN : ∀ i, 2 ≤ N i)
    (hsep : ∀ i j, i < j → 2*N i ≤ N j)
    (x y : G.vertices) (hfar : ∀ i, 4*N i < siteRadius x.val y.val)
    (ε : Fin k → ℝ) (hε : ∀ i, 0 < ε i)
    (hcompare : ∀ i (z : Site) (g : Tetrahedral) τ,
      (1-ε i) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (N i) z) b) (G.strictLayer (N i) z)ᶜ
        ((tetraAction.onCut (G.innerCut (N i) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (N i) z) b) (G.strictLayer (N i) z)ᶜ τ) :
    |correlation (fun e : G.edges => e.val) b x y| ≤
      (2:ℝ)/3 * (∏ i, ε i)^2 := by
  classical
  let J := Sum (Fin k) (Fin k)
  let index : J → Fin k := Sum.elim id id
  let center : J → Site := Sum.elim (fun _ => x.val) (fun _ => y.val)
  let sets : J → Finset G.edges := fun i => G.kernelEdges (N (index i)) (center i)
  let pins : J → Finset G.vertices := fun i => (G.strictLayer (N (index i)) (center i))ᶜ
  let cuts : J → Finset G.vertices := Sum.elim
    (fun i => G.innerCut (N i) x.val) (fun i => (G.innerCut (N i) y.val)ᶜ)
  have hbetween (i j : Fin k) : 2*N i+2*N j < siteRadius x.val y.val := by
    have hi := hfar i
    have hj := hfar j
    omega
  have hbetween' (i j : Fin k) : 2*N i+2*N j < siteRadius y.val x.val := by
    rw [siteRadius_symm y.val x.val]
    exact hbetween i j
  have hxy (i : Fin k) : N i < siteRadius x.val y.val := by
    have := hfar i
    have := hN i
    omega
  have hother (i j : Fin k) : G.innerCut (N i) x.val ⊆ (G.innerCut (N j) y.val)ᶜ := by
    intro v hv
    have hv' := (mem_innerCut G (N i) x.val v).mp hv
    have hb := hbetween i j
    have hi := hN i
    have hj := hN j
    have ht := radius_other_gt hv' (show N i+N j < siteRadius x.val y.val by omega)
    simpa only [mem_compl, mem_innerCut, not_le] using ht
  have hmono (z : Site) (i j : Fin k) :
      G.innerCut (N i) z ⊆ G.innerCut (N j) z ∨
      G.innerCut (N j) z ⊆ G.innerCut (N i) z := by
    rcases le_total i j with hij | hji
    · left
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hij with rfl | hij
      · exact le_rfl
      · have := hsep i j hij; have := hN i; omega
    · right
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hji with rfl | hji
      · exact le_rfl
      · have := hsep j i hji; have := hN j; omega
  have hc := concrete_kernel_product_bound (fun e : G.edges => e.val) b sets pins cuts
    x y (fun i => ε (index i))
    (by
      intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact G.adjacent_kernelEdges_disjoint N hsep x.val (fun h => hij (by cases h; rfl))
        | inr j => exact G.kernelEdges_disjoint_other (hbetween i j)
      | inr i =>
        cases j with
        | inl j => exact G.kernelEdges_disjoint_other (hbetween' i j)
        | inr j => exact G.adjacent_kernelEdges_disjoint N hsep y.val (fun h => hij (by cases h; rfl)))
    (by
      intro i j
      cases i with
      | inl i =>
        cases j with
        | inl j => exact hmono x.val i j
        | inr j => exact Or.inl (hother i j)
      | inr i =>
        cases j with
        | inl j => exact Or.inr (hother j i)
        | inr j =>
          rcases hmono y.val i j with h | h
          · exact Or.inr (Finset.compl_subset_compl.mpr h)
          · exact Or.inl (Finset.compl_subset_compl.mpr h))
    (by
      intro i e
      by_cases he : ∃ j, e ∈ sets j
      · left; simp [remainingCoupling, he]
      · right
        have hn : e ∉ sets i := fun hi => he ⟨i, hi⟩
        simpa only [sets, pins, mem_kernelEdges, not_or, mem_compl] using hn)
    (by
      intro i j hij e
      by_cases he : e ∈ sets j
      · right
        simp only [pins, mem_compl]
        cases i with
        | inl i =>
          cases j with
          | inl j => exact G.adjacent_kernelEdges_avoid N hsep x.val (fun h => hij (by cases h; rfl)) e he
          | inr j =>
            have hn := G.kernelEdges_other_radius (hbetween' j i) e he
            simp only [index, center, Sum.elim_inl, id_eq, mem_strictLayer]
            omega
        | inr i =>
          cases j with
          | inl j =>
            have hn := G.kernelEdges_other_radius (hbetween j i) e he
            simp only [index, center, Sum.elim_inr, id_eq, mem_strictLayer]
            omega
          | inr j => exact G.adjacent_kernelEdges_avoid N hsep y.val (fun h => hij (by cases h; rfl)) e he
      · left; simp [maskedCoupling, he])
    (by
      intro i
      cases i with
      | inl i =>
        have hf := hfar i; have hn := hN i
        simp only [pins, index, center, Sum.elim_inl, id_eq, mem_compl,
          mem_strictLayer, siteRadius_self]
        omega
      | inr i =>
        have hf := hfar i; have hn := hN i
        rw [siteRadius_symm x.val y.val] at hf
        simp only [pins, index, center, Sum.elim_inr, id_eq, mem_compl,
          mem_strictLayer, siteRadius_self]
        omega)
    (by
      intro i e
      by_cases he : ∃ j, e ∈ sets j
      · left; simp [remainingCoupling, he]
      · right
        have hn : e ∉ sets i := fun hi => he ⟨i,hi⟩
        cases i with
        | inl i => exact G.nonkernel_same_side (N i) (hN i) x.val e hn
        | inr i =>
          simp only [cuts, Sum.elim_inr, mem_compl]
          exact not_congr (G.nonkernel_same_side (N i) (hN i) y.val e hn))
    (by
      intro i j hij e
      by_cases he : e ∈ sets j
      · right
        cases i with
        | inl i =>
          cases j with
          | inl j => exact G.adjacent_kernelEdges_same_side N hN hsep x.val (fun h => hij (by cases h; rfl)) e he
          | inr j =>
            have hn := G.kernelEdges_other_radius (hbetween' j i) e he
            have hi := hN i
            simp only [cuts, Sum.elim_inl, mem_innerCut]
            omega
        | inr i =>
          simp only [cuts, Sum.elim_inr, mem_compl]
          cases j with
          | inl j =>
            have hn := G.kernelEdges_other_radius (hbetween j i) e he
            have hi := hN i
            simp only [mem_innerCut]
            omega
          | inr j => exact not_congr (G.adjacent_kernelEdges_same_side N hN hsep y.val (fun h => hij (by cases h; rfl)) e he)
      · left; simp [maskedCoupling, he])
    (by
      intro i
      cases i with
      | inl i =>
        have hf := hxy i; have hn := hN i
        simp only [cuts, Sum.elim_inl, mem_innerCut, siteRadius_self]
        omega
      | inr i =>
        have hf := hxy i; have hn := hN i
        rw [siteRadius_symm x.val y.val] at hf
        simp only [cuts, Sum.elim_inr, mem_compl, mem_innerCut, siteRadius_self]
        omega)
    (fun i => hε (index i))
    (by
      intro i g τ
      cases i with
      | inl i => exact hcompare i x.val g τ
      | inr i =>
        change (1-ε i) * pinnedKernel (fun e : G.edges => e.val)
          (maskedCoupling (G.kernelEdges (N i) y.val) b) (G.strictLayer (N i) y.val)ᶜ
          ((tetraAction.onCut (G.innerCut (N i) y.val)ᶜ).move g τ) ≤ _
        rw [pinnedKernel_tetra_complement]
        exact hcompare i y.val g⁻¹ τ)
  have hp : (∏ i : J, ε (index i)) = (∏ i : Fin k, ε i)^2 := by
    rw [Fintype.prod_sum_type]
    simp only [index, Sum.elim_inl, Sum.elim_inr, id_eq, pow_two]
  rw [hp] at hc
  exact hc


/-- The adjacent-scale factorial is squared when both endpoints are screened. -/
theorem two_endpoint_factorial_of_dyadic_kernel_bounds {D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (G : LatticeGraph) (b : G.edges → ℝ)
    (hcomp : ∀ n : ℕ, a ≤ n → ∀ (z : Site) (g : Tetrahedral) τ,
      (1-D/(n:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ
        ((tetraAction.onCut (G.innerCut (2^n:ℕ) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n:ℕ) z) b) (G.strictLayer (2^n:ℕ) z)ᶜ τ)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := denseAnnulusCount (2^(a+1)) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤ (2:ℝ)/3 * (D^k/k.factorial)^2 := by
  classical
  dsimp only
  let r := (siteRadius x.val y.val).toNat
  let k := denseAnnulusCount (2^(a+1)) r (by positivity)
  let N : Fin k → ℤ := fun i => RP2.adjacentDyadicRadius a i
  let ε : Fin k → ℝ := fun i => D/(a+(i.val:ℝ))
  have hN (i : Fin k) : 2 ≤ N i := by
    have hpow : 2^1 ≤ (2:ℕ)^(a+i.val) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    dsimp [N, RP2.adjacentDyadicRadius]
    norm_num only [pow_one] at hpow
    exact_mod_cast hpow
  have hsep (i j : Fin k) (hij : i < j) : 2*N i ≤ N j := by
    dsimp [N]
    exact_mod_cast adjacentDyadicRadius_separated a i.val j.val hij
  have hfar (i : Fin k) : 4*N i < siteRadius x.val y.val := by
    have hi := denseAnnulusCount_inside (2^(a+1)) r (by positivity) i.isLt
    have he : 4*(RP2.adjacentDyadicRadius a i.val) < r := by
      rw [adjacentDyadicRadius_eq]
      rw [pow_succ] at hi
      nlinarith [hi]
    have hr : (r:ℤ) = siteRadius x.val y.val :=
      Int.toNat_of_nonneg (siteRadius_nonneg _ _)
    have hiR : 4*N i < (r:ℤ) := by
      dsimp [N]
      exact_mod_cast he
    rwa [hr] at hiR
  have hε (i : Fin k) : 0 < ε i := by
    apply div_pos hD
    have haR : (2:ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hc := G.two_endpoint_annuli_product_bound b k N hN hsep x y hfar ε hε
    (by
      intro i z g τ
      have h := hcomp (a+i.val) (by omega) z g τ
      simpa only [ε, N, RP2.adjacentDyadicRadius, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h)
  have hp := annular_product_le_factorial (fun j => D/(a+(j:ℝ))) D
    (by positivity) (fun j => div_nonneg hD.le (by positivity)) (dense_factor_le hD.le ha) k
  have hprod : (∏ i : Fin k, ε i) = ∏ j ∈ range k, D/(a+(j:ℝ)) := by
    exact Fin.prod_univ_eq_prod_range (fun j => D/(a+(j:ℝ))) k
  rw [hprod] at hc
  calc
    _ ≤ (2:ℝ)/3 * (∏ j ∈ range k, D/(a+(j:ℝ)))^2 := hc
    _ ≤ (2:ℝ)/3 * (D^k/k.factorial)^2 := by gcongr


/-- Uniform squared factorial bound for signed bounded couplings. -/
theorem two_endpoint_factorial_of_dyadic_comparison_signed {β D : ℝ} (hD : 0 < D)
    (a : ℕ) (ha : 2 ≤ a) (hcomp : SignedDyadicKernelComparison β D a)
    (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := denseAnnulusCount (2^(a+1)) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤
      (2:ℝ)/3 * (D^k/k.factorial)^2 := by
  exact two_endpoint_factorial_of_dyadic_kernel_bounds hD a ha G b
    (fun n hn z g τ => hcomp n hn G b hb z g τ) x y

end Fourier.LatticeGraph

/-- The squared factorial gives twice the adjacent-scale logarithmic exponent. -/
theorem two_endpoint_factorial_logarithmic_bound (N : ℕ) (hN : 0 < N)
    (B : ℝ) (hB : 0 < B) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ r : ℕ, R ≤ r →
      (2/3:ℝ) * (B ^ denseAnnulusCount N r hN /
        (denseAnnulusCount N r hN).factorial)^2 ≤
        Real.exp (-2*Real.log (r:ℝ)*Real.log (Real.log (r:ℝ))/Real.log 2 +
          C*Real.log (r:ℝ)) := by
  obtain ⟨C, hC, R, hlog⟩ := dense_factorial_annulus_logarithmic_bound N hN B hB
  refine ⟨2*C+1, by positivity, max R 2, ?_⟩
  intro r hr
  have hrR : R ≤ r := (le_max_left _ _).trans hr
  have hr2 : 2 ≤ r := (le_max_right _ _).trans hr
  have hr2R : (2:ℝ) ≤ r := by exact_mod_cast hr2
  have hrpos : (0:ℝ) < r := by linarith
  let k := denseAnnulusCount N r hN
  let f := B^k/(k.factorial:ℝ)
  let S := -Real.log (r:ℝ)*Real.log (Real.log (r:ℝ))/Real.log 2 + C*Real.log (r:ℝ)
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hb : (2/3:ℝ)*f ≤ Real.exp S := by
    convert hlog r hrR using 1 <;> dsimp [f, S, k] <;> ring
  change (2/3:ℝ)*f^2 ≤ _
  calc
    _ = (3/2:ℝ)*((2/3:ℝ)*f)^2 := by ring
    _ ≤ (r:ℝ)*(Real.exp S)^2 := by gcongr <;> linarith
    _ = Real.exp (Real.log (r:ℝ) + (S+S)) := by
      rw [Real.exp_add (Real.log (r:ℝ)) (S+S), Real.exp_log hrpos,
        Real.exp_add S S, pow_two]
    _ = _ := by congr 1; dsimp [S]; ring

/-- Stronger all-temperature bound from adjacent annuli at both endpoints. -/
theorem two_endpoint_factorial_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      let r := (Fourier.siteRadius x.val y.val).toNat
      let k := denseAnnulusCount (2^(a+1)) r (by positivity)
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (2:ℝ)/3 * (D^k/k.factorial)^2 := by
  obtain ⟨D, hD, a, ha, hcomparison⟩ :=
    Fourier.LatticeGraph.dyadic_kernel_comparison_signed β hβ
  exact ⟨D, hD, a, ha, fun G b hb x y =>
    Fourier.LatticeGraph.two_endpoint_factorial_of_dyadic_comparison_signed
      hD a ha hcomparison G b hb x y⟩

/-- Leading coefficient `2/log 2`, four times the original `1/log 4` bound. -/
theorem two_endpoint_logarithmic_quadrupolar_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      R ≤ (Fourier.siteRadius x.val y.val).toNat →
      |correlation (fun e : G.edges => e.val) b x y| ≤
        Real.exp (-2*Real.log (Fourier.siteRadius x.val y.val : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x.val y.val : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨D, hD, a, ha, hfactorial⟩ := two_endpoint_factorial_quadrupolar_decay_signed β hβ
  obtain ⟨C, hC, R, hlog⟩ := two_endpoint_factorial_logarithmic_bound
    (2^(a+1)) (by positivity) D hD
  refine ⟨C, hC, R, ?_⟩
  intro G b hb x y hr
  have hn : (((Fourier.siteRadius x.val y.val).toNat : ℕ) : ℝ) =
      (Fourier.siteRadius x.val y.val : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Fourier.siteRadius_nonneg x.val y.val)
  have h := (hfactorial G b hb x y).trans (hlog _ hr)
  simpa only [hn] using h

/-- Ferromagnetic specialization of the two-endpoint factorial estimate. -/
theorem two_endpoint_factorial_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 < D ∧ ∃ a : ℕ, 2 ≤ a ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      let r := (Fourier.siteRadius x.val y.val).toNat
      let k := denseAnnulusCount (2^(a+1)) r (by positivity)
      |correlation (fun e : G.edges => e.val) b x y| ≤
        (2:ℝ)/3 * (D^k/k.factorial)^2 := by
  obtain ⟨D, hD, a, ha, hbound⟩ := two_endpoint_factorial_quadrupolar_decay_signed β hβ
  exact ⟨D, hD, a, ha, fun G b hb x y => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y⟩

/-- Ferromagnetic specialization of the two-endpoint logarithmic envelope. -/
theorem two_endpoint_logarithmic_quadrupolar_decay (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C ≥ 0, ∃ R : ℕ, ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      R ≤ (Fourier.siteRadius x.val y.val).toNat →
      |correlation (fun e : G.edges => e.val) b x y| ≤
        Real.exp (-2*Real.log (Fourier.siteRadius x.val y.val : ℝ) *
          Real.log (Real.log (Fourier.siteRadius x.val y.val : ℝ)) / Real.log 2 +
          C * Real.log (Fourier.siteRadius x.val y.val : ℝ)) := by
  obtain ⟨C, hC, R, hbound⟩ := two_endpoint_logarithmic_quadrupolar_decay_signed β hβ
  exact ⟨C, hC, R, fun G b hb x y hr => hbound G b
    (fun e => by rw [abs_of_nonneg (hb e).1]; exact (hb e).2) x y hr⟩

end
end RP2
