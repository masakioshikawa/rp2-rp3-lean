import RP2.LogSquareRates
import RP2.ThinAnnuli
import RP2.ThinScaleChoice

/-!
# Packing dyadic thin annuli

Each band of radius `2^n` is divided into shells of width `2^(n-h)` with
an equally wide gap.  This gives `2^(h-1)` disjoint shells in that band.
-/
namespace RP2
noncomputable section
open Finset MeasureTheory
open RP2.Fourier

def thinShellCount (h : ℕ) : ℕ := 2^(h-1)

def thinShellWidth (n h : ℕ) : ℕ := 2^(n-h)

def thinShellInner (n h j : ℕ) : ℕ := 2^n + 2*j*thinShellWidth n h

def thinShellOuter (n h j : ℕ) : ℕ := thinShellInner n h j + thinShellWidth n h

theorem thinShell_fills_band {n h : ℕ} (hh : 1 ≤ h) (hhn : h ≤ n) :
    2 * thinShellCount h * thinShellWidth n h = 2^n := by
  dsimp [thinShellCount, thinShellWidth]
  calc
    2 * 2^(h-1) * 2^(n-h) = (2:ℕ)^(1+(h-1)+(n-h)) := by
      simp only [pow_add, pow_one]
    _ = _ := by congr 1; omega

theorem thinShell_inner_ge (n h j : ℕ) : 2^n ≤ thinShellInner n h j := by
  simp [thinShellInner]

theorem thinShell_outer_lt {n h j : ℕ} (hh : 1 ≤ h) (hhn : h ≤ n)
    (hj : j < thinShellCount h) : thinShellOuter n h j < 2*2^n := by
  have hf := thinShell_fills_band hh hhn
  have hw : 0 < thinShellWidth n h := by dsimp [thinShellWidth]; positivity
  have hmul := Nat.mul_le_mul_right (thinShellWidth n h)
    (show 2*j+2 ≤ 2*thinShellCount h by omega)
  dsimp [thinShellOuter, thinShellInner]
  nlinarith

theorem thinShell_width_ge {n h : ℕ} (hh : 4 ≤ n-h) :
    16 ≤ thinShellWidth n h := by
  have hp : (2:ℕ)^4 ≤ 2^(n-h) := pow_le_pow_right₀ (by norm_num) hh
  norm_num only [show (2:ℕ)^4 = 16 by norm_num] at hp
  exact hp

theorem thinShell_width {n h j : ℕ} (hh : 4 ≤ n-h) :
    thinShellInner n h j + 2 ≤ thinShellOuter n h j := by
  have hw := thinShell_width_ge hh
  dsimp [thinShellOuter]
  omega

theorem thinShell_same_band_separated {n h i j : ℕ} (hij : i < j) :
    thinShellOuter n h i ≤ thinShellInner n h j := by
  have hm := Nat.mul_le_mul_right (thinShellWidth n h)
    (show 2*i+1 ≤ 2*j by omega)
  dsimp [thinShellOuter, thinShellInner]
  nlinarith

theorem thinShell_different_band_separated {n n' h h' i j : ℕ}
    (hh : 1 ≤ h) (hhn : h ≤ n) (hi : i < thinShellCount h) (hn : n < n') :
    thinShellOuter n h i ≤ thinShellInner n' h' j := by
  have hp : (2:ℕ)^(n+1) ≤ 2^n' := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hp
  have hp' : 2*2^n ≤ (2:ℕ)^n' := by simpa only [Nat.mul_comm] using hp
  exact (thinShell_outer_lt hh hhn hi).le.trans (hp'.trans (thinShell_inner_ge n' h' j))

/-- The indices of shells in the first `k` bands, ordered first by band
and then by their radius within the band. -/
abbrev ThinShellIndex (h : ℕ → ℕ) (a k : ℕ) :=
  Lex (Σ i : Fin k, Fin (thinShellCount (h (a+i.val))))

theorem thinShellIndex_card (h : ℕ → ℕ) (a k : ℕ) :
    Fintype.card (ThinShellIndex h a k) =
      packedAnnulusCount (fun n => thinShellCount (h n)) a k := by
  change Fintype.card (Σ i : Fin k, Fin (thinShellCount (h (a+i.val)))) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun j => thinShellCount (h (a+j))) k

namespace Fourier.LatticeGraph

/-- Packing all available shells in each successive dyadic band and using
the actual pinned-kernel comparison gives the exact cumulative contraction. -/
theorem packed_half_power_of_thin_kernel_bounds (a : ℕ) (h : ℕ → ℕ)
    (hh : ∀ n, a ≤ n → 1 ≤ h n ∧ h n ≤ n ∧ 4 ≤ n-h n)
    (G : LatticeGraph) (b : G.edges → ℝ)
    (hcomp : ∀ n, a ≤ n → ∀ j, j < thinShellCount (h n) →
      ∀ (z : Site) (g : Tetrahedral) τ,
      (1-(1/2:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (thinShellInner n (h n) j)
          (thinShellOuter n (h n) j) z) b)
        (G.thinLayer (thinShellInner n (h n) j) (thinShellOuter n (h n) j) z)ᶜ
        ((tetraAction.onCut (G.innerCut (thinShellInner n (h n) j) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (thinShellInner n (h n) j)
          (thinShellOuter n (h n) j) z) b)
        (G.thinLayer (thinShellInner n (h n) j) (thinShellOuter n (h n) j) z)ᶜ τ)
    (x y : G.vertices) :
    let r := (siteRadius x.val y.val).toNat
    let k := denseAnnulusCount (2^a) r (by positivity)
    |correlation (fun e : G.edges => e.val) b x y| ≤
      (2:ℝ)/3 * (1/2:ℝ)^packedAnnulusCount (fun n => thinShellCount (h n)) a k := by
  classical
  dsimp only
  let r := (siteRadius x.val y.val).toNat
  let k := denseAnnulusCount (2^a) r (by positivity)
  let J := ThinShellIndex h a k
  let R : J → ℤ := fun i => thinShellInner (a+i.1.val) (h (a+i.1.val)) i.2.val
  let S : J → ℤ := fun i => thinShellOuter (a+i.1.val) (h (a+i.1.val)) i.2.val
  have hpar (i : J) := hh (a+i.1.val) (by omega)
  have hR (i : J) : 0 ≤ R i := by dsimp [R]; positivity
  have hwidth (i : J) : R i+2 ≤ S i := by
    dsimp only [R, S]
    exact_mod_cast thinShell_width (j := i.2.val) (hpar i).2.2
  have hsep (i j : J) (hij : i < j) : S i ≤ R j := by
    rcases i with ⟨i, u⟩
    rcases j with ⟨j, v⟩
    rcases Sigma.Lex.lt_def.mp hij with hij | ⟨heq, huv⟩
    · have hi := thinShell_different_band_separated (hpar ⟨i,u⟩).1
        (hpar ⟨i,u⟩).2.1 u.isLt (j := v.val)
        (h' := h (a+j.val)) (show a+i.val < a+j.val by exact Nat.add_lt_add_left hij a)
      dsimp only [R, S]
      exact_mod_cast hi
    · change i = j at heq
      subst j
      dsimp only at huv
      have hi := thinShell_same_band_separated (n := a+i.val) (h := h (a+i.val)) huv
      dsimp only [R, S]
      exact_mod_cast hi
  have hfar (i : J) : S i < siteRadius x.val y.val := by
    have hi := denseAnnulusCount_inside (2^a) r (by positivity) i.1.isLt
    have hs := thinShell_outer_lt (hpar i).1 (hpar i).2.1 i.2.isLt
    have hi' : 2 * 2^(a+i.1.val) < r := by
      simpa only [pow_add, mul_assoc] using hi
    have hsr : thinShellOuter (a+i.1.val) (h (a+i.1.val)) i.2.val < r := hs.trans hi'
    have hr : (r:ℤ) = siteRadius x.val y.val :=
      Int.toNat_of_nonneg (siteRadius_nonneg _ _)
    have hz : S i < (r:ℤ) := by
      dsimp only [S]
      exact_mod_cast hsr
    rwa [hr] at hz
  have hc := G.thin_square_annuli_product_bound b R S hR hwidth hsep x y hfar
    (fun _ => (1/2:ℝ)) (fun _ => by norm_num)
    (fun i g τ => hcomp (a+i.1.val) (by omega) i.2.val i.2.isLt x.val g τ)
  have hp : (∏ _i : J, (1/2:ℝ)) =
      (1/2:ℝ)^packedAnnulusCount (fun n => thinShellCount (h n)) a k := by
    simp only [prod_const, card_univ]
    rw [thinShellIndex_card]
  rw [hp] at hc
  exact hc

end Fourier.LatticeGraph

/-- Numerical error in the thin-shell comparison after the periodic and
tetrahedral comparison constants have been included. -/
def thinDyadicError (E F : ℝ) (n h : ℕ) : ℝ :=
  E*(2:ℝ)^h/(n-h : ℕ) + F*(2:ℝ)^(6*h)/(2:ℝ)^n

/-- The precise analytic input consumed by the packing argument.  The
eventual choice of scales below proves the small-error hypothesis, before
any finite graph or coupling is chosen. -/
def SignedThinDyadicKernelComparison (β E F : ℝ) : Prop :=
  ∀ n h : ℕ, 1 ≤ h → 2*h ≤ n → 4 ≤ n-h → thinDyadicError E F n h ≤ 1/2 →
    ∀ j : ℕ, j < thinShellCount h → ∀ (G : Fourier.LatticeGraph)
    (b : G.edges → ℝ), (∀ e, |b e| ≤ β) →
    ∀ (z : Fourier.Site) (g : Tetrahedral) τ,
      (1-thinDyadicError E F n h) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (thinShellInner n h j)
          (thinShellOuter n h j) z) b)
        (G.thinLayer (thinShellInner n h j) (thinShellOuter n h j) z)ᶜ
        ((tetraAction.onCut (G.innerCut (thinShellInner n h j) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (thinShellInner n h j)
          (thinShellOuter n h j) z) b)
        (G.thinLayer (thinShellInner n h j) (thinShellOuter n h j) z)ᶜ τ

/-- The linear shell count is sufficient for the log-square rate. -/
theorem thinShellCount_linear {A n h : ℕ} (hA : 0 < A) (hh : 1 ≤ h)
    (hcover : n ≤ 2*A*2^h) : (1/(4*(A:ℝ))) * n ≤ thinShellCount h := by
  have he : h = h-1+1 := by omega
  have hc : n ≤ 4*A*thinShellCount h := by
    calc n ≤ 2*A*2^h := hcover
      _ = 4*A*thinShellCount h := by
        unfold thinShellCount
        conv_lhs => rw [he, pow_succ]
        ring
  have hcr : (n:ℝ) ≤ 4*(A:ℝ)*(thinShellCount h:ℝ) := by exact_mod_cast hc
  have hAp : (0:ℝ) < A := by exact_mod_cast hA
  have hd : (n:ℝ)/(4*(A:ℝ)) ≤ thinShellCount h :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hd

/-- Once the uniform thin-shell comparison is proved, the exact finite
graph argument yields an all-distance log-square bound with uniform
constants. -/
theorem log_square_of_thin_comparison_signed (β E F : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hcomparison : SignedThinDyadicKernelComparison β E F) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation (fun e : G.edges => e.val) b x y| ≤
        C * Real.exp (-c * (Real.log (2+(Fourier.siteRadius x.val y.val:ℝ)))^2) := by
  obtain ⟨A, a, hA, ha, hchoice⟩ := thin_scale_choice E F hE hF
  let h : ℕ → ℕ := fun n => denseAnnulusCount A n (by omega)
  let γ : ℝ := 1/(4*(A:ℝ))
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hm (j : ℕ) : γ*(j:ℝ) ≤ thinShellCount (h (a+j)) := by
    have hc := hchoice (a+j) (by omega)
    have hb := thinShellCount_linear (by omega : 0 < A) hc.1 hc.2.2.2.2.1
    have hj : (j:ℝ) ≤ (a+j:ℕ) := by exact_mod_cast (show j ≤ a+j by omega)
    exact (mul_le_mul_of_nonneg_left hj hγ.le).trans hb
  obtain ⟨C, hC, c, hc, hrate⟩ := packed_annulus_log_square_bound
    (fun n => thinShellCount (h n)) a (2^a) (by positivity) hγ hm
  refine ⟨C, hC, c, hc, ?_⟩
  intro G b hb x y
  have hh : ∀ n, a ≤ n → 1 ≤ h n ∧ h n ≤ n ∧ 4 ≤ n-h n := by
    intro n hn
    have hc := hchoice n hn
    exact ⟨hc.1, by dsimp [h]; omega, hc.2.2.1⟩
  have hcomp : ∀ n, a ≤ n → ∀ j, j < thinShellCount (h n) →
      ∀ (z : Site) (g : Tetrahedral) τ,
      (1-(1/2:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (thinShellInner n (h n) j)
          (thinShellOuter n (h n) j) z) b)
        (G.thinLayer (thinShellInner n (h n) j) (thinShellOuter n (h n) j) z)ᶜ
        ((tetraAction.onCut (G.innerCut (thinShellInner n (h n) j) z)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.thinKernelEdges (thinShellInner n (h n) j)
          (thinShellOuter n (h n) j) z) b)
        (G.thinLayer (thinShellInner n (h n) j) (thinShellOuter n (h n) j) z)ᶜ τ := by
    intro n hn j hj z g τ
    have hp := hchoice n hn
    have hsmall : thinDyadicError E F n (h n) ≤ 1/2 := hp.2.2.2.2.2
    have hc := hcomparison n (h n) hp.1 hp.2.1 hp.2.2.1 hsmall j hj G b hb z g τ
    exact (mul_le_mul_of_nonneg_right (by linarith : 1-(1/2:ℝ) ≤
      1-thinDyadicError E F n (h n)) (pinnedPartition_pos _ _ _ _).le).trans hc
  have hp := G.packed_half_power_of_thin_kernel_bounds a h hh b hcomp x y
  have hresult := hp.trans (hrate (siteRadius x.val y.val).toNat)
  have hdist : (((siteRadius x.val y.val).toNat : ℕ):ℝ) =
      (siteRadius x.val y.val:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (siteRadius_nonneg x.val y.val)
  simpa only [hdist] using hresult

end
end RP2
