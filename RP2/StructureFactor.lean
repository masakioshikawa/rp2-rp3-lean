module

public import RP2.LimitCorollary
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

public section

/-!
# Smooth quadrupolar structure factors

Every polynomially weighted absolute moment of a lattice function being summable
implies that its Fourier series is smooth in momentum.  This module proves this
statement for arbitrary coefficients and then applies it to the actual
infinite-volume quadrupolar correlation.  Translation invariance is not needed
for the fixed-base-point Fourier series; in the translation-invariant case it
is the usual quadrupolar structure factor.

The momentum convention is `exp (I * k · (y - x))`, with no factor of `2 * π`.
The result is smoothness, not analyticity or exponential clustering.
-/

namespace RP2
noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

namespace Fourier

/-- The two real momentum coordinates, equipped with the product norm. -/
abbrev Momentum := ℝ × ℝ

/-- The real pairing `k · (y - x)`, viewed as a continuous linear map in `k`. -/
@[expose] def momentumPhase (x y : Site) : Momentum →L[ℝ] ℝ :=
  ((y.1 - x.1 : ℤ) : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
  ((y.2 - x.2 : ℤ) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem momentumPhase_apply (x y : Site) (k : Momentum) :
    momentumPhase x y k = (y.1 - x.1 : ℤ) * k.1 + (y.2 - x.2 : ℤ) * k.2 := rfl

/-- Each linear pairing grows at most linearly in the lattice radius. -/
theorem norm_momentumPhase_le (x y : Site) :
    ‖momentumPhase x y‖ ≤ 2 * (1 + (siteRadius x y : ℝ)) := by
  have h₁ : |((y.1 - x.1 : ℤ) : ℝ)| ≤ (siteRadius x y : ℝ) := by
    exact_mod_cast (le_max_left |y.1 - x.1| |y.2 - x.2|)
  have h₂ : |((y.2 - x.2 : ℤ) : ℝ)| ≤ (siteRadius x y : ℝ) := by
    exact_mod_cast (le_max_right |y.1 - x.1| |y.2 - x.2|)
  calc
    _ ≤ ‖((y.1 - x.1 : ℤ) : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ‖ +
        ‖((y.2 - x.2 : ℤ) : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_add_le _ _
    _ = |((y.1 - x.1 : ℤ) : ℝ)| + |((y.2 - x.2 : ℤ) : ℝ)| := by
      rw [norm_smul, norm_smul]
      simp
    _ ≤ 2 * (1 + (siteRadius x y : ℝ)) := by linarith

private def oscillator (t : ℝ) : ℂ := Complex.exp ((t : ℂ) * Complex.I)

private theorem oscillator_eq (t : ℝ) :
    oscillator t = (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ) := by
  unfold oscillator
  rw [Complex.exp_mul_I]
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

private theorem contDiff_oscillator : ContDiff ℝ ∞ oscillator := by
  have hc := Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos : ContDiff ℝ ∞ Real.cos)
  have hs := Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin : ContDiff ℝ ∞ Real.sin)
  rw [show oscillator = (fun t => (Real.cos t : ℂ) + Complex.I * (Real.sin t : ℂ))
    from funext oscillator_eq]
  exact hc.add ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => Complex.I)).mul hs)

/-- A harmless factor two bounds all real derivatives of the unit oscillation. -/
private theorem norm_iteratedFDeriv_oscillator_le (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n oscillator t‖ ≤ 2 := by
  let c : ℝ → ℂ := fun t => (Real.cos t : ℂ)
  let s : ℝ → ℂ := fun t => (Real.sin t : ℂ)
  have hc : ContDiff ℝ n c := Complex.ofRealCLM.contDiff.comp Real.contDiff_cos
  have hs : ContDiff ℝ n s := Complex.ofRealCLM.contDiff.comp Real.contDiff_sin
  have hcn : ‖iteratedFDeriv ℝ n c t‖ ≤ 1 := by
    rw [show c = Complex.ofRealLI ∘ Real.cos from rfl,
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left Real.contDiff_cos.contDiffAt le_rfl,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact Real.abs_iteratedDeriv_cos_le_one n t
  have hsn : ‖iteratedFDeriv ℝ n s t‖ ≤ 1 := by
    rw [show s = Complex.ofRealLI ∘ Real.sin from rfl,
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left Real.contDiff_sin.contDiffAt le_rfl,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact Real.abs_iteratedDeriv_sin_le_one n t
  have heq : oscillator = c + Complex.I • s := by
    funext t
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, c, s] using oscillator_eq t
  rw [heq, iteratedFDeriv_add_apply (f := c) (g := Complex.I • s)
    hc.contDiffAt ((hs.const_smul Complex.I).contDiffAt),
    iteratedFDeriv_const_smul_apply (a := Complex.I) hs.contDiffAt]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n c t‖ + ‖Complex.I • iteratedFDeriv ℝ n s t‖ := norm_add_le _ _
    _ ≤ 2 := by simpa only [norm_smul, Complex.norm_I, one_mul, one_add_one_eq_two] using add_le_add hcn hsn

/-- One summand of the complex lattice Fourier series. -/
@[expose] def fourierTerm (x : Site) (C : Site → ℝ) (y : Site) (k : Momentum) : ℂ :=
  (C y : ℂ) * Complex.exp ((momentumPhase x y k : ℂ) * Complex.I)

/-- The lattice Fourier series, with its base point made explicit. -/
@[expose] def latticeFourierSeries (x : Site) (C : Site → ℝ) (k : Momentum) : ℂ :=
  ∑' y : Site, fourierTerm x C y k

/-- The exact weighted absolute moment assumption needed for smoothness. -/
@[expose] def HasSummableMoments (x : Site) (C : Site → ℝ) : Prop :=
  ∀ n : ℕ, Summable (fun y : Site =>
    (1 + (siteRadius x y : ℝ)) ^ n * |C y|)

private theorem contDiff_fourierTerm (x : Site) (C : Site → ℝ) (y : Site) :
    ContDiff ℝ ∞ (fourierTerm x C y) := by
  exact contDiff_const.mul (contDiff_oscillator.comp (momentumPhase x y).contDiff)

/-- Uniform derivative majorant; all powers are natural powers. -/
theorem norm_iteratedFDeriv_fourierTerm_le (x : Site) (C : Site → ℝ)
    (n : ℕ) (y : Site) (k : Momentum) :
    ‖iteratedFDeriv ℝ n (fourierTerm x C y) k‖ ≤
      (2 * 2 ^ n) * ((1 + (siteRadius x y : ℝ)) ^ n * |C y|) := by
  have hs : ContDiff ℝ n (oscillator ∘ momentumPhase x y) :=
    (contDiff_oscillator.comp (momentumPhase x y).contDiff).of_le (by simp)
  have heq : fourierTerm x C y = (C y : ℂ) • (oscillator ∘ momentumPhase x y) := rfl
  rw [heq, iteratedFDeriv_const_smul_apply hs.contDiffAt, norm_smul,
    Complex.norm_real, Real.norm_eq_abs,
    (momentumPhase x y).iteratedFDeriv_comp_right
      (contDiff_oscillator.of_le (by simp) : ContDiff ℝ n oscillator) k le_rfl]
  have hp : 0 ≤ 1 + (siteRadius x y : ℝ) := by
    have h : (0 : ℝ) ≤ siteRadius x y := by exact_mod_cast siteRadius_nonneg x y
    linarith
  calc
    _ ≤ |C y| * (‖iteratedFDeriv ℝ n oscillator (momentumPhase x y k)‖ *
        ∏ _ : Fin n, ‖momentumPhase x y‖) :=
      mul_le_mul_of_nonneg_left (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _)
        (abs_nonneg _)
    _ = |C y| * (‖iteratedFDeriv ℝ n oscillator (momentumPhase x y k)‖ *
        ‖momentumPhase x y‖ ^ n) := by simp
    _ ≤ |C y| * (2 * (2 * (1 + (siteRadius x y : ℝ))) ^ n) := by
      gcongr
      · exact norm_iteratedFDeriv_oscillator_le n _
      · exact norm_momentumPhase_le x y
    _ = (2 * 2 ^ n) * ((1 + (siteRadius x y : ℝ)) ^ n * |C y|) := by
      rw [mul_pow]
      ring

/-- Absolute convergence at every momentum, so the Fourier series is not a
formal use of `tsum` on a divergent family. -/
theorem summable_fourierTerm (x : Site) (C : Site → ℝ)
    (hC : HasSummableMoments x C) (k : Momentum) :
    Summable (fun y => fourierTerm x C y k) := by
  apply Summable.of_norm_bounded ((hC 0).mul_left (2 * 2 ^ (0 : ℕ)))
  intro y
  simpa only [norm_iteratedFDeriv_zero] using norm_iteratedFDeriv_fourierTerm_le x C 0 y k

/-- Each differentiated series is itself absolutely summable. -/
theorem summable_iteratedFDeriv_fourierTerm (x : Site) (C : Site → ℝ)
    (hC : HasSummableMoments x C) (n : ℕ) (k : Momentum) :
    Summable (fun y => iteratedFDeriv ℝ n (fourierTerm x C y) k) :=
  Summable.of_norm_bounded ((hC n).mul_left (2 * 2 ^ n))
    (fun y => norm_iteratedFDeriv_fourierTerm_le x C n y k)

/-- Arbitrary polynomial moments give a smooth Fourier series in both momentum
coordinates jointly. -/
theorem contDiff_latticeFourierSeries (x : Site) (C : Site → ℝ)
    (hC : HasSummableMoments x C) : ContDiff ℝ ∞ (latticeFourierSeries x C) := by
  apply contDiff_tsum (fun y => contDiff_fourierTerm x C y)
    (v := fun n y => (2 * 2 ^ n) * ((1 + (siteRadius x y : ℝ)) ^ n * |C y|))
  · intro n _
    exact (hC n).mul_left _
  · intro n y k _
    exact norm_iteratedFDeriv_fourierTerm_le x C n y k

/-- Every order of Fréchet differentiation may be interchanged with the lattice
sum; convergence is controlled by the same explicit moment majorants. -/
theorem iteratedFDeriv_latticeFourierSeries (x : Site) (C : Site → ℝ)
    (hC : HasSummableMoments x C) (n : ℕ) (k : Momentum) :
    iteratedFDeriv ℝ n (latticeFourierSeries x C) k =
      ∑' y : Site, iteratedFDeriv ℝ n (fourierTerm x C y) k := by
  exact iteratedFDeriv_tsum_apply (fun y => contDiff_fourierTerm x C y)
    (v := fun n y => (2 * 2 ^ n) * ((1 + (siteRadius x y : ℝ)) ^ n * |C y|))
    (fun n _ => (hC n).mul_left _)
    (fun n y k _ => norm_iteratedFDeriv_fourierTerm_le x C n y k) (by simp) k

end Fourier

/-- The fixed-base-point quadrupolar structure factor of the actual infinite
configuration measure.  Under translation invariance it is independent of `x`. -/
@[expose] def quadrupolarStructureFactor (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (x : Fourier.Site) : Fourier.Momentum → ℂ :=
  Fourier.latticeFourierSeries x (infiniteCorrelation μ x)

/-- The literal Fourier-series convention, written without auxiliary pairings. -/
theorem quadrupolarStructureFactor_eq_tsum
    (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (x : Fourier.Site) (k : Fourier.Momentum) :
    quadrupolarStructureFactor μ x k =
      ∑' y : Fourier.Site, (infiniteCorrelation μ x y : ℂ) *
        Complex.exp (Complex.I *
          ((((y.1 - x.1 : ℤ) : ℝ) * k.1 + ((y.2 - x.2 : ℤ) : ℝ) * k.2 : ℝ) : ℂ)) := by
  simp only [quadrupolarStructureFactor, Fourier.latticeFourierSeries,
    Fourier.fourierTerm, Fourier.momentumPhase_apply, mul_comm Complex.I]

/-- The previously proved weighted summability supplies every moment needed by
Fourier analysis, including the unweighted absolute sum. -/
theorem hasSummableMoments_infiniteCorrelation_local_limit_signed (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (hμ : IsSignedFreeBoundaryLocalLimit β μ) (x : Fourier.Site) :
    Fourier.HasSummableMoments x (infiniteCorrelation μ x) := by
  intro n
  simpa only [Real.rpow_natCast] using
    weighted_summability_local_limit_signed β hβ μ hμ x (n : ℝ)

/-- All signed-coupling free-boundary local weak limits have a jointly smooth
quadrupolar structure factor. -/
theorem contDiff_quadrupolarStructureFactor_local_limit_signed (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (hμ : IsSignedFreeBoundaryLocalLimit β μ) (x : Fourier.Site) :
    ContDiff ℝ ∞ (quadrupolarStructureFactor μ x) :=
  Fourier.contDiff_latticeFourierSeries x (infiniteCorrelation μ x)
    (hasSummableMoments_infiniteCorrelation_local_limit_signed β hβ μ hμ x)

/-- Absolute convergence of the actual quadrupolar structure-factor series. -/
theorem summable_quadrupolarStructureFactor_local_limit_signed (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (hμ : IsSignedFreeBoundaryLocalLimit β μ) (x : Fourier.Site) (k : Fourier.Momentum) :
    Summable (fun y => Fourier.fourierTerm x (infiniteCorrelation μ x) y k) :=
  Fourier.summable_fourierTerm x (infiniteCorrelation μ x)
    (hasSummableMoments_infiniteCorrelation_local_limit_signed β hβ μ hμ x) k

/-- Every order of momentum differentiation of the actual quadrupolar structure
factor is given by termwise differentiation of its absolutely convergent series. -/
theorem iteratedFDeriv_quadrupolarStructureFactor_local_limit_signed
    (β : ℝ) (hβ : 0 ≤ β) (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (hμ : IsSignedFreeBoundaryLocalLimit β μ) (x : Fourier.Site)
    (n : ℕ) (k : Fourier.Momentum) :
    iteratedFDeriv ℝ n (quadrupolarStructureFactor μ x) k =
      ∑' y : Fourier.Site,
        iteratedFDeriv ℝ n (Fourier.fourierTerm x (infiniteCorrelation μ x) y) k :=
  Fourier.iteratedFDeriv_latticeFourierSeries x (infiniteCorrelation μ x)
    (hasSummableMoments_infiniteCorrelation_local_limit_signed β hβ μ hμ x) n k

/-- The original nonnegative-coupling local-limit interface retains the same
smoothness conclusion. -/
theorem contDiff_quadrupolarStructureFactor_local_limit (β : ℝ) (hβ : 0 ≤ β)
    (μ : MeasureTheory.ProbabilityMeasure InfiniteConfiguration)
    (hμ : IsFreeBoundaryLocalLimit β μ) (x : Fourier.Site) :
    ContDiff ℝ ∞ (quadrupolarStructureFactor μ x) := by
  apply Fourier.contDiff_latticeFourierSeries
  intro n
  simpa only [Real.rpow_natCast] using weighted_summability_local_limit β hβ μ hμ x (n : ℝ)

end
end RP2
