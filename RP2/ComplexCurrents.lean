import RP2.QuadraticPlaneResponse

/-!
# Complex currents for the quadratic interaction

This module extends the proved real gradient-current estimate to genuinely
complex vertex functions. The complex current is defined by its real and
imaginary parts, using the actual first derivative of the RP² energy.
No positivity of the response bilinear form is assumed.
-/

namespace RP2.Quadratic
noncomputable section
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

namespace SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- The oriented discrete gradient, also for complex potentials. -/
def edgeGradient (S : SpinSystem V E) {𝕜 : Type*} [Sub 𝕜] (f : V → 𝕜) : E → 𝕜 :=
  fun e => f (S.right e) - f (S.left e)

/-- The first derivative in a fixed real rotation axis, complexified linearly. -/
def complexCurrent (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) (σ : V → RP2.Spin) : ℂ :=
  ⟨S.firstEnergy (fun e => (h e).re • g) σ,
    S.firstEnergy (fun e => (h e).im • g) σ⟩

omit [Fintype V] in
@[simp] theorem complexCurrent_re (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) (σ : V → RP2.Spin) :
    (S.complexCurrent g h σ).re = S.firstEnergy (fun e => (h e).re • g) σ := rfl

omit [Fintype V] in
@[simp] theorem complexCurrent_im (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) (σ : V → RP2.Spin) :
    (S.complexCurrent g h σ).im = S.firstEnergy (fun e => (h e).im • g) σ := rfl

omit [Fintype V] in
theorem complexCurrent_eq_sum (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) (σ : V → RP2.Spin) :
    S.complexCurrent g h σ = ∑ e,
      ((2 * S.strength e *
        ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
        ⟪(σ (S.left e)).val, g (σ (S.right e)).val⟫_ℝ : ℝ) : ℂ) * h e := by
  apply Complex.ext <;>
    simp [complexCurrent, firstEnergy, smul_apply, real_inner_smul_right,
      Complex.re_sum, Complex.im_sum, mul_assoc, mul_left_comm, mul_comm]

omit [Fintype V] in
theorem complexCurrent_add (S : SpinSystem V E) (g : SpinOperator 3)
    (h k : E → ℂ) (σ : V → RP2.Spin) :
    S.complexCurrent g (h + k) σ =
      S.complexCurrent g h σ + S.complexCurrent g k σ := by
  simp only [S.complexCurrent_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype V] in
theorem complexCurrent_smul (S : SpinSystem V E) (g : SpinOperator 3)
    (c : ℂ) (h : E → ℂ) (σ : V → RP2.Spin) :
    S.complexCurrent g (c • h) σ = c * S.complexCurrent g h σ := by
  simp only [S.complexCurrent_eq_sum, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

omit [Fintype V] in
theorem complexCurrent_conj (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) (σ : V → RP2.Spin) :
    S.complexCurrent g (fun e => star (h e)) σ = star (S.complexCurrent g h σ) := by
  simp only [S.complexCurrent_eq_sum, map_sum, map_mul, Complex.star_def,
    Complex.conj_ofReal]

omit [Fintype V] in
theorem continuous_complexCurrent (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) : Continuous (S.complexCurrent g h) := by
  have he : S.complexCurrent g h = fun σ => ∑ e,
      ((2 * S.strength e *
        ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
        ⟪(σ (S.left e)).val, g (σ (S.right e)).val⟫_ℝ : ℝ) : ℂ) * h e :=
    funext (S.complexCurrent_eq_sum g h)
  rw [he]
  fun_prop

omit [Fintype V] in
theorem complexCurrent_gradient_normSq (S : SpinSystem V E) (g : SpinOperator 3)
    (f : V → ℂ) (σ : V → RP2.Spin) :
    Complex.normSq (S.complexCurrent g (S.edgeGradient f) σ) =
      (S.firstEnergy (S.axisGradient (fun x => (f x).re) g) σ)^2 +
      (S.firstEnergy (S.axisGradient (fun x => (f x).im) g) σ)^2 := by
  simp only [Complex.normSq_apply, complexCurrent, edgeGradient, axisGradient,
    Complex.sub_re, Complex.sub_im, pow_two]
  rfl

/-- Appendix A.1 for arbitrary complex potentials, proved by applying the
real Ward estimate separately to the real and imaginary parts. -/
theorem complex_gradient_current_bound (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (g : SpinOperator 3)
    (hg : g ∈ skewAdjoint (SpinOperator 3)) (hgn : ‖g‖ ≤ 1) (f : V → ℂ)
    (hP : ∀ x s, S.pin x = some s → f x = 0) :
    S.average (fun σ => Complex.normSq (S.complexCurrent g (S.edgeGradient f) σ)) ≤
      4 * β * ∑ e, Complex.normSq (S.edgeGradient f e) := by
  have hr := S.gradient_current_bound β hb g hg hgn (fun x => (f x).re)
    (fun x s hs => by rw [hP x s hs]; rfl)
  have hi := S.gradient_current_bound β hb g hg hgn (fun x => (f x).im)
    (fun x s hs => by rw [hP x s hs]; rfl)
  simp_rw [S.complexCurrent_gradient_normSq]
  change S.average
    ((fun σ => (S.firstEnergy (S.axisGradient (fun x => (f x).re) g) σ)^2) +
      (fun σ => (S.firstEnergy (S.axisGradient (fun x => (f x).im) g) σ)^2)) ≤ _
  rw [S.average_add
    (f := fun σ => (S.firstEnergy (S.axisGradient (fun x => (f x).re) g) σ)^2)
    (g := fun σ => (S.firstEnergy (S.axisGradient (fun x => (f x).im) g) σ)^2)
    ((S.continuous_firstEnergy _).pow 2) ((S.continuous_firstEnergy _).pow 2)]
  calc
    _ ≤ 4 * β * ∑ e, ((f (S.right e)).re - (f (S.left e)).re)^2 +
        4 * β * ∑ e, ((f (S.right e)).im - (f (S.left e)).im)^2 := add_le_add hr hi
    _ = _ := by
      simp only [edgeGradient, Complex.normSq_apply, Complex.sub_re,
        Complex.sub_im, pow_two, Finset.sum_add_distrib, mul_add]

omit [Fintype V] in
theorem abs_scalar_secondEnergy_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (g : SpinOperator 3) (hg : ‖g‖ ≤ 1)
    (h : E → ℝ) (σ : V → RP2.Spin) :
    |S.secondEnergy (fun e => h e • g) σ| ≤ 4 * β * ∑ e, (h e)^2 := by
  apply (S.abs_secondEnergy_le _ σ).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have hβ := (abs_nonneg _).trans (hb e)
  have hn : ‖h e • g‖ ≤ |h e| := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) hg
  have hn2 : ‖h e • g‖^2 ≤ (h e)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hb e) (by norm_num)) hn2
    (sq_nonneg _) (by positivity)

/-- The real value `R(h, conj h)` of the complex-bilinear second response.
The negative current-square term is retained explicitly. -/
def hermitianResponse (S : SpinSystem V E) (g : SpinOperator 3) (h : E → ℂ) : ℝ :=
  -S.average (fun σ =>
    S.secondEnergy (fun e => (h e).re • g) σ +
    S.secondEnergy (fun e => (h e).im • g) σ +
    Complex.normSq (S.complexCurrent g h σ))

/-- Appendix A.2: an upper bound for the actual second response. This uses
positivity only of the squared current, not of the response. -/
theorem hermitianResponse_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (g : SpinOperator 3) (hg : ‖g‖ ≤ 1)
    (h : E → ℂ) :
    S.hermitianResponse g h ≤ 4 * β * ∑ e, Complex.normSq (h e) := by
  let C := 4 * β * ∑ e, Complex.normSq (h e)
  have hp (σ : V → RP2.Spin) :
      -C ≤ S.secondEnergy (fun e => (h e).re • g) σ +
        S.secondEnergy (fun e => (h e).im • g) σ +
        Complex.normSq (S.complexCurrent g h σ) := by
    have hr := (abs_le.mp (S.abs_scalar_secondEnergy_le β hb g hg
      (fun e => (h e).re) σ)).1
    have hi := (abs_le.mp (S.abs_scalar_secondEnergy_le β hb g hg
      (fun e => (h e).im) σ)).1
    have hn := Complex.normSq_nonneg (S.complexCurrent g h σ)
    have hC : C = 4 * β * ∑ e, (h e).re^2 + 4 * β * ∑ e, (h e).im^2 := by
      simp only [C, Complex.normSq_apply, pow_two, Finset.sum_add_distrib, mul_add]
    linarith
  have hc : Continuous (fun σ =>
      S.secondEnergy (fun e => (h e).re • g) σ +
      S.secondEnergy (fun e => (h e).im • g) σ +
      Complex.normSq (S.complexCurrent g h σ)) := by
    exact ((S.continuous_secondEnergy _).add (S.continuous_secondEnergy _)).add
      (Complex.continuous_normSq.comp (S.continuous_complexCurrent g h))
  have h := S.average_mono continuous_const hc hp
  rw [S.average_const] at h
  unfold hermitianResponse
  linarith

end SpinSystem
end
end RP2.Quadratic
