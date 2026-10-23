module

public import RP2.QuadraticFamily

public section

/-!
# Paper notation for the pinned quadratic response

This interface fixes the sign and complex-conjugation conventions of the note.
`R` is complex bilinear, rather than sesquilinear. Its Hermitian evaluation is
`R S h (conjugate h)`, and is real; no positivity of this evaluation is asserted.
The concrete coefficient in `family_bound` is the proved squared-interaction
coefficient `4 * β`, which is stronger than the common `16 * β` bound.
-/

namespace RP2.Paper
noncomputable section
open RP2.Quadratic RP2.Fourier
open scoped BigOperators ComplexConjugate

universe uV uE uI
variable {V : Type uV} {E : Type uE} {I : Type uI}

/-- Pointwise complex conjugation, used explicitly in all response evaluations. -/
@[expose] def conjugate {A : Type*} (h : A → ℂ) : A → ℂ := fun a => conj (h a)

@[simp] theorem conjugate_conjugate {A : Type*} (h : A → ℂ) :
    conjugate (conjugate h) = h := by ext a; simp [conjugate]

section Response
variable [Fintype V] [Fintype E]

/-- The note's complex-bilinear response `R(h,k) = -D²W(0)[hc,kc]`.
The rotation axis is the fixed generator `axisC` from the concrete development. -/
@[expose] def R (S : SpinSystem V E) (h k : E → ℂ) : ℂ :=
  -S.complexSecondResponse h k

/-- Its real Hermitian evaluation. `R_hermitian_eq` proves that no imaginary
part is discarded by this definition. -/
@[expose] def hermitianR (S : SpinSystem V E) (h : E → ℂ) : ℝ :=
  (R S h (conjugate h)).re

theorem R_symm (S : SpinSystem V E) (h k : E → ℂ) : R S h k = R S k h := by
  unfold R
  rw [S.complexSecondResponse_symm]

theorem R_conjugate (S : SpinSystem V E) (h k : E → ℂ) :
    R S (conjugate h) (conjugate k) = conj (R S h k) := by
  have hp : S.complexSecondObservable (conjugate h) (conjugate k) =
      ⟨fun σ => conj (S.complexSecondObservable h k σ),
        Complex.continuous_conj.comp (S.complexSecondObservable h k).continuous⟩ := by
    ext σ
    simp only [SpinSystem.complexSecondObservable, ContinuousMap.coe_mk,
      SpinSystem.complexHessian, MixedAlgebra.weighted, conjugate, Pi.mul_apply,
      map_add, map_sum, map_mul, Complex.conj_ofReal]
    have hc (u : E → ℂ) : S.complexCurrent Rotation.axisC (conjugate u) σ =
        conj (S.complexCurrent Rotation.axisC u σ) := by
      change S.complexCurrent Rotation.axisC (fun e => conj (u e)) σ = _
      simpa only [Complex.star_def] using S.complexCurrent_conj Rotation.axisC u σ
    rw [hc, hc]
  simp only [R, SpinSystem.complexSecondResponse, hp, S.averageComplex_conj, map_neg]

/-- Conjugate symmetry of the associated Hermitian pairing. -/
theorem R_hermitian_symm (S : SpinSystem V E) (h k : E → ℂ) :
    conj (R S k (conjugate h)) = R S h (conjugate k) := by
  rw [← R_conjugate, conjugate_conjugate, R_symm]

/-- The Hermitian evaluation is an actual real number, with no sign assumption. -/
theorem R_hermitian_im (S : SpinSystem V E) (h : E → ℂ) :
    (R S h (conjugate h)).im = 0 := by
  have he := congrArg Complex.im (R_hermitian_symm S h h)
  simp only [Complex.conj_im] at he
  linarith

theorem R_hermitian_eq (S : SpinSystem V E) (h : E → ℂ) :
    R S h (conjugate h) = (hermitianR S h : ℂ) := by
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im, R_hermitian_im]

/-- Restriction of the complex-bilinear response to real edge fields. -/
theorem R_ofReal (S : SpinSystem V E) (h k : E → ℝ) :
    R S (fun e => (h e : ℂ)) (fun e => (k e : ℂ)) =
      (-S.secondAxisResponse h k : ℝ) := by
  simp only [R, S.complexSecondResponse_ofReal, Complex.ofReal_neg]

/-- The elementary second-response bound, without a positivity assumption on `R`. -/
theorem hermitianR_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β) (h : E → ℂ) :
    hermitianR S h ≤ 4 * β * ∑ e, ‖h e‖ ^ 2 := by
  exact S.complexSecondResponse_upper β hb h

end Response

section Family
variable [Fintype V] [Fintype E] [Fintype I]

/-- The paper's Gram kernel `T(e,l) = ∑ᵢ dfᵢ(e) conj(dfᵢ(l))`. -/
@[expose] def T (S : SpinSystem V E) (f : I → V → ℂ) : E → E → ℂ :=
  familyKernel (fun i => S.edgeGradient (f i))

/-- The current `q = ∑ᵢ S(fᵢ, conjugate fᵢ)`, with the paper's factor `1/2`. -/
@[expose] def q (S : SpinSystem V E) (f : I → V → ℂ) : E → ℂ :=
  ∑ i, S.commutatorForm (f i) (conjugate (f i))

omit [Fintype V] [Fintype E] in
/-- The Gram kernel is Hermitian, fixing the order of its two edge indices. -/
theorem T_conjugate (S : SpinSystem V E) (f : I → V → ℂ) (e l : E) :
    conj (T S f e l) = T S f l e := by
  simp only [T, familyKernel, map_sum, map_mul, starRingEnd_self_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

omit [Fintype V] [Fintype E] in
/-- Every diagonal commutator sum is purely imaginary. -/
theorem q_conjugate (S : SpinSystem V E) (f : I → V → ℂ) :
    conjugate (q S f) = -q S f := by
  ext e
  simp only [conjugate, q, Finset.sum_apply, map_sum, Pi.neg_apply,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [SpinSystem.commutatorForm, SpinSystem.complexCross, Pi.smul_apply,
    smul_eq_mul, conjugate, map_mul, map_sub, map_div₀, map_one, map_ofNat,
    starRingEnd_self_apply]
  ring

omit [Fintype V] in
/-- The Hilbert--Schmidt norm squared written in the paper's edge indices. -/
theorem T_HSSquare (S : SpinSystem V E) (f : I → V → ℂ) :
    familyHSSquare (fun i => S.edgeGradient (f i)) =
      ∑ e, ∑ l, ‖T S f e l‖ ^ 2 := rfl

/-- The fourth-order family inequality in the note's `R`, `T`, and `q` notation.
It applies to arbitrary signed couplings bounded in absolute value and to
arbitrary prescribed directors, provided each test function vanishes at pins. -/
theorem family_bound (S : SpinSystem V E) (β : ℝ) (hβ : 0 ≤ β)
    (hb : ∀ e, |S.strength e| ≤ β)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) :
    hermitianR S (q S f) ≤
      (6 * (16 * β)^2 + 4 * (16 * β) * Real.sqrt (16 * β) + 16 * β) *
        (∑ e, ∑ l, ‖T S f e l‖^2) +
      (4 * β) * ∑ i, ∑ j,
        min (‖f i‖^2 * ∑ e, ‖S.edgeGradient (f j) e‖^2)
          (‖f j‖^2 * ∑ e, ‖S.edgeGradient (f i) e‖^2) := by
  exact S.rotation_family_bound β hβ hb f hP

end Family
end
end RP2.Paper
