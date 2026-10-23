import RP3.QuadraticComplexWard
import RP3.QuadraticCoefficientBounds
import RP3.FourierAll
/-!
# Actual finite-family observables for RP³
Adapted from OpenAI ClassicalON FamilyKernel/FamilyBound, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
-/
namespace RP3.Quadratic
universe uV uE uI uJ uΩ
noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open RP3.Fourier
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SpinSystem
variable {V : Type uV} {E : Type uE} {I : Type uI} [Fintype V] [Fintype E] [Fintype I]

omit [Fintype V] [Fintype I] in
def currentObservable (S : SpinSystem V E) (M : SpinOperator 4) (u : E → ℂ) :
    C((V → RP3.Spin), ℂ) := ⟨_, S.continuous_complexCurrent M u⟩

omit [Fintype V] [Fintype I] in
def mixedCoefficientObservable (S : SpinSystem V E) (a : MixedAlgebra.Slot) (e : E) :
    C((V → RP3.Spin), ℂ) := ⟨fun σ => ((S.mixedCoefficients σ).get a e : ℂ), by
  cases a <;> unfold MixedAlgebra.Coeffs.get mixedCoefficients localInner <;> fun_prop⟩

omit [Fintype V] [Fintype I] in
def mixedWeightedObservable (S : SpinSystem V E) (a : MixedAlgebra.Slot) (u : E → ℂ) :
    C((V → RP3.Spin), ℂ) := ∑ e, S.mixedCoefficientObservable a e * ContinuousMap.const _ (u e)

omit [Fintype V] [Fintype I] [Fintype E] in
def conjugateObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℂ) :=
  ⟨fun σ => conj (f σ), Complex.continuous_conj.comp f.continuous⟩

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem conjugateObservable_apply {Ω : Type uΩ} [TopologicalSpace Ω]
    (f : C(Ω, ℂ)) (σ : Ω) : conjugateObservable f σ = conj (f σ) := rfl

omit [Fintype V] [Fintype I] [Fintype E] in
@[simp] theorem normObservable_conjugate {Ω : Type uΩ} [TopologicalSpace Ω]
    (f : C(Ω, ℂ)) : normObservable (conjugateObservable f) = normObservable f := by
  ext σ
  exact Complex.norm_conj (f σ)


omit [Fintype V] [Fintype I] in
@[simp] theorem currentObservable_conj (S : SpinSystem V E) (M : SpinOperator 4)
    (u : E → ℂ) : S.currentObservable M (fun e => conj (u e)) =
      conjugateObservable (S.currentObservable M u) := by
  ext σ
  exact S.complexCurrent_conj M u σ

omit [Fintype V] [Fintype I] in
@[simp] theorem mixedCoefficientObservable_conj (S : SpinSystem V E)
    (a : MixedAlgebra.Slot) (e : E) :
    conjugateObservable (S.mixedCoefficientObservable a e) = S.mixedCoefficientObservable a e := by
  ext σ
  exact Complex.conj_ofReal _

omit [Fintype V] [Fintype E] in
theorem familyKernel_differential (S : SpinSystem V E) (f : I → V → ℂ) (e : E) :
    familyKernel (fun i => S.edgeGradient (f i)) e =
      S.edgeGradient (fun x => ∑ i, S.edgeGradient (f i) e * conj (f i x)) := by
  funext l
  simp only [familyKernel, edgeGradient, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem row_current_moment (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β)
    (M : SpinOperator 4) (hM : M ∈ skewAdjoint (SpinOperator 4)) (hMn : ‖M‖ ≤ 1)
    (f : I → V → ℂ) (hP : ∀ i x s, S.pin x = some s → f i x = 0) (e : E) :
    S.averageLinear (normObservable (S.currentObservable M
      (familyKernel (fun i => S.edgeGradient (f i)) e)) *
      normObservable (S.currentObservable M
      (familyKernel (fun i => S.edgeGradient (f i)) e))) ≤
        4 * β * rowSquare (fun i => S.edgeGradient (f i)) e := by
  have hp : ∀ x s, S.pin x = some s →
      (∑ i, S.edgeGradient (f i) e * conj (f i x)) = 0 := by
    intro x s hs
    simp [hP _ x s hs]
  have h := S.complex_gradient_current_bound β hb M hM hMn
    (fun x => ∑ i, S.edgeGradient (f i) e * conj (f i x)) hp
  rw [← S.familyKernel_differential f e] at h
  change S.average (fun σ =>
    ‖S.complexCurrent M (familyKernel (fun i => S.edgeGradient (f i)) e) σ‖ *
    ‖S.complexCurrent M (familyKernel (fun i => S.edgeGradient (f i)) e) σ‖) ≤ _
  simpa only [rowSquare, ← Complex.sq_norm, pow_two] using h

omit [Fintype V] [Fintype E] [Fintype I] in
theorem mixedCoefficientObservable_norm_le (S : SpinSystem V E) (β : ℝ)
    (hb : ∀ e, |S.strength e| ≤ β)
    (a : MixedAlgebra.Slot) (e : E) (σ : V → RP3.Spin) :
    ‖S.mixedCoefficientObservable a e σ‖ ≤ 16 * β := by
  change ‖(((S.mixedCoefficients σ).get a e : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact S.abs_mixedCoefficient_le_sixteen β hb a σ e

omit [Fintype I] in
theorem averageComplex_pos_square (S : SpinSystem V E) (F : C((V → RP3.Spin), ℂ)) :
    0 ≤ (S.averageComplexLinear (F * conjugateObservable F)).re := by
  rw [S.averageComplex_re]
  apply S.averageLinear_nonneg
  intro σ
  change 0 ≤ (F σ * conj (F σ)).re
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

omit [Fintype I] in
theorem norm_averageComplex_sum_le {J : Type uJ} [Fintype J]
    (S : SpinSystem V E) (F : J → C((V → RP3.Spin), ℂ)) (bound : J → ℝ)
    (hF : ∀ j, ‖S.averageComplexLinear (F j)‖ ≤ bound j) :
    ‖S.averageComplexLinear (∑ j, F j)‖ ≤ ∑ j, bound j := by
  rw [map_sum]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hF j)

def familyPaired (S : SpinSystem V E) (u : I → E → ℂ) : C((V → RP3.Spin), ℂ) :=
  ∑ i, (S.currentObservable axisA (u i) *
    S.currentObservable axisB (fun e => conj (u i e)) +
    S.mixedWeightedObservable .ab (fun e => u i e * conj (u i e)))

def familyRemainder (S : SpinSystem V E) (u : I → E → ℂ) : C((V → RP3.Spin), ℂ) :=
  let T := familyKernel u
  let X := fun M e => S.currentObservable M (T e)
  let C := S.mixedCoefficientObservable
  let bar := conjugateObservable
  let k := fun z => ContinuousMap.const (V → RP3.Spin) z
  (∑ e, C .aa e * X axisB e * bar (X axisB e)) +
  (∑ e, C .ab e * X axisB e * X axisA e) +
  (∑ e, C .ab e * bar (X axisA e) * bar (X axisB e)) +
  (∑ e, C .bb e * bar (X axisA e) * X axisA e) +
  (∑ e, ∑ l, C .aa e * C .bb l * k (T e l * conj (T e l))) +
  (∑ e, ∑ l, C .ab e * C .ab l * k (T e l ^ 2)) +
  (∑ e, C .aab e * k (T e e) * bar (X axisB e)) +
  (∑ e, C .abb e * k (T e e) * X axisA e) +
  (∑ e, C .aab e * k (conj (T e e)) * X axisB e) +
  (∑ e, C .abb e * k (conj (T e e)) * bar (X axisA e)) +
  (∑ e, C .aabb e * k (T e e * conj (T e e)))

omit [Fintype V] in

theorem familyObservable_contraction (S : SpinSystem V E) (u : I → E → ℂ) :
    (∑ i, ∑ j, S.complexMixedObservable (u i) (fun e => conj (u i e))
      (fun e => conj (u j e)) (u j)) =
        S.familyPaired u * conjugateObservable (S.familyPaired u) + S.familyRemainder u := by
  ext σ
  have h := MixedAlgebra.four_family_contraction (S.complexCoefficients σ) u
    (fun i e => conj (u i e)) (fun i e => conj (u i e)) u
  simp only [ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    complexMixedObservable, ContinuousMap.coe_mk]
  rw [h]
  simp only [familyPaired, familyRemainder, ContinuousMap.sum_apply,
    ContinuousMap.add_apply, ContinuousMap.mul_apply, conjugateObservable_apply,
    ContinuousMap.const_apply, currentObservable, mixedCoefficientObservable,
    ContinuousMap.coe_mk, MixedAlgebra.paired, MixedAlgebra.kernel,
    familyKernel, complexCoefficients, MixedAlgebra.Coeffs.map,
    mixedCoefficients, Function.comp_def, Complex.ofRealHom_eq_coe,
    complexCurrent_eq_sum, mixedWeightedObservable, MixedAlgebra.Coeffs.get, localInner,
    map_sum, map_add, map_mul,
    starRingEnd_self_apply, pow_two]
  congr 1
  all_goals simp only [MixedAlgebra.weighted, MixedAlgebra.kernel, familyKernel,
    map_sum, map_mul, map_add, map_ofNat, Complex.conj_ofReal,
    starRingEnd_self_apply, Pi.mul_apply, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_pow, one_apply_eq_self, mul_assoc]


end SpinSystem
end
end RP3.Quadratic
