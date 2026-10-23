module

public import RP3.QuadraticFamilyKernel
public import RP3.QuadraticCoefficientBounds

public section

/-! # Quantitative contraction estimates for quadratic RP³
Adapted from OpenAI ClassicalON/FamilyEstimate, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
-/
namespace RP3.Quadratic
universe uV uE
noncomputable section
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem norm_avg_coeff_two (S : SpinSystem V E) (M v : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ a e σ, ‖S.mixedCoefficientObservable a e σ‖ ≤ M)
    (a : MixedAlgebra.Slot) (e : E) (F G : C((V → RP3.Spin), ℂ))
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ v)
    (hG : S.averageLinear (normObservable G * normObservable G) ≤ v) :
    ‖S.averageComplexLinear (S.mixedCoefficientObservable a e * F * G)‖ ≤ M*v :=
  S.norm_averageComplex_mul_mul_le_of_moments _ F G M v hM (hcoeff a e) hF hG

theorem norm_avg_coeff_coeff_const (S : SpinSystem V E) (M : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ a e σ, ‖S.mixedCoefficientObservable a e σ‖ ≤ M)
    (a b : MixedAlgebra.Slot) (e l : E) (z : ℂ) :
    ‖S.averageComplexLinear (S.mixedCoefficientObservable a e *
      S.mixedCoefficientObservable b l * ContinuousMap.const _ z)‖ ≤ M^2*‖z‖ := by
  apply S.norm_averageComplex_le_const
  intro σ
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg z)
  rw [pow_two]
  exact mul_le_mul (hcoeff a e σ) (hcoeff b l σ) (norm_nonneg _) hM

theorem norm_avg_coeff_const_current (S : SpinSystem V E) (M q : ℝ)
    (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hcoeff : ∀ a e σ, ‖S.mixedCoefficientObservable a e σ‖ ≤ M)
    (a : MixedAlgebra.Slot) (e : E) (z : ℂ)
    (hz : ‖z‖ ≤ Real.sqrt q) (F : C((V → RP3.Spin), ℂ))
    (hF : S.averageLinear (normObservable F * normObservable F) ≤ M*q) :
    ‖S.averageComplexLinear (S.mixedCoefficientObservable a e * ContinuousMap.const _ z * F)‖ ≤
      M*Real.sqrt M*q := by
  have hC (σ : V → RP3.Spin) :
      ‖(S.mixedCoefficientObservable a e * ContinuousMap.const (V → RP3.Spin) z) σ‖ ≤ M*‖z‖ := by
    simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hcoeff a e σ) (norm_nonneg z)
  calc _ ≤ (M*‖z‖)*Real.sqrt (M*q) :=
        S.norm_averageComplex_mul_le_of_moment _ F (M*‖z‖) (M*q)
          (mul_nonneg hM (norm_nonneg z)) hC hF
       _ ≤ (M*Real.sqrt q)*Real.sqrt (M*q) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz hM) (Real.sqrt_nonneg _)
       _ = M*Real.sqrt M*q := by
          rw [Real.sqrt_mul hM]
          calc _ = M*Real.sqrt M*(Real.sqrt q*Real.sqrt q) := by ring
               _ = _ := by rw [Real.mul_self_sqrt hq]

theorem norm_avg_coeff_const (S : SpinSystem V E) (M : ℝ)
    (hcoeff : ∀ a e σ, ‖S.mixedCoefficientObservable a e σ‖ ≤ M)
    (a : MixedAlgebra.Slot) (e : E) (z : ℂ) :
    ‖S.averageComplexLinear (S.mixedCoefficientObservable a e * ContinuousMap.const _ z)‖ ≤ M*‖z‖ := by
  apply S.norm_averageComplex_le_const
  intro σ
  simp only [ContinuousMap.mul_apply, ContinuousMap.const_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (hcoeff a e σ) (norm_nonneg z)

end SpinSystem
end
end RP3.Quadratic
