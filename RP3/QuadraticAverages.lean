module

public import RP3.QuadraticPlaneResponse

public section
/-!
# Real and complex Gibbs expectation as linear maps
Adapted from OpenAI's ClassicalON MixedWard and ComplexWard, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
-/
namespace RP3.Quadratic
universe uV uE uΩ
noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

@[expose] def averageLinear (S : SpinSystem V E) : C((V → RP3.Spin), ℝ) →ₗ[ℝ] ℝ where
  toFun f := S.average f
  map_add' f g := S.average_add f.continuous g.continuous
  map_smul' r f := S.average_mul_const r f

@[simp] theorem averageLinear_apply (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℝ)) : S.averageLinear f = S.average f := rfl

theorem integrable_complex_integrand (S : SpinSystem V E)
    {f : (V → RP3.Spin) → ℂ} (hf : Continuous f) :
    Integrable (fun σ => f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ)) S.reference :=
  (hf.mul (Complex.continuous_ofReal.comp (S.continuous_energy _).rexp)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

@[expose] def averageComplexLinear (S : SpinSystem V E) : C((V → RP3.Spin), ℂ) →ₗ[ℂ] ℂ where
  toFun f := (∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_mul]
    rw [integral_add (S.integrable_complex_integrand f.continuous)
      (S.integrable_complex_integrand g.continuous), add_div]
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul, RingHom.id_apply, mul_div_assoc]

@[expose] def ofRealObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℝ)) : C(Ω, ℂ) :=
  ⟨fun σ => (f σ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem averageComplex_ofReal (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℝ)) :
    S.averageComplexLinear (ofRealObservable f) = (S.averageLinear f : ℂ) := by
  change (∫ σ, (f σ : ℂ) * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ) = _
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, ← Complex.ofReal_div]
  rfl


@[expose] def normObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => ‖f σ‖, f.continuous.norm⟩

@[expose] def reObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => (f σ).re, Complex.continuous_re.comp f.continuous⟩

@[expose] def imObservable {Ω : Type uΩ} [TopologicalSpace Ω] (f : C(Ω, ℂ)) : C(Ω, ℝ) :=
  ⟨fun σ => (f σ).im, Complex.continuous_im.comp f.continuous⟩

theorem averageLinear_nonneg (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℝ)) (hf : ∀ σ, 0 ≤ f σ) : 0 ≤ S.averageLinear f :=
  S.average_nonneg hf

theorem averageLinear_mono (S : SpinSystem V E)
    (f g : C((V → RP3.Spin), ℝ)) (hfg : ∀ σ, f σ ≤ g σ) :
    S.averageLinear f ≤ S.averageLinear g := S.average_mono f.continuous g.continuous hfg

theorem averageLinear_mul_self_nonneg (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℝ)) : 0 ≤ S.averageLinear (f*f) :=
  S.averageLinear_nonneg _ (fun σ => mul_self_nonneg (f σ))

theorem averageLinear_cauchySchwarz (S : SpinSystem V E)
    (f g : C((V → RP3.Spin), ℝ)) :
    (S.averageLinear (f*g))^2 ≤ S.averageLinear (f*f) * S.averageLinear (g*g) := by
  have hp (t : ℝ) : 0 ≤ S.averageLinear (f*f) * (t*t) +
      (2*S.averageLinear (f*g))*t + S.averageLinear (g*g) := by
    have h := S.averageLinear_mul_self_nonneg (t • f + g)
    have he : (t • f + g)*(t • f + g) =
        (t*t) • (f*f) + (2*t) • (f*g) + g*g := by
      ext σ
      simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply,
        ContinuousMap.smul_apply, smul_eq_mul]
      ring
    rw [he, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
    nlinarith
  have h := discrim_le_zero hp
  unfold discrim at h
  nlinarith

theorem averageLinear_mul_le_sqrt (S : SpinSystem V E)
    (f g : C((V → RP3.Spin), ℝ)) :
    S.averageLinear (f*g) ≤
      Real.sqrt (S.averageLinear (f*f)) * Real.sqrt (S.averageLinear (g*g)) := by
  rw [← Real.sqrt_mul (S.averageLinear_mul_self_nonneg f)]
  exact Real.le_sqrt_of_sq_le (S.averageLinear_cauchySchwarz f g)

theorem norm_averageComplex_le (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℂ)) :
    ‖S.averageComplexLinear f‖ ≤ S.averageLinear (normObservable f) := by
  change ‖(∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (S.Z_pos _)]
  calc _ ≤ (∫ σ, ‖f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ)‖ ∂S.reference) /
      S.Z (fun _ => 1) :=
      div_le_div_of_nonneg_right (norm_integral_le_integral_norm _) (S.Z_pos _).le
    _ = S.averageLinear (normObservable f) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      rfl

theorem averageComplex_re (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℂ)) :
    (S.averageComplexLinear f).re = S.averageLinear (reObservable f) := by
  change ((∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ)).re = _
  rw [Complex.div_ofReal_re]
  have h := integral_re (S.integrable_complex_integrand f.continuous)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rfl

theorem averageComplex_conj (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℂ)) :
    S.averageComplexLinear ⟨fun σ => conj (f σ), Complex.continuous_conj.comp f.continuous⟩ =
      conj (S.averageComplexLinear f) := by
  change (∫ σ, conj (f σ) * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
    (S.Z (fun _ => 1) : ℂ) =
      conj ((∫ σ, f σ * (Real.exp (S.energy (fun _ => 1) σ) : ℂ) ∂S.reference) /
        (S.Z (fun _ => 1) : ℂ))
  conv_lhs => arg 1; arg 2; ext σ; rw [← Complex.conj_ofReal (Real.exp _), ← map_mul]
  rw [integral_conj, map_div₀]
  congr 1
  exact (Complex.conj_ofReal _).symm

@[simp] theorem averageLinear_const (S : SpinSystem V E) (c : ℝ) :
    S.averageLinear (ContinuousMap.const _ c) = c := S.average_const c

@[simp] theorem averageLinear_one (S : SpinSystem V E) : S.averageLinear 1 = 1 :=
  S.average_const 1

@[simp] theorem normObservable_mul {Ω : Type uΩ} [TopologicalSpace Ω] (f g : C(Ω, ℂ)) :
    normObservable (f*g) = normObservable f * normObservable g := by
  ext x
  exact norm_mul (f x) (g x)

theorem norm_averageComplex_le_const (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℂ)) (c : ℝ) (h : ∀ σ, ‖f σ‖ ≤ c) :
    ‖S.averageComplexLinear f‖ ≤ c := by
  calc _ ≤ S.averageLinear (normObservable f) := S.norm_averageComplex_le f
       _ ≤ S.averageLinear (ContinuousMap.const _ c) := S.averageLinear_mono _ _ h
       _ = c := S.averageLinear_const c

theorem norm_averageComplex_mul_le (S : SpinSystem V E)
    (f g : C((V → RP3.Spin), ℂ)) :
    ‖S.averageComplexLinear (f*g)‖ ≤
      Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
      Real.sqrt (S.averageLinear (normObservable g * normObservable g)) := by
  calc _ ≤ S.averageLinear (normObservable (f*g)) := S.norm_averageComplex_le _
       _ = S.averageLinear (normObservable f * normObservable g) := by rw [normObservable_mul]
       _ ≤ _ := S.averageLinear_mul_le_sqrt _ _

theorem averageLinear_norm_le_sqrt (S : SpinSystem V E)
    (f : C((V → RP3.Spin), ℂ)) :
    S.averageLinear (normObservable f) ≤
      Real.sqrt (S.averageLinear (normObservable f * normObservable f)) := by
  simpa only [mul_one, one_mul, S.averageLinear_one, Real.sqrt_one] using
    S.averageLinear_mul_le_sqrt (normObservable f) 1

theorem norm_averageComplex_mul_mul_le (S : SpinSystem V E)
    (a f g : C((V → RP3.Spin), ℂ)) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c *
      (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
       Real.sqrt (S.averageLinear (normObservable g * normObservable g))) := by
  have hpt : ∀ σ, normObservable (a*f*g) σ ≤
      (c • (normObservable f * normObservable g)) σ := by
    intro σ
    change ‖a σ*f σ*g σ‖ ≤ c * (‖f σ‖*‖g σ‖)
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_right (ha σ) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc _ ≤ S.averageLinear (normObservable (a*f*g)) := S.norm_averageComplex_le _
       _ ≤ S.averageLinear (c • (normObservable f * normObservable g)) :=
          S.averageLinear_mono _ _ hpt
       _ = c * S.averageLinear (normObservable f * normObservable g) := by
          rw [map_smul, smul_eq_mul]
       _ ≤ _ := mul_le_mul_of_nonneg_left (S.averageLinear_mul_le_sqrt _ _) hc

theorem norm_averageComplex_mul_mul_le_of_moments (S : SpinSystem V E)
    (a f g : C((V → RP3.Spin), ℂ)) (c v : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c)
    (hf : S.averageLinear (normObservable f * normObservable f) ≤ v)
    (hg : S.averageLinear (normObservable g * normObservable g) ≤ v) :
    ‖S.averageComplexLinear (a*f*g)‖ ≤ c*v := by
  have hv : 0 ≤ v := (S.averageLinear_mul_self_nonneg (normObservable f)).trans hf
  calc _ ≤ c * (Real.sqrt (S.averageLinear (normObservable f * normObservable f)) *
      Real.sqrt (S.averageLinear (normObservable g * normObservable g))) :=
      S.norm_averageComplex_mul_mul_le a f g c hc ha
       _ ≤ c * (Real.sqrt v * Real.sqrt v) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
              (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hc
       _ = c*v := by rw [Real.mul_self_sqrt hv]

theorem norm_averageComplex_mul_le_of_moment (S : SpinSystem V E)
    (a f : C((V → RP3.Spin), ℂ)) (c v : ℝ) (hc : 0 ≤ c)
    (ha : ∀ σ, ‖a σ‖ ≤ c)
    (hf : S.averageLinear (normObservable f * normObservable f) ≤ v) :
    ‖S.averageComplexLinear (a*f)‖ ≤ c*Real.sqrt v := by
  have h := S.norm_averageComplex_mul_mul_le a f 1 c hc ha
  simp only [mul_one] at h
  have h1 : normObservable (1 : C((V → RP3.Spin), ℂ)) = 1 := by
    ext σ
    change ‖(1 : ℂ)‖ = (1 : ℝ)
    exact norm_one
  rw [h1, mul_one, S.averageLinear_one, Real.sqrt_one, mul_one] at h
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hf) hc)


end SpinSystem
end
end RP3.Quadratic
