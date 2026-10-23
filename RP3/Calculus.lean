module

public import RP3.MathlibImports

public section

/-!
Adapted from OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, licensed under Apache-2.0.
Copyright OpenAI. The namespace and imports have been changed and the
interaction-independent lemmas separated from the O(n) Gibbs model.
-/

namespace RP3
universe uΩ uF
open MeasureTheory
noncomputable section

theorem hasDerivAt_integral_compact
    {Ω : Type uΩ} {F : Type uF} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f fd : ℝ → Ω → F)
    (hf : Continuous (Function.uncurry f)) (hfd : Continuous (Function.uncurry fd))
    (hd : ∀ t ω, HasDerivAt (fun u => f u ω) (fd t ω) t) (t : ℝ) :
    HasDerivAt (fun u => ∫ ω, f u ω ∂μ) (∫ ω, fd t ω ∂μ) t := by
  have hi (u : ℝ) : Integrable (f u) μ :=
    (hf.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hdi (u : ℝ) : Integrable (fd u) μ :=
    (hfd.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := (((isCompact_closedBall t 1).prod
    (isCompact_univ : IsCompact (Set.univ : Set Ω))).image hfd).isBounded.exists_norm_le
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.closedBall t 1) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds t zero_lt_one)
    (Filter.Eventually.of_forall fun u => (hi u).aestronglyMeasurable)
    (hi t) (hdi t).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω u hu => hC _ ⟨(u, ω), ⟨hu, Set.mem_univ _⟩, rfl⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun ω u _ => hd u ω)).2

@[expose] def fourthBell {Ω : Type uΩ} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (F 0 t ω) * (F 4 t ω + 4 * F 1 t ω * F 3 t ω + 3 * (F 2 t ω)^2 +
    6 * (F 1 t ω)^2 * F 2 t ω + (F 1 t ω)^4)

theorem iteratedDeriv_four_integral_exp
    {Ω : Type uΩ} [TopologicalSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : ℕ → ℝ → Ω → ℝ)
    (hC : ∀ k, Continuous (Function.uncurry (F k)))
    (hD : ∀ k t ω, HasDerivAt (fun u => F k u ω) (F (k+1) t ω) t) (t : ℝ) :
    iteratedDeriv 4 (fun u => ∫ ω, Real.exp (F 0 u ω) ∂μ) t =
      ∫ ω, fourthBell F t ω ∂μ := by
  let w0 := fun u ω => Real.exp (F 0 u ω)
  let w1 := fun u ω => Real.exp (F 0 u ω) * F 1 u ω
  let w2 := fun u ω => Real.exp (F 0 u ω) * (F 2 u ω + (F 1 u ω)^2)
  let w3 := fun u ω => Real.exp (F 0 u ω) *
    (F 3 u ω + 3 * F 1 u ω * F 2 u ω + (F 1 u ω)^3)
  let w4 := fourthBell F
  have c0 : Continuous (Function.uncurry w0) := (hC 0).rexp
  have c1 : Continuous (Function.uncurry w1) := (hC 0).rexp.mul (hC 1)
  have c2 : Continuous (Function.uncurry w2) :=
    (hC 0).rexp.mul ((hC 2).add ((hC 1).pow 2))
  have c3 : Continuous (Function.uncurry w3) := (hC 0).rexp.mul
    (((hC 3).add (((hC 1).const_mul 3).mul (hC 2))).add ((hC 1).pow 3))
  have c4 : Continuous (Function.uncurry w4) := (hC 0).rexp.mul
    (((((hC 4).add (((hC 1).const_mul 4).mul (hC 3))).add
      (((hC 2).pow 2).const_mul 3)).add ((((hC 1).pow 2).const_mul 6).mul
        (hC 2))).add ((hC 1).pow 4))
  have d0 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w0 v ω) (w1 u ω) u := (hD 0 u ω).exp
  have d1 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w1 v ω) (w2 u ω) u :=
    ((d0 u ω).mul (hD 1 u ω)).congr_deriv (by dsimp [w0, w1, w2]; ring)
  have d2 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w2 v ω) (w3 u ω) u :=
    ((d0 u ω).mul ((hD 2 u ω).add ((hD 1 u ω).pow 2))).congr_deriv
      (by dsimp [w0, w1, w3]; ring)
  have d3 (u : ℝ) (ω : Ω) : HasDerivAt (fun v => w3 v ω) (w4 u ω) u :=
    ((d0 u ω).mul (((hD 3 u ω).add (((hD 1 u ω).const_mul 3).mul
      (hD 2 u ω))).add ((hD 1 u ω).pow 3))).congr_deriv
      (by dsimp [w0, w1, w4, fourthBell]; ring)
  have e0 : deriv (fun u => ∫ ω, w0 u ω ∂μ) = (fun u => ∫ ω, w1 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w0 w1 c0 c1 d0 u).deriv
  have e1 : deriv (fun u => ∫ ω, w1 u ω ∂μ) = (fun u => ∫ ω, w2 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w1 w2 c1 c2 d1 u).deriv
  have e2 : deriv (fun u => ∫ ω, w2 u ω ∂μ) = (fun u => ∫ ω, w3 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w2 w3 c2 c3 d2 u).deriv
  have e3 : deriv (fun u => ∫ ω, w3 u ω ∂μ) = (fun u => ∫ ω, w4 u ω ∂μ) :=
    funext fun u => (hasDerivAt_integral_compact μ w3 w4 c3 c4 d3 u).deriv
  change iteratedDeriv 4 (fun u => ∫ ω, w0 u ω ∂μ) t = ∫ ω, w4 t ω ∂μ
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, e0, e1, e2, e3]

end
end RP3
