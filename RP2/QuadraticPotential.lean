import RP2.QuadraticSecondGauge
import RP2.TetrahedralPaths
import RP2.PeriodicODE

/-! Gauge shifts and boundary rotation paths for the actual squared RP² interaction.
Adapted from OpenAI ClassicalON/PotentialRotation.lean and PeriodicPartition.lean
at adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0). -/

namespace RP2

universe uE uV

noncomputable section
open MeasureTheory
open RP2.Rotation hiding Spin
namespace Quadratic
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def potentialRotation (f : V → ℝ) (t : ℝ) (x : V) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  rotationExp ((t*f x) • axisC) (skewAdjoint.smul_mem _ axisC_skew)

def rotatePotential (S : SpinSystem V E) (f : V → ℝ) (t : ℝ) : SpinSystem V E :=
  S.rotatePins (potentialRotation f t)

def potentialOperators (S : SpinSystem V E) (f : V → ℝ) : E → SpinOperator 3 :=
  fun e => S.edgeGradient f e • axisC

omit [Fintype V] [Fintype E] in
theorem gauge_potential_shift (S : SpinSystem V E) (f : V → ℝ) (t u : ℝ) :
    S.gauge (fun e => NormedSpace.exp (u • S.potentialOperators f e)) (potentialRotation f t) =
      (fun e => NormedSpace.exp ((t+u) • S.potentialOperators f e)) := by
  funext e
  apply ContinuousLinearMap.ext
  intro v
  change (potentialRotation f t (S.left e)).symm
    (NormedSpace.exp (u • S.potentialOperators f e) (potentialRotation f t (S.right e) v)) = _
  simp only [potentialRotation,rotationExp_symm_apply,rotationExp_apply,potentialOperators,
    smul_smul,← neg_smul (t*f (S.left e)) axisC]
  rw [← mul_apply_eq_comp,← mul_apply_eq_comp,← exp_smul_add,← exp_smul_add]
  apply congrArg (fun r : ℝ => NormedSpace.exp (r • axisC) v)
  simp only [edgeGradient]
  ring

theorem potential_shift_Z (S : SpinSystem V E) (f : V → ℝ) (t u : ℝ) :
    S.Z (fun e => NormedSpace.exp ((t+u) • S.potentialOperators f e)) =
      (S.rotatePotential f t).Z (fun e => NormedSpace.exp (u • S.potentialOperators f e)) := by
  rw [← S.gauge_potential_shift]
  exact S.Z_gauge _ _

theorem potential_shift_first (S : SpinSystem V E) (f : V → ℝ) (t u : ℝ) :
    (∫ σ, S.firstWeight (S.potentialOperators f) (t+u) σ ∂S.reference) =
      ∫ σ, (S.rotatePotential f t).firstWeight (S.potentialOperators f) u σ ∂(S.rotatePotential f t).reference := by
  have h := (S.hasDerivAt_twistZ (S.potentialOperators f) (t+u)).comp u
    ((hasDerivAt_id u).const_add t)
  simp only [mul_one] at h
  have he : (fun v => S.Z (fun e => NormedSpace.exp ((t+v) • S.potentialOperators f e))) =
      (fun v => (S.rotatePotential f t).Z (fun e => NormedSpace.exp (v • S.potentialOperators f e))) :=
    funext fun v => S.potential_shift_Z f t v
  change HasDerivAt (fun v => S.Z (fun e => NormedSpace.exp ((t+v) • S.potentialOperators f e))) _ u at h
  rw [he] at h
  exact h.unique ((S.rotatePotential f t).hasDerivAt_twistZ (S.potentialOperators f) u)

theorem potential_shift_second (S : SpinSystem V E) (f : V → ℝ) (t u : ℝ) :
    (∫ σ, S.secondWeight (S.potentialOperators f) (t+u) σ ∂S.reference) =
      ∫ σ, (S.rotatePotential f t).secondWeight (S.potentialOperators f) u σ ∂(S.rotatePotential f t).reference := by
  have h := (S.hasDerivAt_firstVariation (S.potentialOperators f) (t+u)).comp u
    ((hasDerivAt_id u).const_add t)
  simp only [mul_one] at h
  have he : (fun v => ∫ σ, S.firstWeight (S.potentialOperators f) (t+v) σ ∂S.reference) =
      (fun v => ∫ σ, (S.rotatePotential f t).firstWeight (S.potentialOperators f) v σ ∂(S.rotatePotential f t).reference) :=
    funext fun v => S.potential_shift_first f t v
  change HasDerivAt (fun v => ∫ σ, S.firstWeight (S.potentialOperators f) (t+v) σ ∂S.reference) _ u at h
  rw [he] at h
  exact h.unique ((S.rotatePotential f t).hasDerivAt_firstVariation (S.potentialOperators f) u)

theorem potential_second_response (S : SpinSystem V E) (f : V → ℝ) (t : ℝ) :
    (∫ σ, S.secondWeight (S.potentialOperators f) t σ ∂S.reference) /
      S.Z (fun e => NormedSpace.exp (t • S.potentialOperators f e)) =
      (S.rotatePotential f t).secondAxisResponse (S.edgeGradient f) (S.edgeGradient f) := by
  have hZ := S.potential_shift_Z f t 0
  have h2 := S.potential_shift_second f t 0
  simp only [add_zero,zero_smul ℝ (S.potentialOperators f _),NormedSpace.exp_zero] at hZ
  simp only [add_zero] at h2
  rw [hZ,h2,(S.rotatePotential f t).secondAxisResponse_integral]
  rfl

omit [Fintype V] [Fintype E] in
theorem spinRotation_potential_periodic (f : V → ℝ) (x : V)
    (h : f x=0 ∨ f x=1) (s : RP2.Spin) (t : ℝ) :
    spinRotation (potentialRotation f (t+2*Real.pi) x) s =
      spinRotation (potentialRotation f t x) s := by
  apply Subtype.ext
  simp only [spinRotation_val,potentialRotation,rotationExp_apply]
  rcases h with h | h
  · simp only [h,mul_zero]
  · simp only [h,mul_one,exp_axisC_periodic t]

omit [Fintype V] [Fintype E] in
theorem rotatePotential_periodic (S : SpinSystem V E) (f : V → ℝ)
    (hP : ∀ x s, S.pin x=some s → f x=0 ∨ f x=1) :
    Function.Periodic (S.rotatePotential f) (2*Real.pi) := by
  intro t
  have hpin : (S.rotatePotential f (t+2*Real.pi)).pin = (S.rotatePotential f t).pin := by
    funext x
    apply Option.map_congr
    intro s hs
    exact spinRotation_potential_periodic f x (hP x s hs) s t
  exact congrArg (fun p => SpinSystem.mk S.left S.right S.strength p) hpin

theorem potential_partition_ratio (S : SpinSystem V E) (f : V → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hP : ∀ x s, S.pin x=some s → f x=0 ∨ f x=1)
    (hR : ∀ t, -(S.rotatePotential f t).secondAxisResponse (S.edgeGradient f) (S.edgeGradient f) ≤ δ)
    (x y : ℝ) :
    1-δ*(2*Real.pi)^2/2 ≤ (S.rotatePotential f x).Z (fun _ => 1) /
      (S.rotatePotential f y).Z (fun _ => 1) := by
  let A := S.potentialOperators f
  let F := fun t : ℝ => S.Z (fun e => NormedSpace.exp (t • A e))
  let F' := fun t => ∫ σ, S.firstWeight A t σ ∂S.reference
  let F'' := fun t => ∫ σ, S.secondWeight A t σ ∂S.reference
  have hZ (t : ℝ) : F t=(S.rotatePotential f t).Z (fun _ => 1) := by
    have h := S.potential_shift_Z f t 0
    simpa only [add_zero,zero_smul ℝ (S.potentialOperators f _),NormedSpace.exp_zero] using h
  have hper : Function.Periodic F (2*Real.pi) := by
    intro t
    rw [hZ,hZ,S.rotatePotential_periodic f hP t]
  have hpos (t : ℝ) : 0<F t := S.Z_pos _
  have hode (t : ℝ) : -(δ*F t) ≤ F'' t := by
    have hr := hR t
    rw [← S.potential_second_response] at hr
    change -(F'' t/F t) ≤ δ at hr
    rw [← neg_div,div_le_iff₀ (hpos t)] at hr
    linarith
  have h := RP2.periodic_ode_ratio F F' F'' (2*Real.pi) δ (by positivity) hδ
    hper hpos (S.hasDerivAt_twistZ A) (S.hasDerivAt_firstVariation A) hode x y
  simpa only [hZ] using h


end SpinSystem
end Quadratic

end

end RP2
