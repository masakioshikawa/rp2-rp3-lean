import RP2.RotationGeometry
import RP2.Calculus

/-!
# Pinned quadratic-spin Gibbs systems

Gauge transformations and their reference-measure proofs are adapted from
OpenAI's ClassicalON/FiniteVolume.lean at commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The interaction here is the squared scalar product. Its derivative jets are
constructed by the product rule, rather than the linear-energy formulas in
that source.
-/

namespace RP2.Quadratic
universe uV uE
noncomputable section
open MeasureTheory
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace

def siteReference (p : Option (RP2.Spin)) : Measure (RP2.Spin) :=
  match p with
  | none => sphereProbability
  | some s => Measure.dirac s

instance siteReference_isProbability (p : Option (RP2.Spin)) :
    IsProbabilityMeasure (siteReference p) := by
  cases p <;> dsimp [siteReference] <;> infer_instance

structure SpinSystem (V : Type uV) (E : Type uE) where
  left : E → V
  right : E → V
  strength : E → ℝ
  pin : V → Option (RP2.Spin)

namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def reference (S : SpinSystem V E) : Measure (V → RP2.Spin) :=
  Measure.pi (fun x => siteReference (S.pin x))

instance reference_isProbability (S : SpinSystem V E) :
    IsProbabilityMeasure S.reference := by
  unfold reference
  infer_instance

def energy (S : SpinSystem V E) (K : E → SpinOperator 3) (σ : V → RP2.Spin) : ℝ :=
  ∑ e, S.strength e * ⟪(σ (S.left e)).val, K e (σ (S.right e)).val⟫_ℝ ^ 2

def Z (S : SpinSystem V E) (K : E → SpinOperator 3) : ℝ :=
  ∫ σ, Real.exp (S.energy K σ) ∂S.reference

omit [Fintype V] in
theorem continuous_energy (S : SpinSystem V E) (K : E → SpinOperator 3) :
    Continuous (S.energy K) := by
  unfold energy
  fun_prop

theorem integrable_weight (S : SpinSystem V E) (K : E → SpinOperator 3) :
    Integrable (fun σ => Real.exp (S.energy K σ)) S.reference :=
  (S.continuous_energy K).rexp.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem Z_pos (S : SpinSystem V E) (K : E → SpinOperator 3) :
    0 < S.Z K := by
  unfold Z
  apply (integral_pos_iff_support_of_nonneg
    (fun σ => (Real.exp_pos _).le) (S.integrable_weight K)).mpr
  have hs : Function.support (fun σ => Real.exp (S.energy K σ)) = Set.univ := by
    ext σ
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

def rotateConfiguration
    (U : V → E3 ≃ₗᵢ[ℝ] E3) :
    (V → RP2.Spin) ≃ₜ (V → RP2.Spin) :=
  Homeomorph.piCongrRight (fun x => spinRotation (U x))

def rotatePins (S : SpinSystem V E)
    (U : V → E3 ≃ₗᵢ[ℝ] E3) :
    SpinSystem V E :=
  { S with pin := fun x => (S.pin x).map (spinRotation (U x)) }

def gauge (S : SpinSystem V E) (K : E → SpinOperator 3)
    (U : V → E3 ≃ₗᵢ[ℝ] E3) :
    E → SpinOperator 3 :=
  fun e => (U (S.left e)).symm.toContinuousLinearEquiv.toContinuousLinearMap * K e *
    (U (S.right e)).toContinuousLinearEquiv.toContinuousLinearMap

omit [Fintype E] in
theorem rotateConfiguration_preserves_reference (S : SpinSystem V E)
    (U : V → E3 ≃ₗᵢ[ℝ] E3) :
    MeasurePreserving (rotateConfiguration U) S.reference (S.rotatePins U).reference := by
  change MeasurePreserving (fun σ x => spinRotation (U x) (σ x))
    (Measure.pi (fun x => siteReference (S.pin x)))
    (Measure.pi (fun x => siteReference ((S.pin x).map (spinRotation (U x)))))
  apply measurePreserving_pi
  intro x
  cases S.pin x with
  | none => exact spinRotation_preserves_probability (U x)
  | some s =>
    exact ⟨(spinRotation (U x)).measurable, Measure.map_dirac s⟩

omit [Fintype V] in
theorem energy_gauge (S : SpinSystem V E) (K : E → SpinOperator 3)
    (U : V → E3 ≃ₗᵢ[ℝ] E3)
    (σ : V → RP2.Spin) :
    S.energy (S.gauge K U) σ = (S.rotatePins U).energy K (rotateConfiguration U σ) := by
  apply Finset.sum_congr rfl
  intro e _
  change S.strength e * _ ^ 2 = S.strength e * _ ^ 2
  apply congrArg (fun r : ℝ => S.strength e * r ^ 2)
  change ⟪(σ (S.left e)).val,
      (U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val))⟫_ℝ =
    ⟪U (S.left e) (σ (S.left e)).val, K e (U (S.right e) (σ (S.right e)).val)⟫_ℝ
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    ((U (S.left e)).inner_map_map (σ (S.left e)).val
      ((U (S.left e)).symm (K e (U (S.right e) (σ (S.right e)).val)))).symm

theorem Z_gauge (S : SpinSystem V E) (K : E → SpinOperator 3)
    (U : V → E3 ≃ₗᵢ[ℝ] E3) :
    S.Z (S.gauge K U) = (S.rotatePins U).Z K := by
  unfold Z
  simp_rw [energy_gauge]
  exact (S.rotateConfiguration_preserves_reference U).integral_comp
    (rotateConfiguration U).measurableEmbedding
    (fun σ => Real.exp ((S.rotatePins U).energy K σ))

omit [Fintype V] [Fintype E] in

theorem rotatePins_eq_self (S : SpinSystem V E)
    (U : V → E3 ≃ₗᵢ[ℝ] E3)
    (hU : ∀ x s, S.pin x = some s → spinRotation (U x) s = s) :
    S.rotatePins U = S := by
  suffices hp : (fun x => (S.pin x).map (spinRotation (U x))) = S.pin by
    unfold rotatePins
    rw [hp]
  funext x
  cases h : S.pin x with
  | none => rfl
  | some s => simp only [Option.map_some, hU x s h]

theorem Z_gauge_of_fixes_pins (S : SpinSystem V E)
    (K : E → SpinOperator 3)
    (U : V → E3 ≃ₗᵢ[ℝ] E3)
    (hU : ∀ x s, S.pin x = some s → spinRotation (U x) s = s) :
    S.Z (S.gauge K U) = S.Z K := by
  rw [S.Z_gauge K U, S.rotatePins_eq_self U hU]

def W (S : SpinSystem V E) (A : E → SpinOperator 3) : ℝ :=
  S.Z (fun e => NormedSpace.exp (A e)) / S.Z (fun _ => 1)

@[simp] theorem W_zero (S : SpinSystem V E) : S.W 0 = 1 := by
  simp only [W, Pi.zero_apply, NormedSpace.exp_zero]
  exact div_self (S.Z_pos _).ne'

def gaugeProduct (S : SpinSystem V E) (F : V → SpinOperator 3) : E → SpinOperator 3 :=
  fun e => NormedSpace.exp (F (S.left e)) *
    NormedSpace.exp (F (S.right e) - F (S.left e)) *
    NormedSpace.exp (-F (S.right e))

theorem noncommuting_gauge (S : SpinSystem V E)
    (F : V → SpinOperator 3) (hF : ∀ x, F x ∈ skewAdjoint (SpinOperator 3))
    (hP : ∀ x s, S.pin x = some s → F x = 0) :
    S.Z (fun e => NormedSpace.exp (F (S.right e) - F (S.left e))) =
      S.Z (S.gaugeProduct F) := by
  let U := fun x => rotationExp (-F x) ((skewAdjoint _).neg_mem (hF x))
  have hfix : ∀ x s, S.pin x = some s → spinRotation (U x) s = s := by
    intro x s hs
    apply Subtype.ext
    change NormedSpace.exp (-F x) s.val = s.val
    rw [hP x s hs, neg_zero, NormedSpace.exp_zero]
    rfl
  have hg : S.gauge (fun e => NormedSpace.exp (F (S.right e) - F (S.left e))) U =
      S.gaugeProduct F := by
    funext e
    apply ContinuousLinearMap.ext
    intro v
    change (U (S.left e)).symm
      (NormedSpace.exp (F (S.right e) - F (S.left e)) (U (S.right e) v)) = _
    simp only [U, rotationExp_symm_apply, rotationExp_apply, neg_neg,
      gaugeProduct, mul_apply_eq_comp]
  rw [← hg]
  exact (S.Z_gauge_of_fixes_pins _ U hfix).symm

end SpinSystem
end
end RP2.Quadratic
