module

public import RP3.QuadraticWard
public import RP3.PinnedKernel

public section

/-!
# Connecting the analytic Gibbs system to the existing RP³ definitions

These equalities identify the partition functions, including arbitrary pinned
spins. They do not assume an annular estimate or a decay theorem.
-/
namespace RP3.Quadratic
noncomputable section
open MeasureTheory
open RP3.Rotation hiding Spin
open scoped InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

@[expose] def freeSystem (edge : E → V × V) (b : E → ℝ) : SpinSystem V E where
  left e := (edge e).1
  right e := (edge e).2
  strength := b
  pin _ := none

@[expose] def pinnedSystem (edge : E → V × V) (b : E → ℝ) (pins : Finset V)
    (τ : RP3.Configuration V) : SpinSystem V E :=
  { freeSystem edge b with pin := fun v => if v ∈ pins then some (τ v) else none }

omit [Fintype V] [DecidableEq V] in
theorem freeSystem_energy (edge : E → V × V) (b : E → ℝ) (σ : RP3.Configuration V) :
    (freeSystem edge b).energy (fun _ => 1) σ = RP3.interaction edge b σ := by
  simp only [SpinSystem.energy, freeSystem, one_apply_eq_self, RP3.interaction]

omit [DecidableEq V] in
theorem freeSystem_partition (edge : E → V × V) (b : E → ℝ) :
    (freeSystem edge b).Z (fun _ => 1) = RP3.partition edge b := by
  simp only [SpinSystem.Z, freeSystem_energy]
  rfl

omit [DecidableEq V] in
theorem freeSystem_correlation (edge : E → V × V) (b : E → ℝ) (x y : V) :
    (freeSystem edge b).average (RP3.observable x y) = RP3.correlation edge b x y := by
  simp only [SpinSystem.average, freeSystem_energy, freeSystem_partition]
  rfl

omit [Fintype V] in
theorem pinnedSystem_energy (edge : E → V × V) (b : E → ℝ) (pins : Finset V)
    (τ σ : RP3.Configuration V) :
    (pinnedSystem edge b pins τ).energy (fun _ => 1) σ = RP3.interaction edge b σ := by
  simp only [SpinSystem.energy, pinnedSystem, freeSystem, one_apply_eq_self, RP3.interaction]

omit [Fintype E] in
/-- Overwriting the boundary pushes the free reference probability to the
product law with the prescribed Dirac masses. -/
theorem fillPins_preserves_reference (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (τ : RP3.Configuration V) :
    MeasurePreserving (RP3.fillPins pins τ) (RP3.referenceLaw (V := V))
      (pinnedSystem edge b pins τ).reference := by
  change MeasurePreserving (fun σ v => if v ∈ pins then τ v else σ v)
    (Measure.pi (fun _ => RP3.sphereProbability))
    (Measure.pi (fun v => siteReference (if v ∈ pins then some (τ v) else none)))
  apply measurePreserving_pi
  intro v
  by_cases hv : v ∈ pins
  · simp only [hv, ite_true, siteReference]
    have he : (ite (v ∈ pins) (τ v) : RP3.Spin → RP3.Spin) = (fun _ => τ v) := by
      funext s
      simp [hv]
    rw [he]
    refine ⟨measurable_const, ?_⟩
    simp only [Measure.map_const, measure_univ, one_smul]
  · simp only [hv, ite_false, siteReference]
    have he : (ite (v ∈ pins) (τ v) : RP3.Spin → RP3.Spin) = id := by
      funext s
      simp [hv]
    rw [he]
    exact MeasurePreserving.id _

/-- The analytic pinned partition function equals the one used in the
kernel-comparison interface, with no change of Gibbs measure. -/
theorem pinnedSystem_partition (edge : E → V × V) (b : E → ℝ) (pins : Finset V)
    (τ : RP3.Configuration V) :
    (pinnedSystem edge b pins τ).Z (fun _ => 1) = RP3.pinnedPartition edge b pins τ := by
  let S := pinnedSystem edge b pins τ
  have hm := fillPins_preserves_reference edge b pins τ
  change (∫ σ, Real.exp (S.energy (fun _ => 1) σ) ∂S.reference) =
    ∫ σ, Real.exp (RP3.interaction edge b (RP3.fillPins pins τ σ)) ∂(RP3.referenceLaw (V := V))
  simp only [S, pinnedSystem_energy]
  rw [← hm.map_eq]
  exact integral_map_of_stronglyMeasurable (RP3.fillPins pins τ).continuous.measurable
    (RP3.weight edge b).continuous.stronglyMeasurable

end
end RP3.Quadratic
