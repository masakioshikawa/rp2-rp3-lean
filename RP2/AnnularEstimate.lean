module

public import RP2.QuadraticPotential
public import RP2.Fourier.AnnulusResponse

public section

/-! Uniform periodic boundary-rotation estimates for the squared RP² model.
Adapted from OpenAI ClassicalON/AnnulusPartition.lean, Apache-2.0. -/

namespace RP2

noncomputable section
open RP2.Rotation hiding Spin
open RP2.Quadratic
namespace Fourier.LatticeGraph

@[expose] def thetaPotential (G : LatticeGraph) (k : ℕ) (x : G.vertices) : ℝ :=
  squareTheta (scaledSite k x.val)

@[expose] def rotatedBoundaryPins (G : LatticeGraph) (k : ℕ) (P : G.vertices → Option (RP2.Spin))
    (t : ℝ) : G.vertices → Option (RP2.Spin) :=
  fun x => (P x).map (spinRotation (Quadratic.SpinSystem.potentialRotation (G.thetaPotential k) t x))

theorem thetaPotential_binary_pins (G : LatticeGraph) (k : ℕ)
    (P : G.vertices → Option (RP2.Spin)) (hP : G.BoundaryPins k P) :
    ∀ x s, P x=some s → G.thetaPotential k x=0 ∨ G.thetaPotential k x=1 := by
  intro x s hs
  rcases hP x s hs with h | h
  · exact Or.inr (squareTheta_one _ h.1 h.2)
  · exact Or.inl (squareTheta_zero _ h)

theorem rotatedBoundaryPins_boundary (G : LatticeGraph) (k : ℕ)
    (P : G.vertices → Option (RP2.Spin)) (hP : G.BoundaryPins k P) (t : ℝ) :
    G.BoundaryPins k (G.rotatedBoundaryPins k P t) := by
  intro x s hs
  cases hp : P x with
  | none => simp [rotatedBoundaryPins,hp] at hs
  | some u => exact hP x u hp

theorem rotatePotential_spinSystem (G : LatticeGraph) (k : ℕ) (b : G.edges → ℝ)
    (P : G.vertices → Option (RP2.Spin)) (t : ℝ) :
    (G.spinSystem b P).rotatePotential (G.thetaPotential k) t =
      G.spinSystem b (G.rotatedBoundaryPins k P t) := rfl


/-- Quantitative ratio comparison at every sufficiently large dyadic scale. -/
theorem annulus_partition_inverse_scale (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ k : ℕ, 4 ≤ k →
      ∀ G : LatticeGraph, G.WithinDyadicBox k →
      ∀ b : G.edges → ℝ, (∀ e, |b e| ≤ β) →
      ∀ P : G.vertices → Option RP2.Spin, G.BoundaryPins k P → ∀ x y : ℝ,
      1-D/(k:ℝ) ≤ (G.spinSystem b (G.rotatedBoundaryPins k P x)).Z (fun _ => 1) /
        (G.spinSystem b (G.rotatedBoundaryPins k P y)).Z (fun _ => 1) := by
  obtain ⟨K, hK, hresponse⟩ := annulus_response_inverse_scale β hβ
  refine ⟨K*(2*Real.pi)^2/2, by positivity, ?_⟩
  intro k hk G hG b hb P hP x y
  have hp := G.thetaPotential_binary_pins k P hP
  have hr (t : ℝ) :
      -((G.spinSystem b P).rotatePotential (G.thetaPotential k) t).secondAxisResponse
        ((G.spinSystem b P).edgeGradient (G.thetaPotential k))
        ((G.spinSystem b P).edgeGradient (G.thetaPotential k)) ≤ K/(k:ℝ) := by
    exact hresponse k hk G hG b hb (G.rotatedBoundaryPins k P t)
      (G.rotatedBoundaryPins_boundary k P hP t)
  have h := (G.spinSystem b P).potential_partition_ratio (G.thetaPotential k)
    (K/(k:ℝ)) (div_nonneg hK (Nat.cast_nonneg k)) hp hr x y
  simp only [rotatePotential_spinSystem] at h
  convert h using 1 <;> ring

end Fourier.LatticeGraph
end
end RP2
