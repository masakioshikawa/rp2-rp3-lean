import RP3.ModelWitnesses
import RP3.LogSquareLimits

/-! Proofs contributed in the Claude Opus review supplied by the user on
11 October 2026, integrated and checked against this pinned development.
See REVIEW-RESPONSE.md for scope and attribution. -/
noncomputable section
open MeasureTheory Filter RP3
open scoped InnerProductSpace BigOperators Matrix Topology

namespace RP3.SO3
open RP3.ModelWitnesses

/-- Rotation matrix of `q = q₀ + q₁ i + q₂ j + q₃ k` (unnormalized). -/
def rotMat (q : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q 0 ^ 2 + q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2, 2 * (q 1 * q 2 - q 0 * q 3), 2 * (q 1 * q 3 + q 0 * q 2);
     2 * (q 1 * q 2 + q 0 * q 3), q 0 ^ 2 - q 1 ^ 2 + q 2 ^ 2 - q 3 ^ 2, 2 * (q 2 * q 3 - q 0 * q 1);
     2 * (q 1 * q 3 - q 0 * q 2), 2 * (q 2 * q 3 + q 0 * q 1), q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 + q 3 ^ 2]

theorem trace_rotMat (u v : Fin 4 → ℝ) :
    Matrix.trace ((rotMat u)ᵀ * rotMat v) =
      4 * (∑ i, u i * v i) ^ 2 - (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_four, rotMat]
  ring

theorem rotMat_orthogonal (u : Fin 4 → ℝ) (hu : ∑ i, u i ^ 2 = 1) :
    (rotMat u)ᵀ * rotMat u = 1 := by
  simp [Fin.sum_univ_four] at hu
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rotMat] <;>
    first
      | ring1
      | linear_combination (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 + 1) * hu

theorem rotMat_det (u : Fin 4 → ℝ) (hu : ∑ i, u i ^ 2 = 1) : (rotMat u).det = 1 := by
  simp [Fin.sum_univ_four] at hu
  rw [Matrix.det_fin_three]
  simp [rotMat]
  linear_combination ((u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) ^ 2 +
    (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) + 1) * hu

/-- `rotMat` is multiplicative: `R(p) R(q) = R(p q)` (Hamilton product). -/
theorem rotMat_mul (p q : Fin 4 → ℝ) :
    rotMat p * rotMat q = rotMat (lmulFun p q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rotMat, lmulFun] <;> ring

/-- The SO(3) rotation of an `S³` spin. -/
def rotOf (s : Spin) : Matrix (Fin 3) (Fin 3) ℝ := rotMat s.val

theorem rotOf_mem_SO3 (s : Spin) : rotOf s ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff']
  refine ⟨?_, rotMat_det _ (spin_squares s)⟩
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact rotMat_orthogonal _ (spin_squares s)

theorem qPair_eq_trace (s t : Spin) :
    qPair s t = (1 / 4) * Matrix.trace ((rotOf s)ᵀ * rotOf t) := by
  rw [rotOf, rotOf, trace_rotMat, spin_squares, spin_squares, qPair, inner_eq_sum]
  ring

theorem inner_sq_eq_trace (s t : Spin) :
    ⟪s.val, t.val⟫_ℝ ^ 2 = (1 + Matrix.trace ((rotOf s)ᵀ * rotOf t)) / 4 := by
  rw [rotOf, rotOf, trace_rotMat, spin_squares, spin_squares, inner_eq_sum]
  ring

/-- The actual correlation, rewritten entirely in SO(3) variables. -/
theorem correlation_eq_so3 {V E : Type*} [Fintype V] [Fintype E]
    (edge : E → V × V) (b : E → ℝ) (x y : V) :
    correlation edge b x y =
      (∫ σ, (1 / 4 * Matrix.trace ((rotOf (σ x))ᵀ * rotOf (σ y))) *
          Real.exp (∑ e, b e *
            ((1 + Matrix.trace ((rotOf (σ (edge e).1))ᵀ * rotOf (σ (edge e).2))) / 4))
        ∂referenceLaw) /
      (∫ σ, Real.exp (∑ e, b e *
            ((1 + Matrix.trace ((rotOf (σ (edge e).1))ᵀ * rotOf (σ (edge e).2))) / 4))
        ∂referenceLaw) := by
  change (∫ σ, qPair (σ x) (σ y) * Real.exp (interaction edge b σ) ∂referenceLaw) /
    (∫ σ, Real.exp (interaction edge b σ) ∂referenceLaw) = _
  simp only [interaction, qPair_eq_trace, inner_sq_eq_trace]

/-- **Suggested restatement.** The log-square theorem for the SO(3) matrix model. -/
theorem so3_log_square_decay_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ), (∀ e, |b e| ≤ β) →
      ∀ (x y : G.vertices),
      |(∫ σ, (1 / 4 * Matrix.trace ((rotOf (σ x))ᵀ * rotOf (σ y))) *
          Real.exp (∑ e : G.edges, b e *
            ((1 + Matrix.trace ((rotOf (σ e.val.1))ᵀ * rotOf (σ e.val.2))) / 4))
        ∂referenceLaw) /
      (∫ σ, Real.exp (∑ e : G.edges, b e *
            ((1 + Matrix.trace ((rotOf (σ e.val.1))ᵀ * rotOf (σ e.val.2))) / 4))
        ∂referenceLaw)| ≤
        C * Real.exp (-c * Real.log (2 + (Fourier.siteRadius x.val y.val : ℝ)) ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ := log_square_quadrupolar_decay_signed β hβ
  refine ⟨C, hC, c, hc, fun G b hb x y => ?_⟩
  have h1 := h G b hb x y
  rwa [correlation_eq_so3] at h1

/-- The pushforward of the uniform law under `rotOf` is left-invariant, hence Haar. -/
def HaarInvariance : Prop :=
  ∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ f : C(Matrix (Fin 3) (Fin 3) ℝ, ℝ),
    ∫ s, f (R * rotOf s) ∂sphereProbability = ∫ s, f (rotOf s) ∂sphereProbability

/-- **Remaining target.** Every rotation comes from a unit quaternion. This is
classical: take `q₀ = √(1 + Tr R)/2` when `Tr R > -1`, and use the analogous
formulas from a dominant diagonal entry otherwise. -/
def RotOfSurjective : Prop :=
  ∀ R ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∃ p : Spin, rotOf p = R

theorem continuous_rotOf : Continuous rotOf := by
  have hc : ∀ k : Fin 4, Continuous fun s : Spin => (s.val : E4) k := fun k =>
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) k).comp continuous_subtype_val
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [rotOf, rotMat] <;> fun_prop

theorem rotOf_lmul (p s : Spin) :
    rotOf (Rotation.spinRotation (lmulIsoOf p.val (spin_squares p)) s) =
      rotOf p * rotOf s := by
  rw [rotOf, rotOf, rotOf, rotMat_mul]
  congr 1

/-- **Proved reduction.** Given surjectivity, the pushforward is left-invariant,
because `rotOf` is multiplicative and left multiplication by a unit quaternion
preserves the uniform law. -/
theorem haarInvariance_of_surjective (h : RotOfSurjective) : HaarInvariance := by
  intro R hR f
  obtain ⟨p, rfl⟩ := h R hR
  have hmp := Rotation.spinRotation_preserves_probability (lmulIsoOf p.val (spin_squares p))
  have hcont : Continuous fun s : Spin => f (rotOf s) := f.continuous.comp continuous_rotOf
  calc ∫ s, f (rotOf p * rotOf s) ∂sphereProbability
      = ∫ s, f (rotOf (Rotation.spinRotation (lmulIsoOf p.val (spin_squares p)) s))
          ∂sphereProbability := by simp_rw [rotOf_lmul]
    _ = ∫ s, f (rotOf s) ∂sphereProbability := by
        rw [← integral_map hmp.measurable.aemeasurable hcont.aestronglyMeasurable, hmp.map_eq]


end RP3.SO3

end
