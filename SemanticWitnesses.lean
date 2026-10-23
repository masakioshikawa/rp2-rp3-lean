module

public import RP2

public section

/- Permanent semantic checks, compiled separately from the public library.
They test the model's normalization, a concrete nonempty graph, admissible
negative couplings, and the literal normalized Gibbs-integral endpoint. -/
namespace RP2.Audit
noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

theorem qPair_self (s : Spin) : qPair s s = (2 : ℝ) / 3 := by
  norm_num [qPair, real_inner_self_eq_norm_sq, spin_norm]

theorem correlation_self {V E : Type*} [Fintype V] [Fintype E]
    (edge : E → V × V) (b : E → ℝ) (x : V) :
    correlation edge b x x = (2 : ℝ) / 3 := by
  rw [← Quadratic.freeSystem_correlation edge b x x]
  change (Quadratic.freeSystem edge b).average (fun σ => qPair (σ x) (σ x)) = _
  simp_rw [qPair_self]
  exact (Quadratic.freeSystem edge b).average_const _

theorem partition_zero_coupling {V E : Type*} [Fintype V] [Fintype E]
    (edge : E → V × V) : partition edge (fun _ => 0) = 1 := by
  change (∫ σ : Configuration V, Real.exp (interaction edge (fun _ => 0) σ)
    ∂referenceLaw) = 1
  simp [interaction]

theorem pinnedPartition_all_sites {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] (edge : E → V × V) (b : E → ℝ) (τ : Configuration V) :
    pinnedPartition edge b Finset.univ τ = Real.exp (interaction edge b τ) := by
  change (∫ σ : Configuration V,
    Real.exp (interaction edge b (fillPins Finset.univ τ σ)) ∂referenceLaw) = _
  have hf (σ : Configuration V) : fillPins Finset.univ τ σ = τ := by
    funext v
    simp [fillPins]
  simp_rw [hf]
  simp

def oneEdgeVertices : Finset Fourier.Site := {(0, 0), (1, 0)}
def oneEdgeLeft : oneEdgeVertices := ⟨(0, 0), by simp [oneEdgeVertices]⟩
def oneEdgeRight : oneEdgeVertices := ⟨(1, 0), by simp [oneEdgeVertices]⟩

def oneEdgeGraph : Fourier.LatticeGraph where
  vertices := oneEdgeVertices
  edges := {(oneEdgeLeft, oneEdgeRight)}
  nearest := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    left
    norm_num [oneEdgeLeft, oneEdgeRight]

theorem oneEdgeGraph_has_two_vertices : oneEdgeGraph.vertices.card = 2 := by
  norm_num [oneEdgeGraph, oneEdgeVertices]

theorem oneEdgeGraph_has_one_edge : oneEdgeGraph.edges.card = 1 := by
  simp [oneEdgeGraph]

theorem oneEdgeGraph_admissible (β : ℝ) (hβ : 0 ≤ β) :
    ∀ e : oneEdgeGraph.edges, 0 ≤ (fun _ => β) e ∧ (fun _ => β) e ≤ β := by
  intro e
  exact ⟨hβ, le_rfl⟩

/-- The signed domain includes genuinely negative, nonzero interactions. -/
theorem oneEdgeGraph_negative_coupling (β : ℝ) (hβ : 0 < β) :
    ∀ e : oneEdgeGraph.edges,
      |(fun _ => -β) e| ≤ β ∧ (fun _ => -β) e < 0 := by
  intro e
  exact ⟨by simp [abs_of_pos hβ], by linarith⟩

def oneEdgeObservation : oneEdgeGraph.vertices :=
  ⟨(0, 0), by simp [oneEdgeGraph, oneEdgeVertices]⟩

theorem oneEdgeGraph_nonzero_correlation (β : ℝ) :
    correlation (fun e : oneEdgeGraph.edges => e.val) (fun _ => β)
      oneEdgeObservation oneEdgeObservation ≠ 0 := by
  rw [correlation_self]
  norm_num

/-- Fully expanded semantic endpoint: actual integral quotient, spherical
reference probability, squared interaction, and integer sup distance. -/
theorem expanded_superpolynomial_endpoint_signed (β : ℝ) (hβ : 0 ≤ β) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |(∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (⟪(σ x).val, (σ y).val⟫_ℝ ^ 2 - 1 / 3) *
          Real.exp (∑ e : G.edges,
            b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere))) /
      (∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Real.exp (∑ e : G.edges,
          b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)))| ≤
        A * (1 + ((max |y.val.1 - x.val.1| |y.val.2 - x.val.2| : ℤ) : ℝ)) ^ (-p) := by
  obtain ⟨A, hA, h⟩ := RP2.superpolynomial_quadrupolar_decay_signed β hβ p
  refine ⟨A, hA, ?_⟩
  intro G b hb x y
  exact h G b hb x y

/-- Compatibility check: the original ferromagnetic endpoint retains its literal type. -/
theorem expanded_superpolynomial_endpoint (β : ℝ) (hβ : 0 ≤ β) (p : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
      (∀ e, 0 ≤ b e ∧ b e ≤ β) → ∀ (x y : G.vertices),
      |(∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (⟪(σ x).val, (σ y).val⟫_ℝ ^ 2 - 1 / 3) *
          Real.exp (∑ e : G.edges,
            b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere))) /
      (∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Real.exp (∑ e : G.edges,
          b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)))| ≤
        A * (1 + ((max |y.val.1 - x.val.1| |y.val.2 - x.val.2| : ℤ) : ℝ)) ^ (-p) := by
  obtain ⟨A, hA, h⟩ := RP2.superpolynomial_quadrupolar_decay β hβ p
  refine ⟨A, hA, ?_⟩
  intro G b hb x y
  exact h G b hb x y


end
end RP2.Audit
