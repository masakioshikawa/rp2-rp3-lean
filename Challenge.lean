module

public import Mathlib

public section

/-!
# Log-square decay for two-dimensional projective spin models

The definitions below specify finite subgraphs of the square lattice, normalized
spherical product measure, the squared-inner-product Gibbs weight, and the
quadrupolar observable. Dimension 3 realizes RP² and dimension 4 realizes RP³.
Constants are uniform in the finite graph, bounded signed couplings, and sites.
No decay estimate, analytic response certificate, or limit hypothesis is assumed.
The statements do not claim exponential decay at all temperatures or exclude
transitions invisible to this observable. This interface advertises finite-volume
results; additional local-limit theorems remain in the full proof development.
-/

namespace ProjectiveDecay

open MeasureTheory
open scoped BigOperators InnerProductSpace

/-- Sites of the two-dimensional square lattice. -/
abbrev Site := ℤ × ℤ

/-- One positively oriented representative of a nearest-neighbor bond. -/
@[expose] def PositiveNeighbor (x y : Site) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 ∧ y.2 = x.2 + 1)

/-- Any finite square-lattice subgraph, allowing deleted vertices and bonds. -/
structure SquareGraph where
  vertices : Finset Site
  edges : Finset (vertices × vertices)
  nearest : ∀ e ∈ edges, PositiveNeighbor e.1.val e.2.val

/-- Unit vectors representing directors; the weight and observable are even. -/
abbrev Spin (d : ℕ) := Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1

/-- Surface measure divided by its total mass. -/
@[expose] noncomputable def sphereProbability (d : ℕ) : Measure (Spin d) :=
  ((volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere Set.univ)⁻¹ •
    (volume : Measure (EuclideanSpace ℝ (Fin d))).toSphere

/-- Independent normalized spherical measure at every vertex. -/
@[expose] noncomputable def referenceLaw (d : ℕ) (G : SquareGraph) :
    Measure (G.vertices → Spin d) :=
  Measure.pi (fun _ => sphereProbability d)

/-- Dimensionless Gibbs weight with one signed coupling per bond. -/
@[expose] noncomputable def weight (d : ℕ) (G : SquareGraph)
    (b : G.edges → ℝ) (σ : G.vertices → Spin d) : ℝ :=
  Real.exp (∑ e : G.edges, b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)

/-- The actual normalized two-point quadrupolar integral, with subtraction 1/d. -/
@[expose] noncomputable def correlation (d : ℕ) (G : SquareGraph)
    (b : G.edges → ℝ) (x y : G.vertices) : ℝ :=
  (∫ σ : G.vertices → Spin d,
    (⟪(σ x).val, (σ y).val⟫_ℝ ^ 2 - 1 / (d : ℝ)) * weight d G b σ
      ∂referenceLaw d G) /
  (∫ σ : G.vertices → Spin d, weight d G b σ ∂referenceLaw d G)

/-- Exact integer lattice infinity distance. -/
@[expose] def radius (x y : Site) : ℤ :=
  max |y.1 - x.1| |y.2 - x.2|

/-- Uniform all-temperature log-square bound for RP2, with bounded signed couplings. -/
theorem rp2_log_square (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : SquareGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation 3 G b x y| ≤
        C * Real.exp (-c * (Real.log (2 + (radius x.val y.val : ℝ))) ^ 2) := by
  sorry

/-- Uniform all-temperature log-square bound for RP3, with bounded signed couplings. -/
theorem rp3_log_square (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : SquareGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation 4 G b x y| ≤
        C * Real.exp (-c * (Real.log (2 + (radius x.val y.val : ℝ))) ^ 2) := by
  sorry

end ProjectiveDecay
