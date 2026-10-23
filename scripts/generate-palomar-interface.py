#!/usr/bin/env python3
"""Generate the two independently compiled interfaces from one statement text.

Challenge imports only Mathlib; Solution imports the proved development.
Only the two Challenge theorem bodies contain intentional sorry placeholders.
"""
from pathlib import Path
import argparse

ROOT = Path(__file__).resolve().parents[1]
MODEL = r'''public section

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

'''

def statement(d: int) -> str:
    return f'''/-- Uniform all-temperature log-square bound for RP{d-1}, with bounded signed couplings. -/
theorem rp{d-1}_log_square (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (G : SquareGraph) (b : G.edges → ℝ),
      (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |correlation {d} G b x y| ≤
        C * Real.exp (-c * (Real.log (2 + (radius x.val y.val : ℝ))) ^ 2) := by
'''

def proof(d: int) -> str:
    ns = f'RP{d-1}'
    return f'''  obtain ⟨C, hC, c, hc, hbound⟩ := {ns}.log_square_quadrupolar_decay_signed β hβ
  refine ⟨C, hC, c, hc, ?_⟩
  intro G b hb x y
  let G' : {ns}.Fourier.LatticeGraph :=
    {{ vertices := G.vertices, edges := G.edges, nearest := G.nearest }}
  have h := hbound G' b hb x y
  change |correlation {d} G b x y| ≤
    C * Real.exp (-c * (Real.log (2 + (radius x.val y.val : ℝ))) ^ 2) at h
  exact h

'''

def generated(solution: bool) -> str:
    imports = 'public import RP2\npublic import RP3' if solution else 'public import Mathlib'
    body = ''.join(statement(d) + (proof(d) if solution else '  sorry\n\n') for d in (3, 4))
    return 'module\n\n' + imports + '\n\n' + MODEL + body + 'end ProjectiveDecay\n'

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--check', action='store_true')
    args = ap.parse_args()
    for name, solution in [('Challenge.lean', False), ('Solution.lean', True)]:
        path = ROOT / name
        expected = generated(solution)
        if args.check:
            if not path.is_file() or path.read_text() != expected:
                raise SystemExit(f'{name} differs from its generator')
        else:
            path.write_text(expected)
        print(f'{name}: {len(expected.splitlines())} lines')

if __name__ == '__main__':
    main()
