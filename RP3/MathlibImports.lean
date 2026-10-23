import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Data.Int.Star
import Mathlib.Data.Sigma.Order
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Tactic

/-! Shared Mathlib prerequisites for the RP³ proof.
Extracted from the elaborated development and supplemented with the tactic
frontend. This replaces the six imports of all of Mathlib. It is a shared
prerequisite set, not a claim of per-file minimality. -/
