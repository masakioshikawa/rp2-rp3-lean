module

public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.CategoryTheory.Countable
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Sigma.Order
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Tactic

public section

/-! Shared Mathlib prerequisites for the RP³ proof.
Extracted from the elaborated development and supplemented with the tactic
frontend. This replaces the six imports of all of Mathlib. It is a shared
prerequisite set, not a claim of per-file minimality. -/
