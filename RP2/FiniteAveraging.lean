import RP2.Averaging

/-! Concrete finite-group averages and integration against finite measures. -/

namespace RP2

open Finset MeasureTheory

variable {Ω G : Type*} [TopologicalSpace Ω]

/-- A continuous finite-group action, written without a global typeclass so
several different cuts can act on the same configuration space. -/
structure FiniteAction (G Ω : Type*) [Group G] [TopologicalSpace Ω] where
  move : G → C(Ω, Ω)
  one_apply : ∀ x, move 1 x = x
  mul_apply : ∀ g h x, move (g * h) x = move g (move h x)

namespace FiniteAction

variable [Group G] [Fintype G] (A : FiniteAction G Ω)

noncomputable def pullback (g : G) : C(Ω, ℝ) →ₗ[ℝ] C(Ω, ℝ) where
  toFun f := f.comp (A.move g)
  map_add' f h := by ext x; rfl
  map_smul' c f := by ext x; rfl

noncomputable def average : C(Ω, ℝ) →ₗ[ℝ] C(Ω, ℝ) :=
  (Fintype.card G : ℝ)⁻¹ • ∑ g : G, A.pullback g

@[simp] theorem average_apply (f : C(Ω, ℝ)) (x : Ω) :
    A.average f x = (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (A.move g x) := by
  simp [average, pullback]

theorem card_ne_zero : (Fintype.card G : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem invariant (f : C(Ω, ℝ)) (g : G) (x : Ω) :
    A.average f (A.move g x) = A.average f x := by
  simp only [average_apply, ← A.mul_apply]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight g) (fun h => f (A.move h x))

theorem average_of_invariant (f : C(Ω, ℝ))
    (hf : ∀ g x, f (A.move g x) = f x) : A.average f = f := by
  ext x
  simp only [average_apply, hf, sum_const, card_univ, nsmul_eq_mul]
  exact inv_mul_cancel_left₀ (card_ne_zero (G := G)) _

theorem average_one : A.average 1 = 1 :=
  A.average_of_invariant 1 (fun _ _ => rfl)

theorem average_idem (f : C(Ω, ℝ)) : A.average (A.average f) = A.average f :=
  A.average_of_invariant _ (A.invariant f)

theorem average_pull (f h : C(Ω, ℝ)) (hf : A.average f = f) :
    A.average (f * h) = f * A.average h := by
  have hfinv (g : G) (x : Ω) : f (A.move g x) = f x := by
    rw [← hf]
    exact A.invariant f g x
  ext x
  simp only [average_apply, ContinuousMap.mul_apply, hfinv, ← mul_sum]
  ring

theorem average_nonneg (f : C(Ω, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ A.average f x := by
  intro x
  rw [average_apply]
  exact mul_nonneg (by positivity) (sum_nonneg (fun g _ => hf _))

/-- Pairwise rotational comparison implies the lower bound used to split a kernel. -/
theorem comparison_lower (K : C(Ω, ℝ)) (ε : ℝ)
    (hcomp : ∀ g x, (1 - ε) * K (A.move g x) ≤ K x) :
    ∀ x, (1 - ε) * A.average K x ≤ K x := by
  intro x
  have hs := sum_le_sum (s := (univ : Finset G)) (fun g _ => hcomp g x)
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum] at hs
  have hc : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [average_apply]
  calc
    (1 - ε) * ((Fintype.card G : ℝ)⁻¹ * ∑ g, K (A.move g x)) =
        ((1 - ε) * ∑ g, K (A.move g x)) / Fintype.card G := by ring
    _ ≤ K x := (div_le_iff₀ hc).mpr (by simpa [mul_comm] using hs)

theorem preserve_integral (I : PositiveIntegral Ω)
    (hI : ∀ g f, I.linear (A.pullback g f) = I.linear f) (f : C(Ω, ℝ)) :
    I.linear (A.average f) = I.linear f := by
  simp only [average, LinearMap.smul_apply, LinearMap.sum_apply, map_smul,
    map_sum, hI, sum_const, card_univ, nsmul_eq_mul, smul_eq_mul]
  exact inv_mul_cancel_left₀ (card_ne_zero (G := G)) _

/-- Normalisation of one rotation subgroup by another makes their averages commute.
The reindexing `e h` is conjugation for nested cuts. -/
theorem averages_commute_of_normalizes (B : FiniteAction G Ω)
    (e : G → G ≃ G)
    (hn : ∀ g h x, B.move h (A.move g x) = A.move (e h g) (B.move h x))
    (f : C(Ω, ℝ)) : A.average (B.average f) = B.average (A.average f) := by
  ext x
  simp only [average_apply, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  simp only [hn]
  exact Equiv.sum_comp (e h) (fun g => (Fintype.card G : ℝ)⁻¹ *
    ((Fintype.card G : ℝ)⁻¹ * f (A.move g (B.move h x))))

end FiniteAction

/-- The positive integral interface is realised by ordinary integration;
compactness ensures every continuous function here is integrable. -/
noncomputable def integralOnCompact [CompactSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] : PositiveIntegral Ω where
  linear := {
    toFun := fun f => ∫ x, f x ∂μ
    map_add' := fun f g => integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    map_smul' := fun c f => integral_smul c f }
  nonneg := fun _ hf => integral_nonneg hf

/-- Assemble the structural interface from actual finite actions and invariant integration. -/
noncomputable def systemOfFiniteActions {ι : Type*} [Group G] [Fintype G]
    (I : PositiveIntegral Ω) (A : ι → FiniteAction G Ω)
    (hI : ∀ i g f, I.linear ((A i).pullback g f) = I.linear f)
    (hc : ∀ i j f, (A i).average ((A j).average f) =
      (A j).average ((A i).average f)) : AveragingSystem I ι where
  avg i := (A i).average
  one i := (A i).average_one
  idem i := (A i).average_idem
  commute := hc
  pull i := (A i).average_pull
  preserve i := (A i).preserve_integral I (hI i)

end RP2
