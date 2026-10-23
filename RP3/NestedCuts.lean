module

public import RP3.FiniteAveraging

public section

/-! Rotations on nested sets of spins. The averages commute even though
individual rotations about different axes need not commute. -/

namespace RP3.FiniteAction

open Finset MeasureTheory

variable {X V G : Type*} [TopologicalSpace X] [Group G]
  [DecidableEq V]

/-- Apply one rotation to all sites of a cut, fixing every other spin. -/
@[expose] noncomputable def onCut (A : FiniteAction G X) (s : Finset V) : FiniteAction G (V → X) where
  move g := ⟨fun σ v => if v ∈ s then A.move g (σ v) else σ v, by
    apply continuous_pi
    intro v
    by_cases hv : v ∈ s
    · simpa [hv, Function.comp_def] using (A.move g).continuous.comp (continuous_apply v)
    · simpa [hv] using (continuous_apply v : Continuous (fun σ : V → X => σ v))⟩
  one_apply σ := by ext v; simp [A.one_apply]
  mul_apply g h σ := by ext v; by_cases hv : v ∈ s <;> simp [hv, A.mul_apply]

@[simp] theorem onCut_apply (A : FiniteAction G X) (s : Finset V)
    (g : G) (σ : V → X) (v : V) :
    (A.onCut s).move g σ v = if v ∈ s then A.move g (σ v) else σ v := rfl

/-- Outer rotations conjugate the subgroup of inner rotations. -/
theorem nested_conjugation (A : FiniteAction G X) {s t : Finset V} (hst : s ⊆ t)
    (g h : G) (σ : V → X) :
    (A.onCut t).move h ((A.onCut s).move g σ) =
      (A.onCut s).move (h * g * h⁻¹) ((A.onCut t).move h σ) := by
  ext v
  by_cases hs : v ∈ s
  · have ht := hst hs
    simp only [onCut_apply, hs, ht, ite_true, ← A.mul_apply]
    congr 1
    group
  · by_cases ht : v ∈ t <;> simp [hs, ht]

theorem nested_averages_commute [Fintype G] (A : FiniteAction G X) {s t : Finset V}
    (hst : s ⊆ t) (f : C(V → X, ℝ)) :
    (A.onCut s).average ((A.onCut t).average f) =
      (A.onCut t).average ((A.onCut s).average f) := by
  apply (A.onCut s).averages_commute_of_normalizes (A.onCut t)
    (fun h => (MulAut.conj h).toEquiv)
  intro g h σ
  exact A.nested_conjugation hst g h σ

/-- A finite action is a homeomorphism for each group element. -/
@[expose] noncomputable def toHomeomorph (A : FiniteAction G X) (g : G) : X ≃ₜ X where
  toFun := A.move g
  invFun := A.move g⁻¹
  left_inv x := by rw [← A.mul_apply, inv_mul_cancel, A.one_apply]
  right_inv x := by rw [← A.mul_apply, mul_inv_cancel, A.one_apply]
  continuous_toFun := (A.move g).continuous
  continuous_invFun := (A.move g⁻¹).continuous

/-- Product reference measures are invariant under cut rotations as soon as
single-site reference measures are invariant. -/
theorem onCut_measurePreserving [Fintype V] [MeasurableSpace X] [BorelSpace X]
    (A : FiniteAction G X) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ g, MeasurePreserving (A.move g) μ μ) (s : Finset V) (g : G) :
    MeasurePreserving ((A.onCut s).move g) (Measure.pi fun _ : V => μ)
      (Measure.pi fun _ : V => μ) := by
  have hcoord (v : V) : MeasurePreserving
      (fun x : X => if v ∈ s then A.move g x else x) μ μ := by
    by_cases hv : v ∈ s
    · simpa only [hv, ite_true] using hμ g
    · have heq : (fun x : X => if v ∈ s then A.move g x else x) = id := by
        funext x
        simp [hv]
      rw [heq]
      exact MeasurePreserving.id μ
  exact measurePreserving_pi _ _ hcoord

/-- The complete averaging system on a chain of cuts with a product reference law. -/
@[expose] noncomputable def nestedSystem {ι : Type*} [Fintype G] [Fintype V] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (A : FiniteAction G X) (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ g, MeasurePreserving (A.move g) μ μ)
    (cuts : ι → Finset V) (hchain : ∀ i j, cuts i ⊆ cuts j ∨ cuts j ⊆ cuts i) :
    AveragingSystem (integralOnCompact (Measure.pi fun _ : V => μ)) ι := by
  apply systemOfFiniteActions _ (fun i => A.onCut (cuts i))
  · intro i g f
    exact (A.onCut_measurePreserving μ hμ (cuts i) g).integral_comp
      ((A.onCut (cuts i)).toHomeomorph g).measurableEmbedding f
  · intro i j f
    rcases hchain i j with hij | hji
    · exact A.nested_averages_commute hij f
    · exact (A.nested_averages_commute hji f).symm

end RP3.FiniteAction
