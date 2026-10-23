module

public import RP2.ModelAssembly
public import RP2.TetrahedralAction
public import RP2.LatticeAnnuli
public import RP2.Main

public section

/-!
# The product estimate for the actual finite-volume RP² Gibbs measure

All kernels in this file are ordinary pinned partition integrals of the
squared interaction.  The factorization and the normalization identity are
proved from integration; they are not representation hypotheses.
-/

namespace RP2
noncomputable section
open Finset MeasureTheory

variable {V E J : Type*} [Fintype V] [Fintype E] [Fintype J]
  [DecidableEq V] [DecidableEq J]

/-- A finite-volume product bound with a single analytic hypothesis: the
pointwise rotational comparison for the actual pinned annular kernels.
The remaining hypotheses are finite edge and cut incidences. -/
theorem concrete_kernel_product_bound (edge : E → V × V) (b : E → ℝ)
    (sets : J → Finset E) (pins cuts : J → Finset V) (x y : V) (ε : J → ℝ)
    (hdisjoint : Pairwise (fun i j => Disjoint (sets i) (sets j)))
    (hchain : ∀ i j, cuts i ⊆ cuts j ∨ cuts j ⊆ cuts i)
    (hbaseLocal : ∀ i e, remainingCoupling sets b e = 0 ∨
      ((edge e).1 ∈ pins i ∧ (edge e).2 ∈ pins i))
    (hcrossLocal : ∀ i j, i ≠ j → ∀ e, maskedCoupling (sets j) b e = 0 ∨
      ((edge e).1 ∈ pins i ∧ (edge e).2 ∈ pins i))
    (hobsLocal : ∀ i, x ∈ pins i ∧ y ∈ pins i)
    (hbaseCut : ∀ i e, remainingCoupling sets b e = 0 ∨
      ((edge e).1 ∈ cuts i ↔ (edge e).2 ∈ cuts i))
    (hcrossCut : ∀ i j, i ≠ j → ∀ e, maskedCoupling (sets j) b e = 0 ∨
      ((edge e).1 ∈ cuts i ↔ (edge e).2 ∈ cuts i))
    (hseparates : ∀ i, x ∈ cuts i ∧ y ∉ cuts i)
    (hε : ∀ i, 0 < ε i)
    (hcompare : ∀ i (g : Tetrahedral) τ,
      (1 - ε i) * pinnedKernel edge (maskedCoupling (sets i) b) (pins i)
        ((tetraAction.onCut (cuts i)).move g τ) ≤
        pinnedKernel edge (maskedCoupling (sets i) b) (pins i) τ) :
    |correlation edge b x y| ≤ (2 : ℝ) / 3 * ∏ i, ε i := by
  classical
  let I := integralOnCompact (referenceLaw (V := V))
  let S := tetraNestedSystem cuts hchain
  let f := fun i => weight edge (maskedCoupling (sets i) b)
  let K := fun i => pinnedKernel edge (maskedCoupling (sets i) b) (pins i)
  let W := weight edge (remainingCoupling sets b)
  let O := observable x y
  have hf : ∀ i j, i ≠ j → DependsOnPins (pins i) (f j) := by
    intro i j hij
    exact weight_dependsOnPins edge _ _ (hcrossLocal i j hij)
  have hW : ∀ i, DependsOnPins (pins i) W := by
    intro i
    exact weight_dependsOnPins edge _ _ (hbaseLocal i)
  have hO : ∀ i, DependsOnPins (pins i) O := by
    intro i
    exact observable_dependsOnPins _ x y (hobsLocal i).1 (hobsLocal i).2
  have hZ : I.linear (W * ∏ i, K i) = partition edge b := by
    change (∫ τ, (W * ∏ i, K i) τ ∂referenceLaw) = _
    have h := integral_product_boundaryAverage (univ : Finset J) pins f W
      (fun i _ => hW i) (fun i _ j _ hij => hf i j hij)
    change (∫ τ, (W * ∏ i, K i) τ ∂referenceLaw) =
      ∫ τ, (W * ∏ i, f i) τ ∂referenceLaw at h
    rw [h]
    have hw := weight_partition edge sets hdisjoint b
    change (∫ τ, (weight edge (remainingCoupling sets b) *
      ∏ i, weight edge (maskedCoupling (sets i) b)) τ ∂referenceLaw) = _
    rw [← hw]
    rfl
  have hnum : I.linear (O * W * ∏ i, K i) =
      I.linear (observable x y * weight edge b) := by
    change (∫ τ, (O * W * ∏ i, K i) τ ∂referenceLaw) = _
    have h := integral_product_boundaryAverage (univ : Finset J) pins f (O * W)
      (fun i _ => (hO i).mul (hW i)) (fun i _ j _ hij => hf i j hij)
    change (∫ τ, (O * W * ∏ i, K i) τ ∂referenceLaw) =
      ∫ τ, (O * W * ∏ i, f i) τ ∂referenceLaw at h
    rw [h]
    have hw : O * W * ∏ i, f i = observable x y * weight edge b := by
      rw [weight_partition edge sets hdisjoint b]
      exact mul_assoc _ _ _
    rw [hw]
    rfl
  have hb := S.correlation_bound (univ : Finset J) ε K O W
    (fun i _ => hε i)
    (fun i _ τ => (pinnedPartition_pos edge _ _ τ).le)
    (fun i _ => (tetraAction.onCut (cuts i)).comparison_lower (K i) (ε i)
      (hcompare i))
    (fun i _ j _ hij => pinnedKernel_cut_average_of_edges
      tetraAction tetraLinearIsometry tetraAction_eq_spinRotation
      edge _ (pins j) (cuts i) (hcrossCut i j hij))
    (fun i _ => tetraAction_cut_average_zero _ x y (hseparates i).1 (hseparates i).2)
    (fun τ => abs_qPair_le (τ x) (τ y))
    (fun τ => (Real.exp_pos _).le)
    (fun i _ => weight_cut_average tetraAction tetraLinearIsometry
      tetraAction_eq_spinRotation edge _ (cuts i) (hbaseCut i))
    (by rw [hZ]; exact partition_pos edge b)
  change |I.linear (O * W * ∏ i, K i) / I.linear (W * ∏ i, K i)| ≤ _ at hb
  rw [hZ, hnum] at hb
  exact hb

namespace Fourier.LatticeGraph

/-- The concrete nested-annulus product bound on every retained square-lattice
graph.  The only hypothesis beyond geometric scale separation is comparison
of explicitly defined pinned RP² partition integrals. -/
theorem square_annuli_product_bound (G : LatticeGraph) (b : G.edges → ℝ)
    (k : ℕ) (N : Fin k → ℤ) (hN : ∀ i, 2 ≤ N i)
    (hsep : ∀ i j, i < j → 2*N i < N j)
    (x y : G.vertices) (hy : ∀ i, 2*N i < siteRadius x.val y.val)
    (ε : Fin k → ℝ) (hε : ∀ i, 0 < ε i)
    (hcompare : ∀ i (g : Tetrahedral) τ,
      (1 - ε i) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (N i) x.val) b) (G.strictLayer (N i) x.val)ᶜ
        ((tetraAction.onCut (G.innerCut (N i) x.val)).move g τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (N i) x.val) b) (G.strictLayer (N i) x.val)ᶜ τ) :
    |correlation (fun e : G.edges => e.val) b x y| ≤ (2 : ℝ)/3 * ∏ i, ε i := by
  classical
  let sets := fun i => G.kernelEdges (N i) x.val
  let pins := fun i => (G.strictLayer (N i) x.val)ᶜ
  let cuts := fun i => G.innerCut (N i) x.val
  have hleft (i : Fin k) : x ∈ pins i := by
    simp only [pins, mem_compl, mem_strictLayer, siteRadius_self]
    have := hN i
    omega
  have hright (i : Fin k) : y ∈ pins i := by
    simp only [pins, mem_compl, mem_strictLayer]
    have := hy i
    omega
  apply concrete_kernel_product_bound (fun e : G.edges => e.val) b sets pins cuts
    x y ε
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact G.separated_kernelEdges x.val (hsep i j hij)
    · exact (G.separated_kernelEdges x.val (hsep j i hji)).symm
  · intro i j
    rcases le_total i j with hij | hji
    · left
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hij with rfl | hij
      · exact le_rfl
      · have := hsep i j hij
        have := hN i
        omega
    · right
      apply G.innerCut_mono
      rcases eq_or_lt_of_le hji with rfl | hji
      · exact le_rfl
      · have := hsep j i hji
        have := hN j
        omega
  · intro i e
    by_cases he : ∃ j, e ∈ sets j
    · left
      simp [remainingCoupling, he]
    · right
      have hn : e ∉ sets i := fun hi => he ⟨i, hi⟩
      simpa only [sets, pins, mem_kernelEdges, not_or, mem_compl] using hn
  · intro i j hij e
    by_cases he : e ∈ sets j
    · right
      simp only [pins, mem_compl]
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact G.kernelEdges_avoid_smaller_interior x.val (hsep i j hij) e he
      · exact G.kernelEdges_avoid_larger_interior x.val (hsep j i hji) e he
    · left
      simp [maskedCoupling, he]
  · exact fun i => ⟨hleft i, hright i⟩
  · intro i e
    by_cases he : ∃ j, e ∈ sets j
    · left
      simp [remainingCoupling, he]
    · right
      exact G.nonkernel_same_side (N i) (hN i) x.val e (fun hi => he ⟨i,hi⟩)
  · intro i j hij e
    by_cases he : e ∈ sets j
    · right
      rcases lt_or_gt_of_ne hij with hij | hji
      · have hn := G.kernelEdges_outside_smaller_cut (by have := hN i; omega)
          x.val (hsep i j hij) e he
        exact iff_of_false hn.1 hn.2
      · have hn := G.kernelEdges_inside_larger_cut x.val (hsep j i hji) e he
        exact iff_of_true hn.1 hn.2
    · left
      simp [maskedCoupling, he]
  · intro i
    simp only [cuts, mem_innerCut, siteRadius_self]
    have := hN i
    have := hy i
    omega
  · exact hε
  · exact hcompare

end Fourier.LatticeGraph

end
end RP2
