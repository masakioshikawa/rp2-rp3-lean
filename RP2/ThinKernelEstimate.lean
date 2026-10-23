module

public import RP2.ThinProfileLattice
public import RP2.ThinResponse
public import RP2.ThinDyadicParameters
public import RP2.LogSquarePacking

public section

/-! Actual full-graph kernel comparison from the thin-annulus response. -/
namespace RP2.Fourier.LatticeGraph
noncomputable section
open RP2 RP2.Quadratic
open scoped Classical

/-- Exact restriction and rotation transfer for an arbitrary thin shell.
The analytic premise is discharged by `thin_annulus_response` below. -/
theorem thin_kernel_comparison_of_response
    (k : ℕ) (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (R S : ℤ) (hR : (R:ℝ)=a*(2:ℝ)^k)
    (hS : (S:ℝ)=(a+δ)*(2:ℝ)^k) (hSbox : S ≤ 2*(2:ℤ)^k)
    (β : ℝ) (hβ : 0 ≤ β) (B : ℝ) (hB : 0 ≤ B)
    (hresponse : ∀ (H : LatticeGraph), H.WithinDyadicBox k →
      ∀ (b : H.edges → ℝ), (∀ e, |b e| ≤ β) →
      ∀ (P : H.vertices → Option RP2.Spin), H.ThinBoundaryPins k a δ P →
        -(H.spinSystem b P).secondAxisResponse
          (H.thinThetaEdge k a δ) (H.thinThetaEdge k a δ) ≤ B)
    (G : LatticeGraph) (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (z : Site) (g : Tetrahedral) (τ : Configuration G.vertices) :
    (1-6*Real.pi^2*B) * pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.thinKernelEdges R S z) b) (G.thinLayer R S z)ᶜ
      ((tetraAction.onCut (G.innerCut R z)).move g τ) ≤
    pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.thinKernelEdges R S z) b) (G.thinLayer R S z)ᶜ τ := by
  by_cases hsmall : B*(2*Real.pi)^2/2 ≤ 1
  · let H := (G.thinAnnulusGraph R S z).translate z
    let bH : H.edges → ℝ := fun e => maskedCoupling (G.thinKernelEdges R S z) b
      (G.restrictEdge (· ∈ thinAnnulusSites R S z)
        (((G.thinAnnulusGraph R S z).translateEdgeEquiv z).symm e))
    let pins : Finset H.vertices :=
      (G.thinAnnulusGraph R S z).translatePins z (G.thinAnnulusPinFinset R S z)
    let θ : H.vertices → ℝ := H.thinThetaPotential k a δ
    let cut := H.innerCut R 0
    have hH : H.WithinDyadicBox k := G.translated_thinAnnulus_within_box R S k z hSbox
    have hbH : ∀ e, |bH e| ≤ β := by
      intro e
      dsimp only [bH, maskedCoupling]
      split_ifs
      · exact hb _
      · simpa using hβ
    have hpinradius (v : H.vertices) (hv : v ∈ pins) :
        siteRadius 0 v.val = R ∨ siteRadius 0 v.val = S :=
      G.translated_thinAnnulus_pin_radius R S z v hv
    have hθ : ∀ v ∈ pins, θ v = if v ∈ cut then 1 else 0 := by
      intro v hv
      simpa only [θ, cut, mem_innerCut] using
        H.thinThetaPotential_of_boundary_radius k a δ hδ ha R S hR hS v (hpinradius v hv)
    have hr : ∀ (υ : Configuration H.vertices) (t : ℝ),
        -((pinnedSystem (fun e : H.edges => e.val) bH pins υ).rotatePotential θ t).secondAxisResponse
          ((pinnedSystem (fun e : H.edges => e.val) bH pins υ).edgeGradient θ)
          ((pinnedSystem (fun e : H.edges => e.val) bH pins υ).edgeGradient θ) ≤ B := by
      intro υ t
      rw [pinnedSystem_rotatePotential_eq_cut _ _ _ _ _ hθ]
      let P : H.vertices → Option RP2.Spin := fun v =>
        if v ∈ pins then some (coordinateCut cut 2 t υ v) else none
      have hP : H.ThinBoundaryPins k a δ P := by
        apply H.thinBoundaryPins_of_radius k a δ R S hR hS P
        intro v s hs
        by_cases hv : v ∈ pins
        · exact hpinradius v hv
        · simp [P, hv] at hs
      exact hresponse H hH bH hbH P hP
    have hc := pinnedKernel_tetra_of_response (fun e : H.edges => e.val) bH pins cut
      θ hθ B hB hsmall hr g (fun v => τ (G.thinAnnulusOriginalVertex R S z v))
    have hcoef : 3*(B*(2*Real.pi)^2/2) = 6*Real.pi^2*B := by ring
    rw [hcoef] at hc
    rw [G.pinnedKernel_centered_thinAnnulus_cut R S z b tetraAction g τ,
      G.pinnedKernel_centered_thinAnnulus R S z b τ]
    exact hc
  · have hcoef : 1-6*Real.pi^2*B ≤ 0 := by nlinarith
    exact (mul_nonpos_of_nonpos_of_nonneg hcoef
      (pinnedPartition_pos _ _ _ _).le).trans (pinnedPartition_pos _ _ _ _).le

/-- The thin-shell comparison is proved for the actual RP² kernels. All
constants are selected before the scale, graph, couplings and pinned arrays. -/
theorem exists_thinKernelComparison_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ E : ℝ, 0 ≤ E ∧ ∃ F : ℝ, 0 ≤ F ∧ SignedThinDyadicKernelComparison β E F := by
  obtain ⟨K,V,hK,hV,hresponse⟩ := thin_annulus_response β hβ
  let E := 6*Real.pi^2*K
  let F := 6*Real.pi^2*V
  refine ⟨E, by dsimp [E]; positivity, F, by dsimp [F]; positivity, ?_⟩
  intro n h hh hh2 hm _hsmall j hj G b hb z g τ
  let R : ℤ := thinShellInner n h j
  let S : ℤ := R+(2:ℤ)^(n-h)
  let a : ℝ := (R:ℝ)/(2:ℝ)^n
  let δ : ℝ := 1/(2:ℝ)^h
  have hNR : (2:ℤ)^n ≤ R := by
    dsimp only [R]
    exact_mod_cast thinShell_inner_ge n h j
  have hSeq : S = (thinShellOuter n h j : ℤ) := by
    simp only [S, R, thinShellOuter, thinShellWidth, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
  have hSN : S ≤ 2*(2:ℤ)^n := by
    rw [hSeq]
    exact_mod_cast (thinShell_outer_lt hh (by omega) hj).le
  obtain ⟨hδ,hδ1,_ha1,ha,_hatop,hmesh,hRS,hR,hS⟩ :=
    thin_dyadic_parameters n h hh2 hm R hNR hSN
  change 0 < δ at hδ
  change δ ≤ 1 at hδ1
  change δ ≤ a at ha
  change 1/(2:ℝ)^n ≤ δ/16 at hmesh
  change R < S at hRS
  change (R:ℝ)=a*(2:ℝ)^n at hR
  change (S:ℝ)=(a+δ)*(2:ℝ)^n at hS
  let B := K/δ/(n:ℝ)+V/δ^6/(2:ℝ)^n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hc := thin_kernel_comparison_of_response n a δ hδ ha R S hR hS hSN β hβ B hB
    (hresponse n h (by omega) hh2 a δ hδ hδ1 ha le_rfl hmesh
      R S hNR hRS hSN hR hS) G b hb z g τ
  have he : 6*Real.pi^2*B ≤ thinDyadicError E F n h := by
    have hcost := thin_dyadic_response_cost n h (by omega) K V hK hV
    calc
      _ ≤ 6*Real.pi^2*(K*(2:ℝ)^h/((n-h:ℕ):ℝ)+V*(2:ℝ)^(6*h)/(2:ℝ)^n) :=
        mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = _ := by dsimp [E,F,thinDyadicError]; ring
  have hnonneg : 0 ≤ pinnedKernel (fun e : G.edges => e.val)
      (maskedCoupling (G.thinKernelEdges R S z) b) (G.thinLayer R S z)ᶜ
      ((tetraAction.onCut (G.innerCut R z)).move g τ) := (pinnedPartition_pos _ _ _ _).le
  have hfinal := (mul_le_mul_of_nonneg_right
    (show 1-thinDyadicError E F n h ≤ 1-6*Real.pi^2*B by linarith)
    hnonneg).trans hc
  simpa only [hSeq, R] using hfinal

end
end RP2.Fourier.LatticeGraph
