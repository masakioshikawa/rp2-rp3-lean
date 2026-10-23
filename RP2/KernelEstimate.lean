module

public import RP2.LatticeModelRestriction
public import RP2.ModelConnection
public import RP2.AnnularEstimate
public import RP2.TetrahedralComparison
public import RP2.SquareRates

public section

/-!
# Uniform tetrahedral comparison for actual annular RP² kernels

This module connects the analytic annulus estimate, the exact restricted and
translated Gibbs integral, and the finite rotational averaging group.
-/
namespace RP2
noncomputable section
open scoped Classical
open Rotation hiding Spin
open Quadratic
open Fourier

variable {V : Type*} [DecidableEq V]

theorem coordinateCut_zero (cut : Finset V) (a : Fin 3) (τ : Configuration V) :
    coordinateCut cut a 0 τ = τ := by
  funext v
  by_cases hv : v ∈ cut
  · apply Subtype.ext
    simpa only [coordinateCut, rotateCut, hv, ite_true, spinRotation_val] using
      coordinateRotation_zero a (τ v).val
  · simp only [coordinateCut, rotateCut, hv, ite_false]

namespace Fourier

theorem scaledSite_inner_of_radius {n : ℕ} {x : Site}
    (h : siteRadius 0 x ≤ (2:ℤ)^n) :
    |(scaledSite n x).1| ≤ 1 ∧ |(scaledSite n x).2| ≤ 1 := by
  have hn : 0 < (2:ℝ)^n := by positivity
  have hxy : |x.1| ≤ (2:ℤ)^n ∧ |x.2| ≤ (2:ℤ)^n := by
    simpa only [siteRadius, Prod.fst_zero, Prod.snd_zero, sub_zero, max_le_iff] using h
  have hx : |(x.1:ℝ)| ≤ (2:ℝ)^n := by exact_mod_cast hxy.1
  have hy : |(x.2:ℝ)| ≤ (2:ℝ)^n := by exact_mod_cast hxy.2
  simpa only [scaledSite, abs_div, abs_of_pos hn, div_le_one hn] using And.intro hx hy

theorem scaledSite_outer_of_radius {n : ℕ} {x : Site}
    (h : 2*(2:ℤ)^n ≤ siteRadius 0 x) :
    2 ≤ |(scaledSite n x).1| ∨ 2 ≤ |(scaledSite n x).2| := by
  have hn : 0 < (2:ℝ)^n := by positivity
  have hxy : 2*(2:ℤ)^n ≤ |x.1| ∨ 2*(2:ℤ)^n ≤ |x.2| := by
    simpa only [siteRadius, Prod.fst_zero, Prod.snd_zero, sub_zero, le_max_iff] using h
  rcases hxy with hx | hy
  · left
    have hxR : 2*(2:ℝ)^n ≤ |(x.1:ℝ)| := by exact_mod_cast hx
    simpa only [scaledSite, abs_div, abs_of_pos hn, le_div_iff₀ hn] using hxR
  · right
    have hyR : 2*(2:ℝ)^n ≤ |(x.2:ℝ)| := by exact_mod_cast hy
    simpa only [scaledSite, abs_div, abs_of_pos hn, le_div_iff₀ hn] using hyR

namespace LatticeGraph

/-- The continuum cutoff takes exactly the required values on both lattice
boundary layers, including nonconstant prescribed spin arrays. -/
theorem thetaPotential_of_boundary_radius (H : LatticeGraph) (n : ℕ)
    (v : H.vertices)
    (hv : siteRadius 0 v.val = (2:ℤ)^n ∨ siteRadius 0 v.val = 2*(2:ℤ)^n) :
    H.thetaPotential n v = if siteRadius 0 v.val ≤ (2:ℤ)^n then 1 else 0 := by
  by_cases hi : siteRadius 0 v.val ≤ (2:ℤ)^n
  · simp only [hi, ite_true, thetaPotential]
    exact squareTheta_one _ (scaledSite_inner_of_radius hi).1
      (scaledSite_inner_of_radius hi).2
  · simp only [hi, ite_false, thetaPotential]
    have ho : siteRadius 0 v.val = 2*(2:ℤ)^n :=
      hv.resolve_left (fun h => hi h.le)
    exact squareTheta_zero _ (scaledSite_outer_of_radius ho.ge)

/-- The actual full-graph annular kernel satisfies the uniform axis-C
comparison, with constants independent of graph and pinned spins. -/
theorem full_kernel_axisC_comparison (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, 4 ≤ n →
      ∀ (G : LatticeGraph) (b : G.edges → ℝ), (∀ e, |b e| ≤ β) →
      ∀ (z : Site) (t : ℝ) (τ : Configuration G.vertices),
      (1-D/(n:ℝ)) * pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n) z) b) (G.strictLayer (2^n) z)ᶜ
        (coordinateCut (G.innerCut (2^n) z) 2 t τ) ≤
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n) z) b) (G.strictLayer (2^n) z)ᶜ τ := by
  obtain ⟨D, hD, hratio⟩ := annulus_partition_inverse_scale β hβ
  refine ⟨D, hD, ?_⟩
  intro n hn G b hb z t τ
  let H := (G.annulusGraph (2^n) z).translate z
  let B : H.edges → ℝ := fun e => maskedCoupling (G.kernelEdges (2^n) z) b
    (G.restrictEdge (· ∈ annulusSites (2^n) z)
      (((G.annulusGraph (2^n) z).translateEdgeEquiv z).symm e))
  let pins : Finset H.vertices :=
    (G.annulusGraph (2^n) z).translatePins z (G.annulusPinFinset (2^n) z)
  let original : H.vertices → G.vertices := G.annulusOriginalVertex (2^n) z
  let P : H.vertices → Option RP2.Spin :=
    fun v => if v ∈ pins then some (τ (original v)) else none
  let τt : ℝ → Configuration H.vertices := fun s v =>
    coordinateCut (G.innerCut (2^n) z) 2 s τ (original v)
  have hB : ∀ e, |B e| ≤ β := by
    intro e
    dsimp only [B, maskedCoupling]
    split_ifs
    · exact hb _
    · simpa using hβ
  have hpRadius (v : H.vertices) (hv : v ∈ pins) :
      siteRadius 0 v.val = (2:ℤ)^n ∨ siteRadius 0 v.val = 2*(2:ℤ)^n :=
    G.translated_annulus_pin_radius (2^n) z v hv
  have hP : H.BoundaryPins n P := by
    intro v s hs
    by_cases hv : v ∈ pins
    · rcases hpRadius v hv with hi | ho
      · exact Or.inl (scaledSite_inner_of_radius hi.le)
      · exact Or.inr (scaledSite_outer_of_radius ho.ge)
    · simp only [P, hv, ite_false] at hs
      cases hs
  have hpin (s : ℝ) : H.rotatedBoundaryPins n P s =
      (fun v => if v ∈ pins then some (τt s v) else none) := by
    funext v
    by_cases hv : v ∈ pins
    · simp only [rotatedBoundaryPins, P, hv, ite_true, Option.map_some]
      apply congrArg some
      apply Subtype.ext
      have hθ := H.thetaPotential_of_boundary_radius n v (hpRadius v hv)
      have hr := G.annulusOriginalVertex_radius (2^n) z v
      by_cases hi : siteRadius 0 v.val ≤ (2:ℤ)^n
      · simp only [hi, ite_true] at hθ
        simp only [τt, coordinateCut, rotateCut, original, mem_innerCut,
          annulusOriginalVertex_radius, hi, ite_true, spinRotation_val,
          SpinSystem.potentialRotation, hθ, mul_one,
          coordinateRotation_apply, coordinateAxis, rotationExp_apply]
        try rfl
      · simp only [hi, ite_false] at hθ
        simp only [τt, coordinateCut, rotateCut, original, mem_innerCut,
          annulusOriginalVertex_radius, hi, ite_false, spinRotation_val,
          SpinSystem.potentialRotation, hθ, mul_zero, zero_smul ℝ axisC,
          rotationExp_apply, NormedSpace.exp_zero, one_apply_eq_self]
    · simp only [rotatedBoundaryPins, P, hv, ite_false, Option.map_none]
  have hZ (s : ℝ) : (H.spinSystem B (H.rotatedBoundaryPins n P s)).Z (fun _ => 1) =
      pinnedKernel (fun e : G.edges => e.val)
        (maskedCoupling (G.kernelEdges (2^n) z) b) (G.strictLayer (2^n) z)ᶜ
        (coordinateCut (G.innerCut (2^n) z) 2 s τ) := by
    rw [hpin]
    change (Quadratic.pinnedSystem (fun e : H.edges => e.val) B pins (τt s)).Z
      (fun _ => 1) = _
    rw [Quadratic.pinnedSystem_partition]
    exact (G.pinnedKernel_centered_annulus (2^n) z b
      (coordinateCut (G.innerCut (2^n) z) 2 s τ)).symm
  have h := hratio n hn H (G.translated_annulus_within_box n z) B hB P hP 0 t
  rw [hZ, hZ, coordinateCut_zero] at h
  exact (le_div_iff₀ (pinnedPartition_pos _ _ _ _)).mp h

/-- All analytic and geometric obligations for the actual tetrahedral kernel
comparison are now discharged. -/
theorem exists_dyadicKernelComparison_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ (D : ℝ) (a : ℕ), 0 < D ∧ 4 ≤ a ∧ SignedDyadicKernelComparison β D a := by
  obtain ⟨D, hD, haxis⟩ := full_kernel_axisC_comparison β hβ
  obtain ⟨m, hm⟩ := exists_nat_gt (D+1)
  refine ⟨3*(D+1), max 4 m, by positivity, le_max_left _ _, ?_⟩
  intro n hn G b hb z g τ
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  let K := fun υ => pinnedKernel (fun e : G.edges => e.val)
    (maskedCoupling (G.kernelEdges (2^n) z) b) (G.strictLayer (2^n) z)ᶜ υ
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnD : D+1 ≤ (n:ℝ) := by
    have hmn : (m:ℝ) ≤ n := by exact_mod_cast ((le_max_right 4 m).trans hn)
    linarith
  have hK : ∀ υ, 0 ≤ K υ := fun υ => (pinnedPartition_pos _ _ _ υ).le
  have hglobal : ∀ h υ, K (tetraGlobalMove h υ) = K υ := by
    intro h υ
    exact pinnedPartition_globalRotation _ _ _ (tetraLinearIsometry h) υ
  have hC : ∀ s υ, (1-(D+1)/(n:ℝ)) * K (coordinateCut (G.innerCut (2^n) z) 2 s υ) ≤ K υ := by
    intro s υ
    have hh := haxis n hn4 G b hb z s υ
    have hfactor : 1-(D+1)/(n:ℝ) ≤ 1-D/(n:ℝ) := by
      apply sub_le_sub_left
      exact div_le_div_of_nonneg_right (by linarith) hnpos.le
    exact (mul_le_mul_of_nonneg_right hfactor (hK _)).trans hh
  have h := tetraCut_comparison_of_axisC K hK hglobal (G.innerCut (2^n) z)
    (div_nonneg (by positivity) hnpos.le) ((div_le_one hnpos).mpr hnD) hC g τ
  convert h using 1 <;> ring

theorem dyadic_kernel_comparison_signed (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D > 0, ∃ a : ℕ, 2 ≤ a ∧ SignedDyadicKernelComparison β D a := by
  obtain ⟨D, a, hD, ha, hcomp⟩ := exists_dyadicKernelComparison_signed β hβ
  exact ⟨D, hD, a, by omega, hcomp⟩
/-- The original ferromagnetic comparison is a consequence of the signed one. -/
theorem exists_dyadicKernelComparison (β : ℝ) (hβ : 0 ≤ β) :
    ∃ (D : ℝ) (a : ℕ), 0 < D ∧ 4 ≤ a ∧ DyadicKernelComparison β D a := by
  obtain ⟨D, a, hD, ha, hcomp⟩ := exists_dyadicKernelComparison_signed β hβ
  exact ⟨D, a, hD, ha, hcomp.toNonnegative⟩

theorem dyadic_kernel_comparison (β : ℝ) (hβ : 0 ≤ β) :
    ∃ D > 0, ∃ a : ℕ, 2 ≤ a ∧ DyadicKernelComparison β D a := by
  obtain ⟨D, hD, a, ha, hcomp⟩ := dyadic_kernel_comparison_signed β hβ
  exact ⟨D, hD, a, ha, hcomp.toNonnegative⟩

end LatticeGraph
end Fourier
end
end RP2
