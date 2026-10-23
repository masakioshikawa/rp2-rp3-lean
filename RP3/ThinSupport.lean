module

public import RP3.ThinAnnuli

public section

/-! Cardinality of the support of thin-annulus mode gradients. -/
namespace RP3.Fourier
noncomputable section
open Finset
open scoped BigOperators

@[expose] def integerSquare (S : ℤ) : Finset Site :=
  Icc (-S) S ×ˢ Icc (-S) S

@[simp] theorem mem_integerSquare (S : ℤ) (v : Site) :
    v ∈ integerSquare S ↔ siteRadius (0,0) v ≤ S := by
  simp [integerSquare, siteRadius, max_le_iff, abs_le,
    and_assoc, and_left_comm, and_comm]

theorem integerSquare_mono {R S : ℤ} (h : R ≤ S) :
    integerSquare R ⊆ integerSquare S := by
  intro v hv
  exact (mem_integerSquare S v).mpr (((mem_integerSquare R v).mp hv).trans h)

theorem integerSquare_card (S : ℤ) (hS : 0 ≤ S) :
    ((integerSquare S).card : ℝ) = (2*(S:ℝ)+1)^2 := by
  have hi : ((Icc (-S) S).card : ℝ) = 2*(S:ℝ)+1 := by
    have hh := Int.card_Icc_of_le (-S) S (show -S ≤ S+1 by omega)
    have hh' : ((Icc (-S) S).card : ℤ) = 2*S+1 := by omega
    exact_mod_cast hh'
  simp only [integerSquare, card_product, Nat.cast_mul, hi]
  ring

@[expose] def integerSquareShell (R S : ℤ) : Finset Site :=
  integerSquare S \ integerSquare (R-1)

@[simp] theorem mem_integerSquareShell (R S : ℤ) (v : Site) :
    v ∈ integerSquareShell R S ↔ R ≤ siteRadius (0,0) v ∧ siteRadius (0,0) v ≤ S := by
  simp only [integerSquareShell, mem_sdiff, mem_integerSquare]
  omega

theorem integerSquareShell_card (R S : ℤ) (hR : 1 ≤ R) (hRS : R ≤ S) :
    ((integerSquareShell R S).card : ℝ) =
      4*((S:ℝ)+R)*((S:ℝ)-R+1) := by
  have hi := integerSquare_mono (show R-1 ≤ S by omega)
  have hc := card_sdiff_add_card_eq_card hi
  have hc' : ((integerSquareShell R S).card:ℝ) +
      ((integerSquare (R-1)).card:ℝ) = ((integerSquare S).card:ℝ) := by
    exact_mod_cast hc
  rw [integerSquare_card S (by omega), integerSquare_card (R-1) (by omega)] at hc'
  push_cast at hc'
  nlinarith

theorem integerSquareShell_card_bound (N R S : ℤ)
    (hN : 1 ≤ N) (hNR : N ≤ R) (hRS : R < S) (hSN : S ≤ 2*N) :
    ((integerSquareShell R S).card : ℝ) ≤ 32*(N:ℝ)*((S:ℝ)-R) := by
  rw [integerSquareShell_card R S (by omega) hRS.le]
  have hN' : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNR' : (N:ℝ) ≤ R := by exact_mod_cast hNR
  have hRS' : (R:ℝ)+1 ≤ S := by exact_mod_cast (show R+1 ≤ S by omega)
  have hSN' : (S:ℝ) ≤ 2*N := by exact_mod_cast hSN
  have hsum : (S:ℝ)+R ≤ 4*N := by linarith
  have hwidth : (S:ℝ)-R+1 ≤ 2*((S:ℝ)-R) := by linarith
  have hp := mul_le_mul hsum hwidth (by linarith : (0:ℝ) ≤ S-R+1)
    (by linarith : (0:ℝ) ≤ 4*N)
  nlinarith

namespace LatticeGraph

/-- An edge in the support is determined by its origin and its direction.
Both endpoints lie in the closed thin shell. -/
theorem thinKernelEdges_card_bound (G : LatticeGraph) (N R S : ℤ)
    (hN : 1 ≤ N) (hNR : N ≤ R) (hRS : R < S) (hSN : S ≤ 2*N) :
    ((G.thinKernelEdges R S (0,0)).card : ℝ) ≤
      64*(N:ℝ)*((S:ℝ)-R) := by
  let i : (G.thinKernelEdges R S (0,0)) → Bool × (integerSquareShell R S) :=
    fun e => (G.edgeDirection e.val, ⟨e.val.val.1.val,
      (mem_integerSquareShell R S _).mpr
        (G.thinKernelEdges_endpoints R S (0,0) e.val e.property).1⟩)
  have hi : Function.Injective i := by
    intro e f h
    have hm : G.edgeDirection e.val = G.edgeDirection f.val := congrArg Prod.fst h
    have hx : e.val.val.1 = f.val.val.1 := by
      apply Subtype.ext
      exact congrArg (fun q : Bool × integerSquareShell R S => q.2.val) h
    have he := G.edge_step e.val
    have hf := G.edge_step f.val
    have hy : e.val.val.2 = f.val.val.2 := by
      apply Subtype.ext
      rw [he, hf, hm, hx]
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext hx hy
  have hc := Fintype.card_le_of_injective i hi
  simp only [Fintype.card_coe, Fintype.card_prod, Fintype.card_bool] at hc
  have hc' : ((G.thinKernelEdges R S (0,0)).card:ℝ) ≤
      2*((integerSquareShell R S).card:ℝ) := by exact_mod_cast hc
  have hs := integerSquareShell_card_bound N R S hN hNR hRS hSN
  linarith

/-- A square-sum estimate that retains the thin spatial support. -/
theorem thin_supported_square_sum (G : LatticeGraph) (N R S : ℤ)
    (hN : 1 ≤ N) (hNR : N ≤ R) (hRS : R < S) (hSN : S ≤ 2*N)
    (U : G.edges → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hzero : ∀ e, e ∉ G.thinKernelEdges R S (0,0) → U e = 0)
    (hbound : ∀ e, ‖U e‖^2 ≤ B) :
    (∑ e, ‖U e‖^2) ≤ 64*(N:ℝ)*((S:ℝ)-R)*B := by
  classical
  have heq : (∑ e, ‖U e‖^2) = ∑ e ∈ G.thinKernelEdges R S (0,0), ‖U e‖^2 := by
    symm
    apply sum_subset (subset_univ _)
    intro e _ he
    simp [hzero e he]
  rw [heq]
  calc
    _ ≤ ∑ e ∈ G.thinKernelEdges R S (0,0), B := sum_le_sum fun e _ => hbound e
    _ = ((G.thinKernelEdges R S (0,0)).card:ℝ)*B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (G.thinKernelEdges_card_bound N R S hN hNR hRS hSN) hB

end LatticeGraph
end
end RP3.Fourier
