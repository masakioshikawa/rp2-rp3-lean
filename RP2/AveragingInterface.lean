module

public import RP2.Averaging

public section

/-!
# Simultaneous positive-remainder normalization

`AveragingSystem` already supplies the model-independent positive-remainder
argument. Its core public declarations are `remainder_nonneg`, `avg_remainder`,
`partition_replace`, `numerator_replace`, and `correlation_bound`.

The theorem below makes the multi-annulus identity `Z_rem = Z` explicit.
It assumes commuting averaging projections and invariance of distinct kernels,
not probabilistic independence or factorisation of their joint measure.
-/
namespace RP2.AveragingSystem

open Finset
variable {Ω ι : Type*} [TopologicalSpace Ω]
variable {I : PositiveIntegral Ω} (S : AveragingSystem I ι)

/-- Replacing every kernel in a finite family by its remainder preserves the
partition function exactly. Nonnegativity is not needed for this identity;
combine with `remainder_nonneg` for the positive-weight interpretation. -/
theorem partition_replace_all (s : Finset ι) (ε : ι → ℝ)
    (K : ι → C(Ω, ℝ)) (W : C(Ω, ℝ))
    (hε : ∀ i ∈ s, ε i ≠ 0)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S.avg i (K j) = K j)
    (hW : ∀ i ∈ s, S.avg i W = W) :
    I.linear (W * ∏ i ∈ s, S.remainder i (ε i) (K i)) =
      I.linear (W * ∏ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty => simp
  | @insert i s hi ih =>
    have hi' : i ∈ insert i s := mem_insert_self i s
    have hin (j : ι) (hj : j ∈ s) : j ∈ insert i s := mem_insert_of_mem hj
    have hWP : S.avg i (W * ∏ j ∈ s, K j) = W * ∏ j ∈ s, K j :=
      S.fixed_mul i (hW i hi') (S.fixed_prod i s K (by
        intro j hj
        exact hcross i hi' j (hin j hj) (by intro he; subst j; exact hi hj)))
    have hrest := ih (W * S.remainder i (ε i) (K i))
      (fun j hj => hε j (hin j hj))
      (fun j hj k hk => hcross j (hin j hj) k (hin k hk)) (by
        intro j hj
        apply S.fixed_mul j (hW j (hin j hj))
        exact S.remainder_fixed i j (K i)
          (hcross j (hin j hj) i hi' (by intro he; subst j; exact hi hj)))
    rw [prod_insert hi, prod_insert hi, ← mul_assoc, hrest]
    calc
      _ = I.linear ((W * ∏ j ∈ s, K j) * S.remainder i (ε i) (K i)) := by
        congr 1
        ring
      _ = I.linear ((W * ∏ j ∈ s, K j) * K i) :=
        S.partition_replace i (hε i hi') _ _ hWP
      _ = _ := by congr 1; ring

end RP2.AveragingSystem
