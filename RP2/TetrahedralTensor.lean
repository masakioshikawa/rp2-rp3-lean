module

public import RP2.TetrahedralAction

public section

/-!
# Tetrahedral cancellation of the quadrupole tensor

The existing scalar cancellation is promoted to a tensor identity. Twelve
orientation-preserving rotations suffice to annihilate every quadrupole; Haar
averaging over the full rotation group is unnecessary for this step.
-/
namespace RP2
noncomputable section
open scoped BigOperators

/-- The unnormalised tetrahedral sum annihilates the entire quadrupole tensor. -/
theorem tetraAction_sum_Q_zero (s : Spin) :
    ∑ g : Tetrahedral, Q (tetraAction.move g s) = 0 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.zero_apply]
  have hs := spin_squares s
  norm_num [Fin.sum_univ_succ] at hs
  change s.val 0 ^ 2 + (s.val 1 ^ 2 + s.val 2 ^ 2) = 1 at hs
  have hp : (∑ a : Fin 3, ∑ b : Fin 4,
      (tetraRotate a b s.val i * tetraRotate a b s.val j -
        if i = j then (1 : ℝ) / 3 else 0)) = 0 := by
    fin_cases i <;> fin_cases j <;>
      norm_num [tetraRotate, evenSigns, cyclic, Fin.sum_univ_succ] <;> nlinarith [hs]
  rw [← Fintype.sum_prod_type', ← Equiv.sum_comp tetrahedralIndex] at hp
  simpa only [Q, tetraAction_val,
    tetraLinear_apply, tetrahedralIndex_apply] using hp

/-- Exactly normalised tensor cancellation: `(1/12) ∑ᵣ Q(Rs) = 0`. -/
theorem tetraAction_average_Q_zero (s : Spin) :
    (12 : ℝ)⁻¹ • (∑ g : Tetrahedral, Q (tetraAction.move g s)) = 0 := by
  rw [tetraAction_sum_Q_zero, smul_zero]

/-- Exactly normalised scalar cancellation with the same finite group. -/
theorem tetraAction_average_qPair_zero (s t : Spin) :
    (12 : ℝ)⁻¹ * (∑ g : Tetrahedral, qPair (tetraAction.move g s) t) = 0 := by
  rw [tetraAction_sum_qPair_zero, mul_zero]

end
end RP2
