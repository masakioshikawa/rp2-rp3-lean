import Mathlib

/-!
# Exact annular averaging

Continuous functions are used so a positive linear functional can be actual
integration against a finite measure on a compact configuration space.
The abstract interface lists the structural averaging properties explicitly.
It contains no decay assumption and no correlation estimate.
-/

namespace RP2

open Finset

variable {Ω ι : Type*} [TopologicalSpace Ω]

/-- Unnormalised integration, retaining positivity and linearity. -/
structure PositiveIntegral (Ω : Type*) [TopologicalSpace Ω] where
  linear : C(Ω, ℝ) →ₗ[ℝ] ℝ
  nonneg : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ linear f

namespace PositiveIntegral

variable (I : PositiveIntegral Ω)

theorem mono {f g : C(Ω, ℝ)} (h : ∀ x, f x ≤ g x) : I.linear f ≤ I.linear g := by
  have hn := I.nonneg (g - f) (fun x => sub_nonneg.mpr (h x))
  simpa only [map_sub, sub_nonneg] using hn

/-- The elementary bounded-observable estimate for a nonnegative weight. -/
theorem abs_weighted_le (O W : C(Ω, ℝ)) {M : ℝ}
    (hO : ∀ x, |O x| ≤ M) (hW : ∀ x, 0 ≤ W x) :
    |I.linear (O * W)| ≤ M * I.linear W := by
  apply abs_le.mpr
  constructor
  · have h := I.mono (f := (-M) • W) (g := O * W) (fun x => by
      change -M * W x ≤ O x * W x
      exact mul_le_mul_of_nonneg_right (abs_le.mp (hO x)).1 (hW x))
    simpa using h
  · have h := I.mono (f := O * W) (g := M • W) (fun x => by
      change O x * W x ≤ M * W x
      exact mul_le_mul_of_nonneg_right (abs_le.mp (hO x)).2 (hW x))
    simpa using h

end PositiveIntegral

/-- A commuting family of averaging projections for nested cuts.

`pull` is the usual rule for taking an invariant factor out of an average.
`preserve` is invariance of the reference integral.  Commutation expresses
normalisation of inner rotations by outer rotations; it does NOT assert
independence of annuli.
-/
structure AveragingSystem (I : PositiveIntegral Ω) (ι : Type*) where
  avg : ι → C(Ω, ℝ) →ₗ[ℝ] C(Ω, ℝ)
  one : ∀ i, avg i 1 = 1
  idem : ∀ i f, avg i (avg i f) = avg i f
  commute : ∀ i j f, avg i (avg j f) = avg j (avg i f)
  pull : ∀ i f g, avg i f = f → avg i (f * g) = f * avg i g
  preserve : ∀ i f, I.linear (avg i f) = I.linear f

namespace AveragingSystem

variable {I : PositiveIntegral Ω} (S : AveragingSystem I ι)

/-- The positive remainder of one annular kernel. -/
noncomputable def remainder (i : ι) (ε : ℝ) (K : C(Ω, ℝ)) : C(Ω, ℝ) :=
  ε⁻¹ • (K - (1 - ε) • S.avg i K)

theorem split (i : ι) {ε : ℝ} (hε : ε ≠ 0) (K : C(Ω, ℝ)) :
    K = (1 - ε) • S.avg i K + ε • S.remainder i ε K := by
  ext x
  simp only [remainder, ContinuousMap.add_apply, ContinuousMap.smul_apply,
    ContinuousMap.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem remainder_nonneg (i : ι) {ε : ℝ} (hε : 0 < ε) (K : C(Ω, ℝ))
    (hlower : ∀ x, (1 - ε) * S.avg i K x ≤ K x) :
    ∀ x, 0 ≤ S.remainder i ε K x := by
  intro x
  exact mul_nonneg (inv_nonneg.mpr hε.le) (sub_nonneg.mpr (hlower x))

theorem avg_remainder (i : ι) {ε : ℝ} (hε : ε ≠ 0) (K : C(Ω, ℝ)) :
    S.avg i (S.remainder i ε K) = S.avg i K := by
  simp only [remainder, map_smul, map_sub, S.idem]
  ext x
  simp only [ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul]
  field_simp
  ring

theorem fixed_mul (i : ι) {f g : C(Ω, ℝ)}
    (hf : S.avg i f = f) (hg : S.avg i g = g) : S.avg i (f * g) = f * g := by
  rw [S.pull i f g hf, hg]

theorem fixed_prod (i : ι) (s : Finset ι) (K : ι → C(Ω, ℝ))
    (hK : ∀ j ∈ s, S.avg i (K j) = K j) :
    S.avg i (∏ j ∈ s, K j) = ∏ j ∈ s, K j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.one i
  | @insert j s hj ih =>
    simp only [prod_insert hj]
    apply S.fixed_mul
    · exact hK j (mem_insert_self _ _)
    · apply ih
      exact fun j hj => hK j (mem_insert_of_mem hj)

theorem remainder_fixed (i j : ι) {ε : ℝ} (K : C(Ω, ℝ))
    (hK : S.avg j K = K) : S.avg j (S.remainder i ε K) = S.remainder i ε K := by
  simp only [remainder, map_smul, map_sub, hK, S.commute j i K]

/-- Replacing one annulus by its remainder preserves the unnormalised partition function. -/
theorem partition_replace (i : ι) {ε : ℝ} (hε : ε ≠ 0)
    (W K : C(Ω, ℝ)) (hW : S.avg i W = W) :
    I.linear (W * S.remainder i ε K) = I.linear (W * K) := by
  calc
    _ = I.linear (S.avg i (W * S.remainder i ε K)) := (S.preserve _ _).symm
    _ = I.linear (W * S.avg i K) := by rw [S.pull _ _ _ hW, S.avg_remainder i hε K]
    _ = I.linear (S.avg i (W * K)) := by rw [S.pull _ _ _ hW]
    _ = _ := S.preserve _ _

/-- An averaged annulus kills an observable whose rotational average vanishes. -/
theorem numerator_average_zero (i : ι) (O W K : C(Ω, ℝ))
    (hO : S.avg i O = 0) (hW : S.avg i W = W) :
    I.linear (O * W * S.avg i K) = 0 := by
  have hF := S.fixed_mul i hW (S.idem i K)
  calc
    _ = I.linear ((W * S.avg i K) * O) := by congr 1; ring
    _ = I.linear (S.avg i ((W * S.avg i K) * O)) := (S.preserve _ _).symm
    _ = 0 := by rw [S.pull _ _ _ hF, hO, mul_zero, map_zero]

/-- Exactly one error factor is extracted; the remaining weight stays nonnegative. -/
theorem numerator_replace (i : ι) {ε : ℝ} (hε : ε ≠ 0)
    (O W K : C(Ω, ℝ)) (hO : S.avg i O = 0) (hW : S.avg i W = W) :
    I.linear (O * W * K) = ε * I.linear (O * W * S.remainder i ε K) := by
  have heq : O * W * K = (1 - ε) • (O * W * S.avg i K) +
      ε • (O * W * S.remainder i ε K) := by
    conv_lhs => rw [S.split i hε K]
    ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.add_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [heq, map_add, map_smul, map_smul, S.numerator_average_zero i O W K hO hW]
  simp

/-- The nested-annulus product estimate, proved by successive replacements.
All analytic information is in the pointwise lower bounds `hlower`.
The other hypotheses express locality, symmetry, and positivity. -/
theorem product_bound (s : Finset ι) (ε : ι → ℝ) (K : ι → C(Ω, ℝ))
    (O W : C(Ω, ℝ)) {M : ℝ}
    (hε : ∀ i ∈ s, 0 < ε i)
    (hK : ∀ i ∈ s, ∀ x, 0 ≤ K i x)
    (hlower : ∀ i ∈ s, ∀ x, (1 - ε i) * S.avg i (K i) x ≤ K i x)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S.avg i (K j) = K j)
    (hO : ∀ i ∈ s, S.avg i O = 0)
    (hObound : ∀ x, |O x| ≤ M)
    (hW : ∀ x, 0 ≤ W x) (hWfixed : ∀ i ∈ s, S.avg i W = W) :
    |I.linear (O * W * ∏ i ∈ s, K i)| ≤
      M * (∏ i ∈ s, ε i) * I.linear (W * ∏ i ∈ s, K i) := by
  classical
  induction s using Finset.induction_on generalizing W with
  | empty =>
    simpa using I.abs_weighted_le O W hObound hW
  | @insert i s hi ih =>
    have hi' : i ∈ insert i s := mem_insert_self i s
    have hin (j : ι) (hj : j ∈ s) : j ∈ insert i s := mem_insert_of_mem hj
    let L := S.remainder i (ε i) (K i)
    let P := ∏ j ∈ s, K j
    have hL : ∀ x, 0 ≤ L x := S.remainder_nonneg i (hε i hi') _ (hlower i hi')
    have hPfixed : S.avg i P = P := S.fixed_prod i s K (by
      intro j hj
      exact hcross i hi' j (hin j hj) (by intro he; subst j; exact hi hj))
    have hWP : S.avg i (W * P) = W * P := S.fixed_mul i (hWfixed i hi') hPfixed
    have hpart : I.linear ((W * L) * P) = I.linear (W * (K i * P)) := by
      calc
        _ = I.linear ((W * P) * L) := by congr 1; ring
        _ = I.linear ((W * P) * K i) :=
          S.partition_replace i (ne_of_gt (hε i hi')) (W * P) (K i) hWP
        _ = _ := by congr 1; ring
    have hnum : I.linear (O * W * (K i * P)) =
        ε i * I.linear (O * (W * L) * P) := by
      calc
        _ = I.linear (O * (W * P) * K i) := by congr 1; ring
        _ = ε i * I.linear (O * (W * P) * L) :=
          S.numerator_replace i (ne_of_gt (hε i hi')) O (W * P) (K i) (hO i hi') hWP
        _ = _ := by congr 2; ring
    have hb := ih (W * L)
      (fun j hj => hε j (hin j hj))
      (fun j hj => hK j (hin j hj))
      (fun j hj => hlower j (hin j hj))
      (fun j hj l hl => hcross j (hin j hj) l (hin l hl))
      (fun j hj => hO j (hin j hj))
      (fun x => mul_nonneg (hW x) (hL x)) (by
        intro j hj
        apply S.fixed_mul j (hWfixed j (hin j hj))
        exact S.remainder_fixed i j (K i)
          (hcross j (hin j hj) i hi' (by intro he; subst j; exact hi hj)))
    rw [prod_insert hi, prod_insert hi]
    change |I.linear (O * W * (K i * P))| ≤ _
    rw [hnum, abs_mul, abs_of_pos (hε i hi')]
    calc
      ε i * |I.linear (O * (W * L) * P)| ≤
          ε i * (M * (∏ j ∈ s, ε j) * I.linear ((W * L) * P)) :=
        mul_le_mul_of_nonneg_left hb (hε i hi').le
      _ = M * (ε i * ∏ j ∈ s, ε j) * I.linear (W * (K i * P)) := by
        rw [hpart]
        ring

/-- Division by a positive partition function gives the correlation bound. -/
theorem correlation_bound (s : Finset ι) (ε : ι → ℝ) (K : ι → C(Ω, ℝ))
    (O W : C(Ω, ℝ)) {M : ℝ}
    (hε : ∀ i ∈ s, 0 < ε i)
    (hK : ∀ i ∈ s, ∀ x, 0 ≤ K i x)
    (hlower : ∀ i ∈ s, ∀ x, (1 - ε i) * S.avg i (K i) x ≤ K i x)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → S.avg i (K j) = K j)
    (hO : ∀ i ∈ s, S.avg i O = 0) (hObound : ∀ x, |O x| ≤ M)
    (hW : ∀ x, 0 ≤ W x) (hWfixed : ∀ i ∈ s, S.avg i W = W)
    (hZ : 0 < I.linear (W * ∏ i ∈ s, K i)) :
    |I.linear (O * W * ∏ i ∈ s, K i) / I.linear (W * ∏ i ∈ s, K i)| ≤
      M * ∏ i ∈ s, ε i := by
  rw [abs_div, abs_of_pos hZ]
  exact (div_le_iff₀ hZ).mpr
    (S.product_bound s ε K O W hε hK hlower hcross hO hObound hW hWfixed)

end AveragingSystem
end RP2
