module

public import RP3.RotationGeometryBase
public import RP3.FourierAll

public section

/-! Proofs contributed in the Claude Opus review supplied by the user on
11 October 2026, integrated and checked against this pinned development.
See REVIEW-RESPONSE.md for scope and attribution. -/
noncomputable section
open MeasureTheory Filter RP3
open scoped InnerProductSpace BigOperators Matrix Topology

namespace RP3.ModelWitnesses

/-- Index set for `±1, ±i, ±j, ±k` and `(±1 ± i ± j ± k)/2`. -/
abbrev Idx := (Fin 4 × Bool) ⊕ (Bool × Bool × Bool × Bool)

@[expose] def sg (b : Bool) : ℝ := if b then 1 else -1

/-- Real coordinates of the 24 unit quaternions of `2T`. -/
@[expose] def gvec : Idx → Fin 4 → ℝ
  | .inl (k, s) => fun i => if i = k then sg s else 0
  | .inr (a, b, c, d) => ![sg a / 2, sg b / 2, sg c / 2, sg d / 2]

theorem card_Idx : Fintype.card Idx = 24 := by simp

theorem gvec_sq (g : Idx) : ∑ i, gvec g i ^ 2 = 1 := by
  rcases g with ⟨k, s⟩ | ⟨a, b, c, d⟩
  · fin_cases k <;> cases s <;> simp [gvec, sg]
  · cases a <;> cases b <;> cases c <;> cases d <;> simp [gvec, sg, Fin.sum_univ_four] <;> norm_num

theorem orbit_moment2 (w : Fin 4 → ℝ) :
    ∑ g : Idx, (∑ i, gvec g i * w i) ^ 2 = 6 * ∑ i, w i ^ 2 := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_four, gvec, sg]
  ring

theorem orbit_moment4 (w : Fin 4 → ℝ) :
    ∑ g : Idx, (∑ i, gvec g i * w i) ^ 4 = 3 * (∑ i, w i ^ 2) ^ 2 := by
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_four, gvec, sg]
  ring

/-- Left multiplication by the quaternion `g` in real coordinates (`= qMatrix`). -/
@[expose] def lmulFun (g u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![g 0 * u 0 - g 1 * u 1 - g 2 * u 2 - g 3 * u 3,
    g 1 * u 0 + g 0 * u 1 - g 3 * u 2 + g 2 * u 3,
    g 2 * u 0 + g 3 * u 1 + g 0 * u 2 - g 1 * u 3,
    g 3 * u 0 - g 2 * u 1 + g 1 * u 2 + g 0 * u 3]

/-- Coordinates of `v ū`; then `⟨g u, v⟩ = ⟨g, v ū⟩`. -/
@[expose] def W (u v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![v 0 * u 0 + v 1 * u 1 + v 2 * u 2 + v 3 * u 3,
    -v 0 * u 1 + v 1 * u 0 - v 2 * u 3 + v 3 * u 2,
    -v 0 * u 2 + v 1 * u 3 + v 2 * u 0 - v 3 * u 1,
    -v 0 * u 3 - v 1 * u 2 + v 2 * u 1 + v 3 * u 0]

theorem pair_eq (g u v : Fin 4 → ℝ) :
    ∑ i, lmulFun g u i * v i = ∑ i, g i * W u v i := by
  simp [Fin.sum_univ_four, lmulFun, W]
  ring

theorem W_sq (u v : Fin 4 → ℝ) :
    ∑ i, W u v i ^ 2 = (∑ i, u i ^ 2) * (∑ i, v i ^ 2) := by
  simp [Fin.sum_univ_four, W]
  ring

theorem lmul_sq (g u : Fin 4 → ℝ) :
    ∑ i, lmulFun g u i ^ 2 = (∑ i, g i ^ 2) * (∑ i, u i ^ 2) := by
  simp [Fin.sum_univ_four, lmulFun]
  ring

@[expose] def lmulLin (g : Fin 4 → ℝ) : E4 →ₗ[ℝ] E4 where
  toFun u := WithLp.toLp 2 (lmulFun g u)
  map_add' u v := by
    ext i
    fin_cases i <;> simp [lmulFun] <;> ring
  map_smul' r u := by
    ext i
    fin_cases i <;> simp [lmulFun] <;> ring

@[simp] theorem lmulLin_apply (g : Fin 4 → ℝ) (u : E4) (i : Fin 4) :
    lmulLin g u i = lmulFun g u i := rfl

theorem lmulLin_norm (g : Fin 4 → ℝ) (hg : ∑ i, g i ^ 2 = 1) (u : E4) :
    ‖lmulLin g u‖ = ‖u‖ := by
  have hs : ‖lmulLin g u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [lmulLin_apply]
    rw [lmul_sq, hg, one_mul]
  nlinarith [norm_nonneg (lmulLin g u), norm_nonneg u]

/-- Left multiplication by any unit quaternion, as a linear isometry of `ℝ⁴`. -/
@[expose] def lmulIsoOf (g : Fin 4 → ℝ) (hg : ∑ i, g i ^ 2 = 1) : E4 ≃ₗᵢ[ℝ] E4 :=
  LinearIsometry.toLinearIsometryEquiv
    { lmulLin g with norm_map' := lmulLin_norm g hg } rfl

@[simp] theorem lmulIsoOf_apply (g : Fin 4 → ℝ) (hg : ∑ i, g i ^ 2 = 1) (u : E4) (i : Fin 4) :
    lmulIsoOf g hg u i = lmulFun g u i := rfl

@[expose] def lmulIso (x : Idx) : E4 ≃ₗᵢ[ℝ] E4 := lmulIsoOf (gvec x) (gvec_sq x)

@[simp] theorem lmulIso_apply (x : Idx) (u : E4) (i : Fin 4) :
    lmulIso x u i = lmulFun (gvec x) u i := rfl

theorem inner_eq_sum (a b : E4) : ⟪a, b⟫_ℝ = ∑ i, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

theorem orbit_sum_tau (s t : Spin) :
    ∑ x : Idx, (⟪lmulIso x s.val, t.val⟫_ℝ ^ 2 - 1 / 4) = 0 := by
  have h2 := orbit_moment2 (W s.val t.val)
  rw [W_sq, spin_squares, spin_squares] at h2
  simp only [inner_eq_sum, lmulIso_apply, pair_eq]
  rw [Finset.sum_sub_distrib, h2]
  simp
  norm_num

theorem orbit_sum_tau_sq (s t : Spin) :
    ∑ x : Idx, (⟪lmulIso x s.val, t.val⟫_ℝ ^ 2 - 1 / 4) ^ 2 = 24 * (1 / 16) := by
  have h2 := orbit_moment2 (W s.val t.val)
  have h4 := orbit_moment4 (W s.val t.val)
  rw [W_sq, spin_squares, spin_squares] at h2 h4
  simp only [inner_eq_sum, lmulIso_apply, pair_eq]
  have hexp : ∀ z : ℝ, (z ^ 2 - 1 / 4) ^ 2 = z ^ 4 - (1 / 2) * z ^ 2 + 1 / 16 := by
    intro z; ring
  simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h2, h4]
  simp
  norm_num

section Averaging
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rotate the spin at one site by `lmulIso x`, leaving all others fixed. -/
@[expose] def rotAt (v₀ : V) (x : Idx) (σ : Configuration V) : Configuration V :=
  fun v => (if v = v₀ then (Rotation.spinRotation (lmulIso x) : Spin → Spin) else id) (σ v)

theorem rotAt_mp (v₀ : V) (x : Idx) :
    MeasurePreserving (rotAt v₀ x) (referenceLaw (V := V)) referenceLaw := by
  unfold rotAt referenceLaw
  refine measurePreserving_pi (fun _ => sphereProbability) (fun _ => sphereProbability)
    (fun v => ?_)
  by_cases hv : v = v₀
  · simp only [hv, ite_true]
    exact Rotation.spinRotation_preserves_probability (lmulIso x)
  · simp only [hv, ite_false]
    exact MeasurePreserving.id _

theorem integral_eq_of_orbit (v₀ : V) (F : Configuration V → ℝ) (hF : Continuous F)
    (c : ℝ) (havg : ∀ σ, ∑ x : Idx, F (rotAt v₀ x σ) = 24 * c) :
    ∫ σ, F σ ∂(referenceLaw (V := V)) = c := by
  have hFi : Integrable F (referenceLaw (V := V)) :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcomp : ∀ x : Idx, ∫ σ, F (rotAt v₀ x σ) ∂(referenceLaw (V := V)) =
      ∫ σ, F σ ∂(referenceLaw (V := V)) := by
    intro x
    rw [← integral_map (rotAt_mp v₀ x).measurable.aemeasurable
      hF.aestronglyMeasurable, (rotAt_mp v₀ x).map_eq]
  have hint : ∀ x : Idx, Integrable (fun σ => F (rotAt v₀ x σ)) (referenceLaw (V := V)) :=
    fun x => ((rotAt_mp v₀ x).integrable_comp hF.aestronglyMeasurable).mpr hFi
  have hsum : ∫ σ, ∑ x : Idx, F (rotAt v₀ x σ) ∂(referenceLaw (V := V)) =
      24 * ∫ σ, F σ ∂(referenceLaw (V := V)) := by
    rw [integral_finsetSum _ (fun x _ => hint x)]
    simp [hcomp]
  simp only [havg] at hsum
  simp at hsum
  linarith

end Averaging

/-- The one-bond graph `(0,0) — (1,0)`. -/
@[expose] def V0 : Finset Fourier.Site := {(0, 0), (1, 0)}
@[expose] def L0' : V0 := ⟨(0, 0), by simp [V0]⟩
@[expose] def R0' : V0 := ⟨(1, 0), by simp [V0]⟩

@[expose] def G1 : Fourier.LatticeGraph where
  vertices := V0
  edges := {(L0', R0')}
  nearest := by
    intro e he
    simp only [Finset.mem_singleton] at he
    subst e
    left
    norm_num [L0', R0']

@[expose] def L0 : G1.vertices := L0'
@[expose] def R0 : G1.vertices := R0'

theorem L0_ne_R0 : L0 ≠ R0 := by
  intro h
  have := congrArg Subtype.val h
  simp [L0, R0, L0', R0'] at this

theorem interaction_G1 (b0 : ℝ) (σ : Configuration G1.vertices) :
    interaction (fun e : G1.edges => e.val) (fun _ => b0) σ =
      b0 * ⟪(σ L0).val, (σ R0).val⟫_ℝ ^ 2 := by
  unfold interaction
  rw [Finset.sum_coe_sort G1.edges
    (fun e => b0 * ⟪(σ e.1).val, (σ e.2).val⟫_ℝ ^ 2),
    show G1.edges = ({(L0, R0)} : Finset (G1.vertices × G1.vertices)) from rfl,
    Finset.sum_singleton]

theorem exp_lower (b τ : ℝ) (hb : 0 < b) (hτ : -1 / 4 ≤ τ) :
    τ + b * Real.exp (-b / 4) * τ ^ 2 ≤ τ * Real.exp (b * τ) := by
  have hE := Real.add_one_le_exp (b * τ)
  have hF := Real.add_one_le_exp (-(b * τ))
  have hEF : Real.exp (b * τ) * Real.exp (-(b * τ)) = 1 := by
    rw [← Real.exp_add]; simp
  have hm : Real.exp (-b / 4) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have hm0 : 0 < Real.exp (-b / 4) := Real.exp_pos _
  have hE0 : 0 < Real.exp (b * τ) := Real.exp_pos _
  rcases le_or_gt 0 τ with h0 | h0
  · have : τ * (b * τ + 1) ≤ τ * Real.exp (b * τ) := mul_le_mul_of_nonneg_left hE h0
    nlinarith [sq_nonneg τ, mul_nonneg hb.le (sq_nonneg τ)]
  · have hlow : Real.exp (-b / 4) ≤ Real.exp (b * τ) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have hstep : Real.exp (b * τ) - 1 ≤ b * τ * Real.exp (b * τ) := by
      nlinarith [hF, hEF, hE0]
    have hstep2 : b * τ * Real.exp (b * τ) ≤ b * τ * Real.exp (-b / 4) := by
      have hbτ : b * τ ≤ 0 := by nlinarith
      exact mul_le_mul_of_nonpos_left hlow hbτ
    nlinarith [hstep, hstep2]

/-- **Suggested witness.** On the one-bond graph, every positive coupling gives a
strictly positive correlation between the two distinct endpoints. -/
theorem G1_correlation_pos (b0 : ℝ) (hb : 0 < b0) :
    0 < correlation (fun e : G1.edges => e.val) (fun _ => b0) L0 R0 := by
  apply div_pos _ (partition_pos _ _)
  change 0 < ∫ σ, qPair (σ L0) (σ R0) *
    Real.exp (interaction (fun e : G1.edges => e.val) (fun _ => b0) σ) ∂referenceLaw
  simp_rw [interaction_G1]
  set τ : Configuration G1.vertices → ℝ := fun σ => qPair (σ L0) (σ R0) with hτdef
  have hτc : Continuous τ := by
    simp only [hτdef, qPair]; fun_prop
  have hrot : ∀ (x : Idx) σ, τ (rotAt L0 x σ) =
      ⟪lmulIso x (σ L0).val, (σ R0).val⟫_ℝ ^ 2 - 1 / 4 := by
    intro x σ
    simp [hτdef, qPair, rotAt, L0_ne_R0.symm]
  have hmean : ∫ σ, τ σ ∂(referenceLaw (V := G1.vertices)) = 0 :=
    integral_eq_of_orbit L0 τ hτc 0 (fun σ => by
      simp only [hrot]; rw [orbit_sum_tau]; ring)
  have hvar : ∫ σ, τ σ ^ 2 ∂(referenceLaw (V := G1.vertices)) = 1 / 16 :=
    integral_eq_of_orbit L0 (fun σ => τ σ ^ 2) (hτc.pow 2) (1 / 16) (fun σ => by
      simp only [hrot]; exact orbit_sum_tau_sq _ _)
  have hw : ∀ σ : Configuration G1.vertices,
      qPair (σ L0) (σ R0) * Real.exp (b0 * ⟪(σ L0).val, (σ R0).val⟫_ℝ ^ 2) =
        Real.exp (b0 / 4) * (τ σ * Real.exp (b0 * τ σ)) := by
    intro σ
    simp only [hτdef, qPair]
    rw [show b0 * ⟪(σ L0).val, (σ R0).val⟫_ℝ ^ 2 =
      b0 / 4 + b0 * (⟪(σ L0).val, (σ R0).val⟫_ℝ ^ 2 - 1 / 4) by ring, Real.exp_add]
    ring
  simp_rw [hw]
  rw [integral_const_mul]
  apply mul_pos (Real.exp_pos _)
  have hint1 : Integrable (fun σ => τ σ + b0 * Real.exp (-b0 / 4) * τ σ ^ 2)
      (referenceLaw (V := G1.vertices)) :=
    (by fun_prop : Continuous fun σ => τ σ + b0 * Real.exp (-b0 / 4) * τ σ ^ 2)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun σ => τ σ * Real.exp (b0 * τ σ))
      (referenceLaw (V := G1.vertices)) :=
    (by fun_prop : Continuous fun σ => τ σ * Real.exp (b0 * τ σ))
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hlow : ∫ σ, (τ σ + b0 * Real.exp (-b0 / 4) * τ σ ^ 2) ∂referenceLaw ≤
      ∫ σ, τ σ * Real.exp (b0 * τ σ) ∂referenceLaw := by
    apply integral_mono hint1 hint2
    intro σ
    apply exp_lower b0 (τ σ) hb
    have : 0 ≤ ⟪(σ L0).val, (σ R0).val⟫_ℝ ^ 2 := sq_nonneg _
    simp only [hτdef, qPair]; linarith
  have hval : ∫ σ, (τ σ + b0 * Real.exp (-b0 / 4) * τ σ ^ 2)
      ∂(referenceLaw (V := G1.vertices)) = b0 * Real.exp (-b0 / 4) * (1 / 16) := by
    have hτi : Integrable τ (referenceLaw (V := G1.vertices)) :=
      hτc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hτ2i : Integrable (fun σ => b0 * Real.exp (-b0 / 4) * τ σ ^ 2)
        (referenceLaw (V := G1.vertices)) :=
      (by fun_prop : Continuous fun σ => b0 * Real.exp (-b0 / 4) * τ σ ^ 2)
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_add hτi hτ2i, integral_const_mul, hmean, hvar]
    ring
  have hpos : 0 < b0 * Real.exp (-b0 / 4) * (1 / 16) := by positivity
  linarith

/-- **Suggested witness.** The headline bound concerns a quantity that is not
identically zero off the diagonal. -/
theorem exists_distinct_sites_positive_correlation (β : ℝ) (hβ : 0 < β) :
    ∃ (G : Fourier.LatticeGraph) (b : G.edges → ℝ) (x y : G.vertices),
      x ≠ y ∧ (∀ e, |b e| ≤ β) ∧ 0 < correlation (fun e : G.edges => e.val) b x y :=
  ⟨G1, fun _ => β, L0, R0, L0_ne_R0, fun _ => by simp [abs_of_pos hβ],
    G1_correlation_pos β hβ⟩


end RP3.ModelWitnesses

end
