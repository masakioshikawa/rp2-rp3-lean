import RP3.FiniteAveraging

/-!
# The finite-volume RP³ model and its quadrupolar observable

Spins are unit vectors, and the interaction and observable are invariant under
independent changes of sign.  Thus they descend to director spins without
choosing a global lift.  No decay theorem is assumed in this module.
-/

namespace RP3

open MeasureTheory
open scoped BigOperators InnerProductSpace

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev Spin := Metric.sphere (0 : E4) 1

@[simp] theorem spin_norm (s : Spin) : ‖s.val‖ = 1 :=
  mem_sphere_zero_iff_norm.mp s.property

noncomputable def antipode (s : Spin) : Spin :=
  ⟨-s.val, mem_sphere_zero_iff_norm.mpr (by simp)⟩

noncomputable def qPair (s t : Spin) : ℝ :=
  ⟪s.val, t.val⟫_ℝ ^ 2 - 1/4

/-- The quadrupolar observable is a function of directors. -/
@[simp] theorem qPair_antipode_left (s t : Spin) : qPair (antipode s) t = qPair s t := by
  simp [qPair, antipode]

@[simp] theorem qPair_antipode_right (s t : Spin) : qPair s (antipode t) = qPair s t := by
  simp [qPair, antipode]

/-- This normalisation is `Tr (Q(s) Q(t))`, not the Legendre `P₂` normalisation. -/
theorem abs_qPair_le (s t : Spin) : |qPair s t| ≤ (3 : ℝ) / 4 := by
  have h := abs_real_inner_le_norm s.val t.val
  simp only [spin_norm, one_mul] at h
  have hs : ⟪s.val, t.val⟫_ℝ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr h
  rw [qPair, abs_le]
  constructor <;> nlinarith [sq_nonneg ⟪s.val, t.val⟫_ℝ]

noncomputable def Q (s : Spin) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => s.val i * s.val j - if i = j then 1/4 else 0

theorem spin_squares (s : Spin) : ∑ i : Fin 4, s.val i ^ 2 = 1 := by
  rw [← EuclideanSpace.real_norm_sq_eq, spin_norm]
  norm_num

/-- The tensor and scalar definitions of the observable coincide. -/
theorem trace_Q_mul (s t : Spin) : Matrix.trace (Q s * Q t) = qPair s t := by
  have hs := spin_squares s
  have ht := spin_squares t
  simp [Fin.sum_univ_succ] at hs ht
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Q, qPair, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num
  nlinarith [hs, ht]

/-- Normalised surface area on the sphere. -/
noncomputable def sphereProbability : Measure Spin :=
  ((volume : Measure E4).toSphere Set.univ)⁻¹ • (volume : Measure E4).toSphere

instance sphereProbability_isProbability : IsProbabilityMeasure sphereProbability := by
  have hs : (volume : Measure E4).toSphere ≠ 0 := Measure.toSphere_ne_zero _
  constructor
  dsimp [sphereProbability]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_eq_zero.not.mpr hs)
    (measure_ne_top _ _)

section FiniteVolume

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev Configuration (V : Type*) := V → Spin

noncomputable def referenceLaw : Measure (Configuration V) :=
  Measure.pi (fun _ => sphereProbability)

instance referenceLaw_isProbability : IsProbabilityMeasure (referenceLaw (V := V)) := by
  unfold referenceLaw
  infer_instance

/-- General finite graph with oriented representatives of its unoriented edges.
The square-lattice geometry is needed later, when annuli are constructed. -/
noncomputable def interaction (edge : E → V × V) (b : E → ℝ)
    (σ : Configuration V) : ℝ :=
  ∑ e, b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2

noncomputable def weight (edge : E → V × V) (b : E → ℝ) : C(Configuration V, ℝ) :=
  ⟨fun σ => Real.exp (interaction edge b σ), by unfold interaction; fun_prop⟩

noncomputable def observable (x y : V) : C(Configuration V, ℝ) :=
  ⟨fun σ => qPair (σ x) (σ y), by unfold qPair; fun_prop⟩

noncomputable def partition (edge : E → V × V) (b : E → ℝ) : ℝ :=
  (integralOnCompact (referenceLaw (V := V))).linear (weight edge b)

noncomputable def correlation (edge : E → V × V) (b : E → ℝ) (x y : V) : ℝ :=
  (integralOnCompact (referenceLaw (V := V))).linear
    (observable x y * weight edge b) / partition edge b

theorem partition_pos (edge : E → V × V) (b : E → ℝ) : 0 < partition edge b := by
  change 0 < ∫ σ, Real.exp (interaction edge b σ) ∂referenceLaw
  apply (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    ((weight edge b).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))).mpr
  have hs : Function.support (fun σ : Configuration V => Real.exp (interaction edge b σ)) =
      Set.univ := by ext σ; simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs, measure_univ]
  exact zero_lt_one

theorem abs_correlation_le (edge : E → V × V) (b : E → ℝ) (x y : V) :
    |correlation edge b x y| ≤ (3 : ℝ) / 4 := by
  have hb := (integralOnCompact (referenceLaw (V := V))).abs_weighted_le
    (observable x y) (weight edge b)
    (fun σ => abs_qPair_le (σ x) (σ y)) (fun σ => (Real.exp_pos _).le)
  unfold correlation
  rw [abs_div, abs_of_pos (partition_pos edge b)]
  exact (div_le_iff₀ (partition_pos edge b)).mpr hb

noncomputable def signChange (η : V → Bool) (σ : Configuration V) : Configuration V :=
  fun x => if η x then antipode (σ x) else σ x

omit [Fintype V] in
/-- Local sign changes leave the energy exactly unchanged. -/
theorem interaction_signChange (edge : E → V × V) (b : E → ℝ)
    (η : V → Bool) (σ : Configuration V) :
    interaction edge b (signChange η σ) = interaction edge b σ := by
  unfold interaction
  apply Finset.sum_congr rfl
  intro e _
  simp only [signChange]
  split_ifs <;> simp [antipode]

omit [Fintype V] in
theorem observable_signChange (x y : V) (η : V → Bool) (σ : Configuration V) :
    observable x y (signChange η σ) = observable x y σ := by
  change qPair _ _ = qPair _ _
  simp only [signChange]
  split_ifs <;> simp

end FiniteVolume


/-- Left multiplication by 1,i,j,k,-1,-i,-j,-k on real quaternion coordinates. -/
noncomputable def quaternionRotate (g : Fin 8) (u : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![![u 0, u 1, u 2, u 3],
    ![-u 1, u 0, -u 3, u 2],
    ![-u 2, u 3, u 0, -u 1],
    ![-u 3, -u 2, u 1, u 0],
    ![-u 0, -u 1, -u 2, -u 3],
    ![u 1, -u 0, u 3, -u 2],
    ![u 2, -u 3, -u 0, u 1],
    ![u 3, u 2, -u 1, -u 0]] g

theorem quaternionRotate_squares (g : Fin 8) (u : Fin 4 → ℝ) :
    ∑ i : Fin 4, quaternionRotate g u i ^ 2 = ∑ i : Fin 4, u i ^ 2 := by
  fin_cases g <;> simp [quaternionRotate, Fin.sum_univ_succ] <;> ring

theorem quaternion_cancellation (u v : Fin 4 → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1) :
    (∑ g : Fin 8, ((∑ i : Fin 4, quaternionRotate g u i * v i)^2 - (1 : ℝ)/4)) = 0 := by
  have hp : (∑ g : Fin 8, ((∑ i : Fin 4, quaternionRotate g u i * v i)^2 - (1 : ℝ)/4)) =
      2 * (∑ i : Fin 4, u i^2) * (∑ i : Fin 4, v i^2) - 2 := by
    simp [quaternionRotate, Fin.sum_univ_succ]
    ring
  rw [hp, hu, hv]
  norm_num

end RP3
