module

public import RP2.FiniteAveraging

public section

/-!
# The finite-volume RP² model and its quadrupolar observable

Spins are unit vectors, and the interaction and observable are invariant under
independent changes of sign.  Thus they descend to director spins without
choosing a global lift.  No decay theorem is assumed in this module.
-/

namespace RP2

open MeasureTheory
open scoped BigOperators InnerProductSpace

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Spin := Metric.sphere (0 : E3) 1

@[simp] theorem spin_norm (s : Spin) : ‖s.val‖ = 1 :=
  mem_sphere_zero_iff_norm.mp s.property

@[expose] noncomputable def antipode (s : Spin) : Spin :=
  ⟨-s.val, mem_sphere_zero_iff_norm.mpr (by simp)⟩

@[expose] noncomputable def qPair (s t : Spin) : ℝ :=
  ⟪s.val, t.val⟫_ℝ ^ 2 - 1 / 3

/-- The quadrupolar observable is a function of directors. -/
@[simp] theorem qPair_antipode_left (s t : Spin) : qPair (antipode s) t = qPair s t := by
  simp [qPair, antipode]

@[simp] theorem qPair_antipode_right (s t : Spin) : qPair s (antipode t) = qPair s t := by
  simp [qPair, antipode]

/-- This normalisation is `Tr (Q(s) Q(t))`, not the Legendre `P₂` normalisation. -/
theorem abs_qPair_le (s t : Spin) : |qPair s t| ≤ (2 : ℝ) / 3 := by
  have h := abs_real_inner_le_norm s.val t.val
  simp only [spin_norm, one_mul] at h
  have hs : ⟪s.val, t.val⟫_ℝ ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).mpr h
  rw [qPair, abs_le]
  constructor <;> nlinarith [sq_nonneg ⟪s.val, t.val⟫_ℝ]

@[expose] noncomputable def Q (s : Spin) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => s.val i * s.val j - if i = j then 1 / 3 else 0

theorem spin_squares (s : Spin) : ∑ i : Fin 3, s.val i ^ 2 = 1 := by
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
@[expose] noncomputable def sphereProbability : Measure Spin :=
  ((volume : Measure E3).toSphere Set.univ)⁻¹ • (volume : Measure E3).toSphere

@[expose] instance sphereProbability_isProbability : IsProbabilityMeasure sphereProbability := by
  have hs : (volume : Measure E3).toSphere ≠ 0 := Measure.toSphere_ne_zero _
  constructor
  dsimp [sphereProbability]
  exact ENNReal.inv_mul_cancel (Measure.measure_univ_eq_zero.not.mpr hs)
    (measure_ne_top _ _)

section FiniteVolume

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev Configuration (V : Type*) := V → Spin

@[expose] noncomputable def referenceLaw : Measure (Configuration V) :=
  Measure.pi (fun _ => sphereProbability)

@[expose] instance referenceLaw_isProbability : IsProbabilityMeasure (referenceLaw (V := V)) := by
  unfold referenceLaw
  infer_instance

/-- General finite graph with oriented representatives of its unoriented edges.
The square-lattice geometry is needed later, when annuli are constructed. -/
@[expose] noncomputable def interaction (edge : E → V × V) (b : E → ℝ)
    (σ : Configuration V) : ℝ :=
  ∑ e, b e * ⟪(σ (edge e).1).val, (σ (edge e).2).val⟫_ℝ ^ 2

@[expose] noncomputable def weight (edge : E → V × V) (b : E → ℝ) : C(Configuration V, ℝ) :=
  ⟨fun σ => Real.exp (interaction edge b σ), by unfold interaction; fun_prop⟩

@[expose] noncomputable def observable (x y : V) : C(Configuration V, ℝ) :=
  ⟨fun σ => qPair (σ x) (σ y), by unfold qPair; fun_prop⟩

@[expose] noncomputable def partition (edge : E → V × V) (b : E → ℝ) : ℝ :=
  (integralOnCompact (referenceLaw (V := V))).linear (weight edge b)

@[expose] noncomputable def correlation (edge : E → V × V) (b : E → ℝ) (x y : V) : ℝ :=
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
    |correlation edge b x y| ≤ (2 : ℝ) / 3 := by
  have hb := (integralOnCompact (referenceLaw (V := V))).abs_weighted_le
    (observable x y) (weight edge b)
    (fun σ => abs_qPair_le (σ x) (σ y)) (fun σ => (Real.exp_pos _).le)
  unfold correlation
  rw [abs_div, abs_of_pos (partition_pos edge b)]
  exact (div_le_iff₀ (partition_pos edge b)).mpr hb

@[expose] noncomputable def signChange (η : V → Bool) (σ : Configuration V) : Configuration V :=
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

/-! A finite cancellation certificate. The twelve displayed transformations
are the orientation-preserving signed cyclic permutations (tetrahedral rotations).
The following polynomial identity verifies cancellation directly; no Haar
integration is needed to annihilate this observable. -/

@[expose] noncomputable def cyclic (a : Fin 3) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![![u 0, u 1, u 2], ![u 1, u 2, u 0], ![u 2, u 0, u 1]] a

@[expose] noncomputable def evenSigns (b : Fin 4) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![![u 0, u 1, u 2], ![u 0, -u 1, -u 2],
    ![-u 0, u 1, -u 2], ![-u 0, -u 1, u 2]] b

@[expose] noncomputable def tetraRotate (a : Fin 3) (b : Fin 4) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  evenSigns b (cyclic a u)

/-- Every displayed finite transformation preserves the sphere. -/
theorem tetraRotate_squares (a : Fin 3) (b : Fin 4) (u : Fin 3 → ℝ) :
    ∑ i : Fin 3, tetraRotate a b u i ^ 2 = ∑ i : Fin 3, u i ^ 2 := by
  fin_cases a <;> fin_cases b <;>
    simp [tetraRotate, evenSigns, cyclic, Fin.sum_univ_succ] <;> ring

theorem tetrahedral_cancellation (u v : Fin 3 → ℝ)
    (hu : ∑ i, u i ^ 2 = 1) (hv : ∑ i, v i ^ 2 = 1) :
    (∑ a : Fin 3, ∑ b : Fin 4,
      ((∑ i : Fin 3, tetraRotate a b u i * v i) ^ 2 - (1 : ℝ) / 3)) = 0 := by
  have hpoly : (∑ a : Fin 3, ∑ b : Fin 4,
      ((∑ i : Fin 3, tetraRotate a b u i * v i) ^ 2 - (1 : ℝ) / 3)) =
      4 * (∑ i : Fin 3, u i ^ 2) * (∑ i : Fin 3, v i ^ 2) - 4 := by
    simp [tetraRotate, evenSigns, cyclic, Fin.sum_univ_succ]
    ring
  rw [hpoly, hu, hv]
  norm_num

end RP2
