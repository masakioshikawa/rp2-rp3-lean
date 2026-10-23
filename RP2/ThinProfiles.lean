module

public import RP2.FourierAll

public section

/-! Balanced smooth profiles in arbitrarily thin square annuli.

The construction reuses the already verified fixed smooth profiles.  A signed
soft-threshold stretches their constant central plateau; this map is affine
where the profiles have nonzero derivatives.  Thus its apparent corners do not
introduce corners in the resulting cutoff functions.
-/

namespace RP2.Fourier
noncomputable section
open Set
open scoped ContDiff

/-- Signed soft threshold, with threshold `c ≥ 0`. -/
@[expose] def plateauMap (c x : ℝ) : ℝ :=
  if x ≤ -c then x+c else if c ≤ x then x-c else 0

theorem plateauMap_left (c x : ℝ) (h : x ≤ -c) : plateauMap c x = x+c := by
  simp [plateauMap, h]

theorem plateauMap_right (c x : ℝ) (hc : 0 ≤ c) (h : c ≤ x) :
    plateauMap c x = x-c := by
  by_cases hx : x ≤ -c
  · have : c = 0 := by linarith
    have : x = 0 := by linarith
    simp_all [plateauMap]
  · simp [plateauMap, hx, h]

theorem plateauMap_middle (c x : ℝ) (h1 : -c ≤ x) (h2 : x ≤ c) :
    plateauMap c x = 0 := by
  unfold plateauMap
  split_ifs <;> linarith

theorem plateauMap_lipschitz (c : ℝ) (hc : 0 ≤ c) (x y : ℝ) :
    |plateauMap c y-plateauMap c x| ≤ |y-x| := by
  have hab := abs_le.mp (le_refl |y-x|)
  unfold plateauMap
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith [abs_nonneg (y-x)]

theorem plateauMap_abs_le (c : ℝ) (hc : 0 ≤ c) (x : ℝ) :
    |plateauMap c x| ≤ |x| := by
  have h := plateauMap_lipschitz c hc 0 x
  simpa [plateauMap_middle c 0 (by linarith) hc] using h

theorem plateauMap_inner (c d x : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : |x| ≤ c+d) : |plateauMap c x| ≤ d := by
  have hx' := abs_le.mp hx
  unfold plateauMap
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

theorem plateauMap_outer (c d x : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : c+d ≤ |x|) : d ≤ |plateauMap c x| := by
  by_cases hxp : 0 ≤ x
  · rw [abs_of_nonneg hxp] at hx
    rw [plateauMap_right c x hc (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos (by linarith)] at hx
    rw [plateauMap_left c x (by linarith), abs_of_nonpos (by linarith)]
    linarith

/-- A short interval either sees the same affine branch or remains entirely in
    the region where every fixed cutoff is constant in this coordinate. -/
theorem plateauMap_step_alternative (c d x y : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hxy : |y-x| ≤ d) :
    plateauMap c y-plateauMap c x = y-x ∨
      (|plateauMap c x| ≤ d ∧ |plateauMap c y| ≤ d) := by
  have hxy' := abs_le.mp hxy
  unfold plateauMap
  split_ifs <;> first
    | (left; ring1)
    | right; constructor <;> rw [abs_le] <;> constructor <;> linarith

/-- Rescaled plateau map. -/
@[expose] def thinCoord (a δ x : ℝ) : ℝ := plateauMap (a-δ) x / δ

@[expose] def thinMap (a δ : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (thinCoord a δ z.1, thinCoord a δ z.2)

@[expose] def thinProfile (a δ : ℝ) (m s : Bool) (z : ℝ × ℝ) : ℝ :=
  squareProfile m s (thinMap a δ z) / Real.sqrt δ

@[expose] def thinTheta (a δ : ℝ) (z : ℝ × ℝ) : ℝ :=
  squareTheta (thinMap a δ z)

theorem thinCoord_lipschitz (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a) (x y : ℝ) :
    |thinCoord a δ y-thinCoord a δ x| ≤ |y-x|/δ := by
  simp only [thinCoord, ← sub_div, abs_div, abs_of_pos hδ]
  exact div_le_div_of_nonneg_right (plateauMap_lipschitz (a-δ) (sub_nonneg.mpr ha) x y) hδ.le

theorem thinMap_lipschitz (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a) (z w : ℝ × ℝ) :
    ‖thinMap a δ w-thinMap a δ z‖ ≤ ‖w-z‖/δ := by
  simp only [thinMap, Prod.mk_sub_mk, Prod.norm_def, Real.norm_eq_abs]
  apply max_le
  · exact (thinCoord_lipschitz a δ hδ ha z.1 w.1).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hδ.le)
  · exact (thinCoord_lipschitz a δ hδ ha z.2 w.2).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hδ.le)

theorem thinCoord_inner (a δ x : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (hx : |x| ≤ a) : |thinCoord a δ x| ≤ 1 := by
  rw [thinCoord, abs_div, abs_of_pos hδ, div_le_one hδ]
  apply plateauMap_inner (a-δ) δ x (sub_nonneg.mpr ha) hδ.le
  linarith

theorem thinCoord_outer (a δ x : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (hx : a+δ ≤ |x|) : 2 ≤ |thinCoord a δ x| := by
  rw [thinCoord, abs_div, abs_of_pos hδ, le_div_iff₀ hδ]
  apply plateauMap_outer (a-δ) (2*δ) x (sub_nonneg.mpr ha) (by positivity)
  linarith

theorem thinProfile_zero_inner (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (m s : Bool) (z : ℝ × ℝ) (hx : |z.1| ≤ a) (hy : |z.2| ≤ a) :
    thinProfile a δ m s z = 0 := by
  unfold thinProfile
  rw [squareProfile_zero_inner m s (thinMap a δ z)
    (thinCoord_inner a δ z.1 hδ ha hx) (thinCoord_inner a δ z.2 hδ ha hy), zero_div]

theorem thinProfile_zero_outer (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (m s : Bool) (z : ℝ × ℝ) (hz : a+δ ≤ |z.1| ∨ a+δ ≤ |z.2|) :
    thinProfile a δ m s z = 0 := by
  unfold thinProfile
  rw [squareProfile_zero_outer m s (thinMap a δ z) ?_, zero_div]
  rcases hz with h | h
  · exact Or.inl (thinCoord_outer a δ z.1 hδ ha h)
  · exact Or.inr (thinCoord_outer a δ z.2 hδ ha h)

theorem thinTheta_one (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (z : ℝ × ℝ) (hx : |z.1| ≤ a) (hy : |z.2| ≤ a) :
    thinTheta a δ z = 1 := by
  exact squareTheta_one (thinMap a δ z)
    (thinCoord_inner a δ z.1 hδ ha hx) (thinCoord_inner a δ z.2 hδ ha hy)

theorem thinTheta_zero (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (z : ℝ × ℝ) (hz : a+δ ≤ |z.1| ∨ a+δ ≤ |z.2|) :
    thinTheta a δ z = 0 := by
  apply squareTheta_zero
  rcases hz with h | h
  · exact Or.inl (thinCoord_outer a δ z.1 hδ ha h)
  · exact Or.inr (thinCoord_outer a δ z.2 hδ ha h)

theorem thinProfile_uniform_bounds : ∃ P : ℝ, 1 ≤ P ∧
    ∀ (a δ : ℝ), 0 < δ → δ ≤ a →
      (∀ m s z, |thinProfile a δ m s z| ≤ P/Real.sqrt δ) ∧
      (∀ m s z w, |thinProfile a δ m s w-thinProfile a δ m s z| ≤
        (P/(δ*Real.sqrt δ))*‖w-z‖) := by
  obtain ⟨P,hP,hv,hL⟩ := profiles_uniform_bound
  refine ⟨P,hP,?_⟩
  intro a δ hδ ha
  have hs : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
  constructor
  · intro m s z
    rw [thinProfile, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (hv m s (thinMap a δ z)) hs.le
  · intro m s z w
    simp only [thinProfile, ← sub_div, abs_div, abs_of_pos hs]
    calc
      _ ≤ (P*‖thinMap a δ w-thinMap a δ z‖)/Real.sqrt δ :=
        div_le_div_of_nonneg_right (hL m s (thinMap a δ z) (thinMap a δ w)) hs.le
      _ ≤ (P*(‖w-z‖/δ))/Real.sqrt δ := by
        gcongr
        exact thinMap_lipschitz a δ hδ ha z w
      _ = _ := by ring

theorem thinTheta_lipschitz_bound : ∃ L : ℝ, 0 ≤ L ∧
    ∀ (a δ : ℝ), 0 < δ → δ ≤ a → ∀ z w,
      |thinTheta a δ w-thinTheta a δ z| ≤ (L/δ)*‖w-z‖ := by
  obtain ⟨L,hL,h⟩ := theta_lipschitz_bound
  refine ⟨L,hL,?_⟩
  intro a δ hδ ha z w
  calc
    _ ≤ L*‖thinMap a δ w-thinMap a δ z‖ := h _ _
    _ ≤ L*(‖w-z‖/δ) := mul_le_mul_of_nonneg_left (thinMap_lipschitz a δ hδ ha z w) hL
    _ = _ := by ring

/-- The coordinate changed by a square-lattice step. -/
@[expose] def stepCoordinate (m : Bool) (z : ℝ × ℝ) : ℝ := if m then z.2 else z.1

@[expose] def thinIncrement (a δ : ℝ) (m : Bool) (ε : ℝ) (z : ℝ × ℝ) : ℝ :=
  thinCoord a δ (stepCoordinate m z+ε)-thinCoord a δ (stepCoordinate m z)

theorem thinMap_squareStep (a δ : ℝ) (m : Bool) (ε : ℝ) (z : ℝ × ℝ) :
    thinMap a δ (squareStep m ε z) =
      squareStep m (thinIncrement a δ m ε z) (thinMap a δ z) := by
  cases m <;> simp [thinMap, squareStep, thinIncrement, stepCoordinate]

theorem thinIncrement_bound (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (m : Bool) (ε : ℝ) (z : ℝ × ℝ) :
    |thinIncrement a δ m ε z| ≤ |ε|/δ := by
  simpa only [thinIncrement, add_sub_cancel_left] using
    thinCoord_lipschitz a δ hδ ha (stepCoordinate m z) (stepCoordinate m z+ε)

theorem thinIncrement_alternative (a δ : ℝ) (hδ : 0 < δ) (ha : δ ≤ a)
    (m : Bool) (ε : ℝ) (z : ℝ × ℝ) (hε : |ε| ≤ δ/16) :
    thinIncrement a δ m ε z = ε/δ ∨
      (|thinCoord a δ (stepCoordinate m z)| ≤ 1/16 ∧
        |thinCoord a δ (stepCoordinate m z+ε)| ≤ 1/16) := by
  have hh := plateauMap_step_alternative (a-δ) (δ/16)
    (stepCoordinate m z) (stepCoordinate m z+ε) (sub_nonneg.mpr ha)
    (by positivity) (by simpa only [add_sub_cancel_left] using hε)
  rcases hh with hh | ⟨hx,hy⟩
  · left
    simp only [thinIncrement, thinCoord, ←sub_div, hh, add_sub_cancel_left]
  · right
    constructor
    · rw [thinCoord, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
      linarith
    · rw [thinCoord, abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
      linarith

theorem thinProfile_product_scale (a δ : ℝ) (hδ : 0 < δ)
    (m : Bool) (z w : ℝ × ℝ) :
    thinProfile a δ m false z*thinProfile a δ m false w-
      thinProfile a δ m true z*thinProfile a δ m true w =
    (squareProfile m false (thinMap a δ z)*squareProfile m false (thinMap a δ w)-
      squareProfile m true (thinMap a δ z)*squareProfile m true (thinMap a δ w))/δ := by
  simp only [thinProfile, div_mul_div_comm, ←sub_div, ←pow_two, Real.sq_sqrt hδ.le]

theorem squareGradient_zero_of_stepCoordinate (m : Bool) (z : ℝ × ℝ)
    (h : |stepCoordinate m z| ≤ 4/3) : squareGradient m z = 0 := by
  cases m
  · have hh : |z.1| ≤ 4/3 := h
    simp [squareGradient, thetaBump_deriv_zero_inner hh]
  · have hh : |z.2| ≤ 4/3 := h
    simp [squareGradient, thetaBump_deriv_zero_inner hh]

theorem thinTheta_step_error : ∃ D : ℝ, 0 ≤ D ∧
    ∀ (a δ : ℝ), 0 < δ → δ ≤ a → ∀ (m : Bool) (z : ℝ × ℝ) (ε : ℝ),
    |ε| ≤ δ/16 →
    |thinTheta a δ (squareStep m ε z)-thinTheta a δ z-
      ε*(thinProfile a δ m false z*thinProfile a δ m false (squareStep m ε z)-
         thinProfile a δ m true z*thinProfile a δ m true (squareStep m ε z))| ≤
      (D/δ^3)*|ε|^3 := by
  obtain ⟨D,hD,hR⟩ := squareTheta_step_error
  refine ⟨D,hD,?_⟩
  intro a δ hδ ha m z ε hε
  let η := thinIncrement a δ m ε z
  let v := thinMap a δ z
  let w := thinMap a δ (squareStep m ε z)
  have hη : |η| ≤ |ε|/δ := thinIncrement_bound a δ hδ ha m ε z
  have hsmall : |η| ≤ 1/16 := hη.trans ((div_le_iff₀ hδ).mpr (by linarith))
  have hw : w = squareStep m η v := thinMap_squareStep a δ m ε z
  have hprod := squareProfile_product_difference m v w
    (by rw [hw]; cases m <;> simpa [squareStep] using hsmall)
    (by rw [hw]; cases m <;> simpa [squareStep] using hsmall)
  let F := squareProfile m false v*squareProfile m false w-
    squareProfile m true v*squareProfile m true w
  have hcoef : η*F = (ε/δ)*F := by
    rcases thinIncrement_alternative a δ hδ ha m ε z hε with heq | ⟨hx,hy⟩
    · rw [show η = ε/δ from heq]
    · have hv0 : squareGradient m v = 0 := by
        apply squareGradient_zero_of_stepCoordinate
        have heq : stepCoordinate m v = thinCoord a δ (stepCoordinate m z) := by
          cases m <;> rfl
        rw [heq]
        linarith
      have hw0 : squareGradient m w = 0 := by
        apply squareGradient_zero_of_stepCoordinate
        have heq : stepCoordinate m w = thinCoord a δ (stepCoordinate m z+ε) := by
          cases m <;> rfl
        rw [heq]
        linarith
      have hF : F = 0 := by dsimp only [F]; rw [hprod,hv0,hw0]; ring
      rw [hF]; ring
  have h := hR m v η hsmall
  rw [←hw] at h
  change |squareTheta w-squareTheta v-η*F| ≤ D*|η|^3 at h
  rw [hcoef] at h
  rw [thinProfile_product_scale a δ hδ m z (squareStep m ε z)]
  change |squareTheta w-squareTheta v-ε*(F/δ)| ≤ _
  calc
    _ = |squareTheta w-squareTheta v-(ε/δ)*F| := by congr 1; ring
    _ ≤ D*|η|^3 := h
    _ ≤ D*(|ε|/δ)^3 := by gcongr
    _ = _ := by ring

end
end RP2.Fourier
