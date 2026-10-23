module

public import RP2.FourierAll

public section

/-! Polynomial moments of a superpolynomially decaying lattice function. -/
namespace RP2.Fourier
noncomputable section

private def displacementEquiv (x : Site) : Site ≃ (Fin 2 → ℤ) :=
  (Equiv.subRight x).trans (finTwoArrowEquiv ℤ).symm

private theorem displacement_norm (x y : Site) :
    ‖displacementEquiv x y‖ = (siteRadius x y : ℝ) := by
  simp [displacementEquiv, EisensteinSeries.norm_eq_max_natAbs, siteRadius,
    Nat.cast_max, Int.cast_max]

/-- The harmless `1 + r` at the origin gives a summable lattice envelope. -/
theorem summable_lattice_envelope (x : Site) :
    Summable (fun y : Site => (1 + (siteRadius x y : ℝ)) ^ (-(3:ℝ))) := by
  classical
  have hs : Summable (fun y : Site => (siteRadius x y : ℝ) ^ (-(3:ℝ))) := by
    have h := ((displacementEquiv x).summable_iff).2
      (EisensteinSeries.summable_one_div_norm_rpow (by norm_num : (2:ℝ)<3))
    simpa only [Function.comp_def, displacement_norm] using h
  have hz : Summable (fun y : Site => if y=x then (1:ℝ) else 0) :=
    (hasSum_ite_eq x (1:ℝ)).summable
  have hn (y : Site) : (0:ℝ) ≤ siteRadius x y := by
    exact_mod_cast siteRadius_nonneg x y
  apply (hs.add hz).of_nonneg_of_le
    (fun y => Real.rpow_nonneg (by have := hn y; positivity) _)
  intro y
  by_cases hy : y=x
  · subst y
    simp
  · have hd : displacementEquiv x y ≠ 0 := by
      intro h
      have hx : displacementEquiv x x = 0 := by
        ext i
        fin_cases i <;> simp [displacementEquiv]
      exact hy ((displacementEquiv x).injective (h.trans hx.symm))
    have hr : (0:ℝ) < siteRadius x y := by
      rw [← displacement_norm]
      exact norm_pos_iff.mpr hd
    simp only [hy, if_false, add_zero]
    exact Real.rpow_le_rpow_of_nonpos hr (by linarith) (by norm_num)

/-- Every polynomially weighted absolute moment is finite.  The hypothesis
is the usual real-exponent superpolynomial bound, with a constant for each
exponent.  The conclusion in fact holds for every real weight exponent. -/
theorem weighted_summable_of_decay (x : Site) (C : Site → ℝ)
    (hC : ∀ p : ℝ, ∃ A > 0, ∀ y,
      |C y| ≤ A * (1 + (siteRadius x y : ℝ)) ^ (-p)) (s : ℝ) :
    Summable (fun y : Site => (1 + (siteRadius x y : ℝ)) ^ s * |C y|) := by
  obtain ⟨A, hA, hbound⟩ := hC (s+3)
  have hn (y : Site) : (0:ℝ) ≤ siteRadius x y := by
    exact_mod_cast siteRadius_nonneg x y
  apply ((summable_lattice_envelope x).mul_left A).of_nonneg_of_le
    (fun y => mul_nonneg (Real.rpow_nonneg (by have := hn y; positivity) _) (abs_nonneg _))
  intro y
  have hr : (0:ℝ) < 1 + (siteRadius x y : ℝ) := by
    have := hn y
    positivity
  calc
    _ ≤ (1 + (siteRadius x y : ℝ)) ^ s *
        (A * (1 + (siteRadius x y : ℝ)) ^ (-(s+3))) :=
      mul_le_mul_of_nonneg_left (hbound y) (Real.rpow_nonneg hr.le _)
    _ = A * (1 + (siteRadius x y : ℝ)) ^ (-(3:ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hr]
      congr 2
      ring

end
end RP2.Fourier
