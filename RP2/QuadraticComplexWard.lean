import RP2.QuadraticMixedWard
/-!
# Complex polarization of the quadratic fourth Ward identity
Adapted from OpenAI ClassicalON/ComplexWard, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
-/
namespace RP2.Quadratic
universe uV uE
noncomputable section
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]
def complexCoefficients (S : SpinSystem V E) (σ : V → RP2.Spin) : MixedAlgebra.Coeffs E ℂ :=
  (S.mixedCoefficients σ).map Complex.ofRealHom

omit [Fintype V] in
@[fun_prop] theorem continuous_complexMixedPolynomial (S : SpinSystem V E)
    (u v w z : E → ℂ) :
    Continuous (fun σ => MixedAlgebra.four (S.complexCoefficients σ) u v w z) := by
  simp only [MixedAlgebra.four, complexCoefficients, MixedAlgebra.Coeffs.map,
    mixedCoefficients, Function.comp_def, Complex.ofRealHom_eq_coe]
  unfold MixedAlgebra.weighted localInner
  fun_prop

def complexMixedObservable (S : SpinSystem V E) (u v w z : E → ℂ) : C((V → RP2.Spin), ℂ) :=
  ⟨_, S.continuous_complexMixedPolynomial u v w z⟩

def complexMixedResponse (S : SpinSystem V E) (u v w z : E → ℂ) : ℂ :=
  S.averageComplexLinear (S.complexMixedObservable u v w z)

theorem complexMixedResponse_ofReal (S : SpinSystem V E) (u v w z : E → ℝ) :
    S.complexMixedResponse (fun e => (u e : ℂ)) (fun e => (v e : ℂ))
      (fun e => (w e : ℂ)) (fun e => (z e : ℂ)) = (S.mixedResponse u v w z : ℂ) := by
  have hc : S.complexMixedObservable (fun e => (u e : ℂ)) (fun e => (v e : ℂ))
      (fun e => (w e : ℂ)) (fun e => (z e : ℂ)) = ofRealObservable (S.mixedObservable u v w z) := by
    ext σ
    exact MixedAlgebra.four_map Complex.ofRealHom (S.mixedCoefficients σ) u v w z
  unfold complexMixedResponse
  rw [hc, S.averageComplex_ofReal]
  rfl

theorem complexMixedResponse_add_first (S : SpinSystem V E) (u v w z u' : E → ℂ) :
    S.complexMixedResponse (u+u') v w z = S.complexMixedResponse u v w z + S.complexMixedResponse u' v w z := by
  have hp : S.complexMixedObservable (u+u') v w z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u' v w z := by
    ext σ
    exact MixedAlgebra.four_add_first (S.complexCoefficients σ) u u' v w z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_first (S : SpinSystem V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse (r • u) v w z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable (r • u) v w z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_first (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_second (S : SpinSystem V E) (u v w z v' : E → ℂ) :
    S.complexMixedResponse u (v+v') w z = S.complexMixedResponse u v w z + S.complexMixedResponse u v' w z := by
  have hp : S.complexMixedObservable u (v+v') w z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v' w z := by
    ext σ
    exact MixedAlgebra.four_add_second (S.complexCoefficients σ) u v v' w z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_second (S : SpinSystem V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u (r • v) w z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u (r • v) w z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_second (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_third (S : SpinSystem V E) (u v w z w' : E → ℂ) :
    S.complexMixedResponse u v (w+w') z = S.complexMixedResponse u v w z + S.complexMixedResponse u v w' z := by
  have hp : S.complexMixedObservable u v (w+w') z = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v w' z := by
    ext σ
    exact MixedAlgebra.four_add_third (S.complexCoefficients σ) u v w w' z
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_third (S : SpinSystem V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u v (r • w) z = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u v (r • w) z = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_third (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexMixedResponse_add_fourth (S : SpinSystem V E) (u v w z z' : E → ℂ) :
    S.complexMixedResponse u v w (z+z') = S.complexMixedResponse u v w z + S.complexMixedResponse u v w z' := by
  have hp : S.complexMixedObservable u v w (z+z') = S.complexMixedObservable u v w z +
      S.complexMixedObservable u v w z' := by
    ext σ
    exact MixedAlgebra.four_add_fourth (S.complexCoefficients σ) u v w z z'
  unfold complexMixedResponse
  rw [hp, map_add]

theorem complexMixedResponse_smul_fourth (S : SpinSystem V E) (u v w z : E → ℂ) (r : ℂ) :
    S.complexMixedResponse u v w (r • z) = r * S.complexMixedResponse u v w z := by
  have hp : S.complexMixedObservable u v w (r • z) = r • S.complexMixedObservable u v w z := by
    ext σ
    exact MixedAlgebra.four_smul_fourth (S.complexCoefficients σ) u v w z r
  unfold complexMixedResponse
  rw [hp, map_smul, smul_eq_mul]

def complexWardDefect (S : SpinSystem V E) : ComplexFourForm (V → ℂ) where
  toFun f g h k := 4 * S.complexMixedResponse (S.edgeGradient f) (S.edgeGradient g)
    (S.edgeGradient h) (S.edgeGradient k) -
    (S.complexSecondResponse (S.complexCross f g) (S.complexCross h k) +
      S.complexSecondResponse (S.complexCross f k) (S.complexCross h g))
  add_first := by
    intro f f' g h k
    simp only [complexDifferential_add, complexMixedResponse_add_first,
      complexCross_add_left, complexSecondResponse_add_left]
    ring
  add_second := by
    intro f g g' h k
    simp only [complexDifferential_add, complexMixedResponse_add_second,
      complexCross_add_right, complexSecondResponse_add_left, complexSecondResponse_add_right]
    ring
  add_third := by
    intro f g h h' k
    simp only [complexDifferential_add, complexMixedResponse_add_third,
      complexCross_add_left, complexSecondResponse_add_right]
    ring
  add_fourth := by
    intro f g h k k'
    simp only [complexDifferential_add, complexMixedResponse_add_fourth,
      complexCross_add_right, complexSecondResponse_add_left, complexSecondResponse_add_right]
    ring
  smul_first := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_first,
      complexCross_smul_left, complexSecondResponse_smul_left]
    ring
  smul_second := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_second,
      complexCross_smul_right, complexSecondResponse_smul_left, complexSecondResponse_smul_right]
    ring
  smul_third := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_third,
      complexCross_smul_left, complexSecondResponse_smul_right]
    ring
  smul_fourth := by
    intro r f g h k
    simp only [complexDifferential_smul, complexMixedResponse_smul_fourth,
      complexCross_smul_right, complexSecondResponse_smul_left, complexSecondResponse_smul_right]
    ring

theorem complexWardDefect_real (S : SpinSystem V E) (f g h k : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    S.complexWardDefect (fun x => (f x : ℂ)) (fun x => (g x : ℂ))
      (fun x => (h x : ℂ)) (fun x => (k x : ℂ)) = 0 := by
  change _ - _ = 0
  apply sub_eq_zero.mpr
  simp only [edgeGradient_ofReal, complexCross_ofReal, complexMixedResponse_ofReal,
    complexSecondResponse_ofReal]
  exact_mod_cast S.mixedResponse_ward f g h k hf hg hh hk

theorem complexMixedResponse_ward (S : SpinSystem V E) (f g h k : V → ℂ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    4 * S.complexMixedResponse (S.edgeGradient f) (S.edgeGradient g)
      (S.edgeGradient h) (S.edgeGradient k) =
      S.complexSecondResponse (S.complexCross f g) (S.complexCross h k) +
        S.complexSecondResponse (S.complexCross f k) (S.complexCross h g) := by
  apply sub_eq_zero.mp
  change S.complexWardDefect f g h k = 0
  refine S.complexWardDefect.zero_of_real (fun x => ∃ s, S.pin x = some s) ?_ f g h k ?_ ?_ ?_ ?_
  · intro a b c d ha hb hc hd
    exact S.complexWardDefect_real a b c d
      (fun x s hs => ha x ⟨s, hs⟩) (fun x s hs => hb x ⟨s, hs⟩)
      (fun x s hs => hc x ⟨s, hs⟩) (fun x s hs => hd x ⟨s, hs⟩)
  · rintro x ⟨s, hs⟩; exact hf x s hs
  · rintro x ⟨s, hs⟩; exact hg x s hs
  · rintro x ⟨s, hs⟩; exact hh x s hs
  · rintro x ⟨s, hs⟩; exact hk x s hs


end SpinSystem
end
end RP2.Quadratic
