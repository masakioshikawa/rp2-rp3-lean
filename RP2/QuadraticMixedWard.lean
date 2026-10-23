import RP2.QuadraticMixedJets
import RP2.QuadraticSecondResponse
/-!
# Polarized fourth Ward identity for the squared RP² interaction
Adapted from OpenAI ClassicalON/MixedWard, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0, copyright OpenAI).
The model-specific coefficient identity is proved in QuadraticMixedJets.
-/
namespace RP2.Quadratic
universe uV uE
noncomputable section
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem planarGradient_eq (S : SpinSystem V E) (f g : V → ℝ) :
    S.planarGradient f g = fun e => planeOperator (S.edgeGradient f e) (S.edgeGradient g e) := by
  funext e
  simp only [planarGradient, planeOperator_eq]
  change (f (S.right e) • axisA + g (S.right e) • axisB) -
      (f (S.left e) • axisA + g (S.left e) • axisB) =
    (f (S.right e) - f (S.left e)) • axisA +
      (g (S.right e) - g (S.left e)) • axisB
  rw [sub_smul (f (S.right e)) (f (S.left e)) axisA,
    sub_smul (g (S.right e)) (g (S.left e)) axisB]
  abel

theorem mixedResponse_diagonal (S : SpinSystem V E) (f g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    2 * S.mixedResponse (S.edgeGradient f) (S.edgeGradient g)
      (S.edgeGradient f) (S.edgeGradient g) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm f g) := by
  have h := congrArg S.averageLinear
    (S.fourthObservable_even (S.edgeGradient f) (S.edgeGradient g))
  simp only [map_sub, map_add, map_smul, smul_eq_mul,
    average_fourthObservable] at h
  have hp := S.fourthResponse_plane_even f g hf hg
  have ha := S.fourthResponse_axisGradient axisA axisA_skew f hf
  have hb := S.fourthResponse_axisGradient axisB axisB_skew g hg
  rw [S.planarGradient_eq, S.planarGradient_eq] at hp
  have hm : S.edgeGradient (-g) = fun e => -S.edgeGradient g e := by
    funext e
    simp only [edgeGradient, Pi.neg_apply]
    ring
  rw [hm] at hp
  change S.fourthResponse (fun e => S.edgeGradient f e • axisA) = 0 at ha
  change S.fourthResponse (fun e => S.edgeGradient g e • axisB) = 0 at hb
  rw [ha, hb] at h
  unfold mixedResponse
  linarith

theorem mixedResponse_polarize_a (S : SpinSystem V E) (u w v : E → ℝ) :
    S.mixedResponse (u+w) v (u+w) v = S.mixedResponse u v u v +
      2 * S.mixedResponse u v w v + S.mixedResponse w v w v := by
  have hp : S.mixedObservable (u+w) v (u+w) v = S.mixedObservable u v u v +
      (2:ℝ) • S.mixedObservable u v w v + S.mixedObservable w v w v := by
    ext σ
    exact MixedAlgebra.four_polarize_a (S.mixedCoefficients σ) u w v
  unfold mixedResponse
  rw [hp, map_add, map_add, map_smul, smul_eq_mul]

theorem mixedResponse_polarize_b (S : SpinSystem V E) (u w v z : E → ℝ) :
    S.mixedResponse u (v+z) w (v+z) = S.mixedResponse u v w v +
      2 * S.mixedResponse u v w z + S.mixedResponse u z w z := by
  have hp : S.mixedObservable u (v+z) w (v+z) = S.mixedObservable u v w v +
      (2:ℝ) • S.mixedObservable u v w z + S.mixedObservable u z w z := by
    ext σ
    exact MixedAlgebra.four_polarize_b (S.mixedCoefficients σ) u w v z
  unfold mixedResponse
  rw [hp, map_add, map_add, map_smul, smul_eq_mul]

omit [Fintype V] [Fintype E] in
theorem edgeGradient_add (S : SpinSystem V E) (f g : V → ℝ) :
    S.edgeGradient (f+g) = S.edgeGradient f + S.edgeGradient g := by
  funext e
  simp only [edgeGradient, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem crossForm_add_left (S : SpinSystem V E) (f g h : V → ℝ) :
    S.crossForm (f+g) h = S.crossForm f h + S.crossForm g h := by
  funext e
  simp only [crossForm, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem crossForm_add_right (S : SpinSystem V E) (f g h : V → ℝ) :
    S.crossForm f (g+h) = S.crossForm f g + S.crossForm f h := by
  funext e
  simp only [crossForm, Pi.add_apply]
  ring

theorem mixedResponse_a_polarized (S : SpinSystem V E) (f h g : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0) :
    2 * S.mixedResponse (S.edgeGradient f) (S.edgeGradient g)
      (S.edgeGradient h) (S.edgeGradient g) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm h g) := by
  have hfh : ∀ x s, S.pin x = some s → (f+h) x = 0 := by
    intro x s hs
    simp only [Pi.add_apply, hf x s hs, hh x s hs, add_zero]
  have hp := S.mixedResponse_diagonal (f+h) g hfh hg
  rw [S.edgeGradient_add, S.mixedResponse_polarize_a, S.crossForm_add_left,
    S.secondAxisResponse_add_left, S.secondAxisResponse_add_right,
    S.secondAxisResponse_add_right, S.secondAxisResponse_symm (S.crossForm h g)] at hp
  have hdiagf := S.mixedResponse_diagonal f g hf hg
  have hdiagh := S.mixedResponse_diagonal h g hh hg
  linarith

theorem mixedResponse_ward (S : SpinSystem V E) (f g h k : V → ℝ)
    (hf : ∀ x s, S.pin x = some s → f x = 0)
    (hg : ∀ x s, S.pin x = some s → g x = 0)
    (hh : ∀ x s, S.pin x = some s → h x = 0)
    (hk : ∀ x s, S.pin x = some s → k x = 0) :
    4 * S.mixedResponse (S.edgeGradient f) (S.edgeGradient g)
      (S.edgeGradient h) (S.edgeGradient k) =
      S.secondAxisResponse (S.crossForm f g) (S.crossForm h k) +
        S.secondAxisResponse (S.crossForm f k) (S.crossForm h g) := by
  have hgk : ∀ x s, S.pin x = some s → (g+k) x = 0 := by
    intro x s hs
    simp only [Pi.add_apply, hg x s hs, hk x s hs, add_zero]
  have hp := S.mixedResponse_a_polarized f h (g+k) hf hh hgk
  rw [S.edgeGradient_add, S.mixedResponse_polarize_b, S.crossForm_add_right,
    S.crossForm_add_right, S.secondAxisResponse_add_left,
    S.secondAxisResponse_add_right, S.secondAxisResponse_add_right] at hp
  have hdiagg := S.mixedResponse_a_polarized f h g hf hh hg
  have hdiagk := S.mixedResponse_a_polarized f h k hf hh hk
  linarith


end SpinSystem
end
end RP2.Quadratic
