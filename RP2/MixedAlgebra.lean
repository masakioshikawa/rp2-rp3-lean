module

public import Mathlib

public section
/-!
# Fourth-order polarization and finite-family algebra

Adapted from OpenAI's ClassicalON RotationWork, MixedWard, ComplexWard, and
FamilyAlgebra at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Copyright OpenAI; Apache-2.0. All statements here are generic commutative-ring
identities; no spin-model hypotheses enter them.
-/
namespace RP2.Quadratic
universe uA uE uI uJ uK uL uV
noncomputable section
open scoped BigOperators ComplexConjugate
namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

@[expose] def weighted (J u : E → K) : K := ∑ e, J e * u e

@[simp] theorem weighted_add (J u v : E → K) :
    weighted J (u+v) = weighted J u + weighted J v := by
  simp [weighted, mul_add, Finset.sum_add_distrib]

@[simp] theorem weighted_neg (J u : E → K) : weighted J (-u) = -weighted J u := by
  simp [weighted]

structure Coeffs (E : Type uE) (K : Type uK) where
  a : E → K
  b : E → K
  aa : E → K
  ab : E → K
  bb : E → K
  aab : E → K
  abb : E → K
  aabb : E → K

inductive Slot where
  | a | b | aa | ab | bb | aab | abb | aabb

@[expose] def Coeffs.get (J : Coeffs E K) : Slot → E → K
  | .a => J.a
  | .b => J.b
  | .aa => J.aa
  | .ab => J.ab
  | .bb => J.bb
  | .aab => J.aab
  | .abb => J.abb
  | .aabb => J.aabb

@[expose] def four (J : Coeffs E K) (u v w z : E → K) : K :=
  weighted J.a u * weighted J.b v * weighted J.a w * weighted J.b z +
  weighted J.ab (u*v) * weighted J.a w * weighted J.b z +
  weighted J.aa (u*w) * weighted J.b v * weighted J.b z +
  weighted J.ab (u*z) * weighted J.b v * weighted J.a w +
  weighted J.ab (v*w) * weighted J.a u * weighted J.b z +
  weighted J.bb (v*z) * weighted J.a u * weighted J.a w +
  weighted J.ab (w*z) * weighted J.a u * weighted J.b v +
  weighted J.ab (u*v) * weighted J.ab (w*z) +
  weighted J.aa (u*w) * weighted J.bb (v*z) +
  weighted J.ab (u*z) * weighted J.ab (v*w) +
  weighted J.aab (u*v*w) * weighted J.b z +
  weighted J.abb (u*v*z) * weighted J.a w +
  weighted J.aab (u*w*z) * weighted J.b v +
  weighted J.abb (v*w*z) * weighted J.a u +
  weighted J.aabb (u*v*w*z)

theorem four_add_first (J : Coeffs E K) (u u' v w z : E → K) :
    four J (u+u') v w z = four J u v w z + four J u' v w z := by
  simp only [four, add_mul, weighted_add]
  ring

theorem four_add_second (J : Coeffs E K) (u v v' w z : E → K) :
    four J u (v+v') w z = four J u v w z + four J u v' w z := by
  simp only [four, add_mul, mul_add, weighted_add]
  ring

theorem four_swap_first_third (J : Coeffs E K) (u v w z : E → K) :
    four J u v w z = four J w v u z := by
  unfold four
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

theorem four_swap_second_fourth (J : Coeffs E K) (u v w z : E → K) :
    four J u v w z = four J u z w v := by
  unfold four
  simp only [mul_comm, mul_left_comm, mul_assoc]
  ring

end MixedAlgebra

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_add_third (J : Coeffs E K) (u v w w' z : E → K) :
    four J u v (w+w') z = four J u v w z + four J u v w' z := by
  rw [four_swap_first_third, four_add_first, four_swap_first_third J w,
    four_swap_first_third J w']

theorem four_add_fourth (J : Coeffs E K) (u v w z z' : E → K) :
    four J u v w (z+z') = four J u v w z + four J u v w z' := by
  rw [four_swap_second_fourth, four_add_second, four_swap_second_fourth J u z,
    four_swap_second_fourth J u z']

theorem four_polarize_a (J : Coeffs E K) (u w v : E → K) :
    four J (u+w) v (u+w) v = four J u v u v + 2 * four J u v w v + four J w v w v := by
  rw [four_add_first, four_add_third, four_add_third, four_swap_first_third J w v u]
  ring

theorem four_polarize_b (J : Coeffs E K) (u w v z : E → K) :
    four J u (v+z) w (v+z) = four J u v w v + 2 * four J u v w z + four J u z w z := by
  rw [four_add_second, four_add_fourth, four_add_fourth, four_swap_second_fourth J u z w v]
  ring

end MixedAlgebra

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]

theorem four_diagonal (J : Coeffs E K) (u v : E → K) :
    four J u v u v =
      (weighted J.a u)^2 * (weighted J.b v)^2 +
      weighted J.aa (u*u) * (weighted J.b v)^2 +
      weighted J.bb (v*v) * (weighted J.a u)^2 +
      4 * weighted J.ab (u*v) * weighted J.a u * weighted J.b v +
      weighted J.aa (u*u) * weighted J.bb (v*v) +
      2 * (weighted J.ab (u*v))^2 +
      2 * weighted J.aab (u*u*v) * weighted J.b v +
      2 * weighted J.abb (u*v*v) * weighted J.a u +
      weighted J.aabb (u*u*v*v) := by
  simp only [four, mul_comm, mul_left_comm]
  ring

end MixedAlgebra

@[expose] def bell4 (x y z w : ℝ) : ℝ := w+4*x*z+3*y^2+6*x^2*y+x^4

theorem bell4_even (a b aa ab bb aaa aab abb bbb p q aaaa aabb bbbb : ℝ)
    (h : p+q = 2*aaaa+12*aabb+2*bbbb) :
    bell4 (a+b) (aa+2*ab+bb) (aaa+3*aab+3*abb+bbb) p +
      bell4 (a-b) (aa-2*ab+bb) (aaa-3*aab+3*abb-bbb) q -
      2*bell4 a aa aaa aaaa - 2*bell4 b bb bbb bbbb =
      12*(a^2*b^2+aa*b^2+bb*a^2+4*ab*a*b+aa*bb+2*ab^2+
        2*aab*b+2*abb*a+aabb) := by
  unfold bell4
  nlinarith only [h]


namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} [Fintype E] [CommRing K]
theorem weighted_const_mul (J u : E → K) (r : K) :
    weighted J (fun e => r * u e) = r * weighted J u := by
  simp only [weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring
end MixedAlgebra

structure ComplexFourForm (A : Type uA) [AddCommMonoid A] [Module ℂ A] where
  toFun : A → A → A → A → ℂ
  add_first : ∀ u u' v w z, toFun (u+u') v w z = toFun u v w z + toFun u' v w z
  add_second : ∀ u v v' w z, toFun u (v+v') w z = toFun u v w z + toFun u v' w z
  add_third : ∀ u v w w' z, toFun u v (w+w') z = toFun u v w z + toFun u v w' z
  add_fourth : ∀ u v w z z', toFun u v w (z+z') = toFun u v w z + toFun u v w z'
  smul_first : ∀ r u v w z, toFun (r • u) v w z = r * toFun u v w z
  smul_second : ∀ r u v w z, toFun u (r • v) w z = r * toFun u v w z
  smul_third : ∀ r u v w z, toFun u v (r • w) z = r * toFun u v w z
  smul_fourth : ∀ r u v w z, toFun u v w (r • z) = r * toFun u v w z

@[expose] instance {A : Type uA} [AddCommMonoid A] [Module ℂ A] :
    CoeFun (ComplexFourForm A) (fun _ => A → A → A → A → ℂ) := ⟨ComplexFourForm.toFun⟩

theorem complex_linear_zero_of_real {V : Type uV} (P : V → Prop)
    (L : (V → ℂ) → ℂ)
    (ha : ∀ u v, L (u+v) = L u + L v)
    (hs : ∀ r u, L (r • u) = r * L u)
    (hr : ∀ u : V → ℝ, (∀ x, P x → u x = 0) → L (fun x => (u x : ℂ)) = 0)
    (u : V → ℂ) (hu : ∀ x, P x → u x = 0) : L u = 0 := by
  have hre : ∀ x, P x → (u x).re = 0 := by
    intro x hx
    rw [hu x hx, Complex.zero_re]
  have him : ∀ x, P x → (u x).im = 0 := by
    intro x hx
    rw [hu x hx, Complex.zero_im]
  have hd : u = (fun x => ((u x).re : ℂ)) + Complex.I • (fun x => ((u x).im : ℂ)) := by
    ext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (u x)).symm
  rw [hd, ha, hs, hr _ hre, hr _ him]
  simp only [mul_zero, add_zero]

theorem ComplexFourForm.zero_of_real {V : Type uV} (F : ComplexFourForm (V → ℂ))
    (P : V → Prop)
    (hr : ∀ u v w z : V → ℝ,
      (∀ x, P x → u x = 0) → (∀ x, P x → v x = 0) →
      (∀ x, P x → w x = 0) → (∀ x, P x → z x = 0) →
      F (fun x => (u x : ℂ)) (fun x => (v x : ℂ))
        (fun x => (w x : ℂ)) (fun x => (z x : ℂ)) = 0)
    (u v w z : V → ℂ)
    (hu : ∀ x, P x → u x = 0) (hv : ∀ x, P x → v x = 0)
    (hw : ∀ x, P x → w x = 0) (hz : ∀ x, P x → z x = 0) :
    F u v w z = 0 := by
  apply complex_linear_zero_of_real P (fun u => F u v w z)
    (fun u u' => F.add_first u u' v w z) (fun r u => F.smul_first r u v w z) ?_ u hu
  intro a ha
  apply complex_linear_zero_of_real P (fun v => F (fun x => (a x : ℂ)) v w z)
    (fun v v' => F.add_second (fun x => (a x : ℂ)) v v' w z)
    (fun r v => F.smul_second r (fun x => (a x : ℂ)) v w z) ?_ v hv
  intro b hb
  apply complex_linear_zero_of_real P
    (fun w => F (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w z)
    (fun w w' => F.add_third (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w w' z)
    (fun r w => F.smul_third r (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) w z) ?_ w hw
  intro c hc
  apply complex_linear_zero_of_real P
    (fun z => F (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z)
    (fun z z' => F.add_fourth (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z z')
    (fun r z => F.smul_fourth r (fun x => (a x : ℂ)) (fun x => (b x : ℂ)) (fun x => (c x : ℂ)) z)
    ?_ z hz
  intro d hd
  exact hr a b c d ha hb hc hd

namespace MixedAlgebra
variable {E : Type uE} {K : Type uK} {L : Type uL} [Fintype E] [CommRing K] [CommRing L]

@[expose] def Coeffs.map (φ : K →+* L) (J : Coeffs E K) : Coeffs E L where
  a := φ ∘ J.a
  b := φ ∘ J.b
  aa := φ ∘ J.aa
  ab := φ ∘ J.ab
  bb := φ ∘ J.bb
  aab := φ ∘ J.aab
  abb := φ ∘ J.abb
  aabb := φ ∘ J.aabb

theorem weighted_map (φ : K →+* L) (J u : E → K) :
    weighted (φ ∘ J) (φ ∘ u) = φ (weighted J u) := by
  simp [weighted]

theorem four_map (φ : K →+* L) (J : Coeffs E K) (u v w z : E → K) :
    four (J.map φ) (φ ∘ u) (φ ∘ v) (φ ∘ w) (φ ∘ z) = φ (four J u v w z) := by
  simp only [four, Coeffs.map, weighted, Function.comp_apply, Pi.mul_apply,
    map_add, map_mul, map_sum]

theorem weighted_smul (J u : E → K) (r : K) :
    weighted J (r • u) = r * weighted J u := by
  exact weighted_const_mul J u r

theorem four_smul_first (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J (r • u) v w z = r * four J u v w z := by
  simp only [four, smul_mul_assoc, weighted_smul]
  ring

theorem four_smul_second (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u (r • v) w z = r * four J u v w z := by
  simp only [four, mul_smul_comm, smul_mul_assoc, weighted_smul]
  ring

theorem four_smul_third (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u v (r • w) z = r * four J u v w z := by
  rw [four_swap_first_third, four_smul_first, four_swap_first_third J w]

theorem four_smul_fourth (J : Coeffs E K) (u v w z : E → K) (r : K) :
    four J u v w (r • z) = r * four J u v w z := by
  rw [four_swap_second_fourth, four_smul_second, four_swap_second_fourth J u z]

end MixedAlgebra


namespace MixedAlgebra
variable {I : Type uI} {J : Type uJ} {E : Type uE} {K : Type uK} [Fintype I] [Fintype J] [Fintype E] [CommRing K]

lemma sum_three_rotate (F : I → J → E → K) :
    (∑ i, ∑ j, ∑ e, F i j e) = ∑ e, ∑ i, ∑ j, F i j e := by
  calc _ = ∑ i, ∑ e, ∑ j, F i j e := by
         apply Finset.sum_congr rfl
         intro i _
         exact Finset.sum_comm
       _ = _ := Finset.sum_comm

lemma sum_weighted_separated (A : E → K) (p : I → E → K) (q : J → E → K)
    (a : I → K) (b : J → K) :
    (∑ i, ∑ j, weighted A (p i * q j) * a i * b j) =
      ∑ e, A e * (∑ i, p i e * a i) * (∑ j, q j e * b j) := by
  simp only [weighted, Finset.sum_mul, Pi.mul_apply]
  rw [sum_three_rotate]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma sum_current (B : E → K) (p : I → E → K) (a : I → K) :
    (∑ i, a i * weighted B (p i)) = weighted B (fun e => ∑ i, a i * p i e) := by
  simp only [weighted, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma contract_two_current (A B C : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i * r j) * weighted B (q i) * weighted C (s j)) =
      ∑ e, A e * weighted B (fun l => ∑ i, p i e * q i l) *
        weighted C (fun l => ∑ j, r j e * s j l) := by
  rw [sum_weighted_separated]
  simp only [sum_current]

lemma contract_two_two (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i * r j) * weighted B (q i * s j)) =
      ∑ e, ∑ l, A e * B l * (∑ i, p i e * q i l) * (∑ j, r j e * s j l) := by
  have h (i : I) (j : J) : weighted A (p i * r j) * weighted B (q i * s j) =
      ∑ l, B l * (weighted A (p i*r j) * q i l * s j l) := by
    simp only [weighted, Finset.mul_sum, Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [h]
  rw [sum_three_rotate]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_weighted_separated]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma contract_three_current (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*q i*r j) * weighted B (s j)) =
      ∑ e, A e * (∑ i, p i e*q i e) * weighted B (fun l => ∑ j, r j e*s j l) := by
  have h := sum_weighted_separated A (fun i => p i*q i) r (fun _ => 1)
    (fun j => weighted B (s j))
  simpa only [mul_one, Pi.mul_apply, sum_current] using h

lemma contract_four (A : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*q i*r j*s j)) =
      ∑ e, A e * (∑ i, p i e*q i e) * (∑ j, r j e*s j e) := by
  have h := sum_weighted_separated A (fun i => p i*q i) (fun j => r j*s j)
    (fun _ => 1) (fun _ => 1)
  simpa only [mul_one, Pi.mul_apply, mul_assoc] using h

lemma four_grouped (C : Coeffs E K) (u v w z : E → K) :
    four C u v w z =
    (weighted C.a u * weighted C.b v + weighted C.ab (u*v)) *
      (weighted C.a w * weighted C.b z + weighted C.ab (w*z)) +
    (weighted C.aa (u*w) * weighted C.b v * weighted C.b z +
      weighted C.ab (u*z) * weighted C.b v * weighted C.a w +
      weighted C.ab (v*w) * weighted C.a u * weighted C.b z +
      weighted C.bb (v*z) * weighted C.a u * weighted C.a w +
      weighted C.aa (u*w) * weighted C.bb (v*z) +
      weighted C.ab (u*z) * weighted C.ab (v*w) +
      weighted C.aab (u*v*w) * weighted C.b z +
      weighted C.abb (u*v*z) * weighted C.a w +
      weighted C.aab (u*w*z) * weighted C.b v +
      weighted C.abb (v*w*z) * weighted C.a u +
      weighted C.aabb (u*v*w*z)) := by
  unfold four
  ring

lemma contract_current_three (A B : E → K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, weighted A (p i*r j*s j) * weighted B (q i)) =
      ∑ e, A e * (∑ j, r j e*s j e) * weighted B (fun l => ∑ i, p i e*q i l) := by
  rw [Finset.sum_comm]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using contract_three_current A B r s p q

omit [Fintype J] in
@[expose] def paired (C : Coeffs E K) (p q : I → E → K) : K :=
  ∑ i, (weighted C.a (p i) * weighted C.b (q i) + weighted C.ab (p i*q i))

omit [Fintype J] in
@[expose] def kernel (p q : I → E → K) (e l : E) : K := ∑ i, p i e*q i l

lemma four_family_contraction (C : Coeffs E K) (p q : I → E → K) (r s : J → E → K) :
    (∑ i, ∑ j, four C (p i) (q i) (r j) (s j)) =
      paired C p q * paired C r s +
    ((∑ e, C.aa e * weighted C.b (kernel p q e) * weighted C.b (kernel r s e)) +
      (∑ e, C.ab e * weighted C.b (kernel p q e) * weighted C.a (kernel s r e)) +
      (∑ e, C.ab e * weighted C.a (kernel q p e) * weighted C.b (kernel r s e)) +
      (∑ e, C.bb e * weighted C.a (kernel q p e) * weighted C.a (kernel s r e)) +
      (∑ e, ∑ l, C.aa e*C.bb l * kernel p q e l * kernel r s e l) +
      (∑ e, ∑ l, C.ab e*C.ab l * kernel p q e l * kernel s r e l) +
      (∑ e, C.aab e * kernel p q e e * weighted C.b (kernel r s e)) +
      (∑ e, C.abb e * kernel p q e e * weighted C.a (kernel s r e)) +
      (∑ e, C.aab e * kernel r s e e * weighted C.b (kernel p q e)) +
      (∑ e, C.abb e * kernel r s e e * weighted C.a (kernel q p e)) +
      (∑ e, C.aabb e * kernel p q e e * kernel r s e e)) := by
  simp only [four_grouped, Finset.sum_add_distrib]
  have hp : (∑ i, ∑ j,
      (weighted C.a (p i)*weighted C.b (q i) + weighted C.ab (p i*q i)) *
      (weighted C.a (r j)*weighted C.b (s j) + weighted C.ab (r j*s j))) =
      paired C p q * paired C r s := by
    simp only [paired, Finset.sum_mul_sum]
  rw [hp, contract_two_current, contract_two_current, contract_two_current,
    contract_two_current, contract_two_two, contract_two_two,
    contract_three_current, contract_three_current, contract_current_three,
    contract_current_three, contract_four]
  rfl

end MixedAlgebra
end
end RP2.Quadratic
