module

public import RP2.QuadraticAverages
public import RP2.ComplexCurrents
public import RP2.MixedAlgebra

public section

/-!
# The real and complex bilinear second response for RP²

The algebraic response interface is adapted from OpenAI's ClassicalON
MixedWard and ComplexWard at adc7f1241b42e322a6451854ab7e4b4c146bf78a
(Apache-2.0, copyright OpenAI). The coefficients below are the derivatives
of the squared interaction, including the square of the first inner-product
derivative in the Hessian.
-/
namespace RP2.Quadratic
universe uV uE
noncomputable section
open RP2.Rotation hiding Spin
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace SpinSystem
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem firstEnergy_add (S : SpinSystem V E) (A B : E → SpinOperator 3)
    (σ : V → RP2.Spin) : S.firstEnergy (A+B) σ = S.firstEnergy A σ + S.firstEnergy B σ := by
  simp only [firstEnergy, Pi.add_apply, add_apply, inner_add_right,
    mul_add, Finset.sum_add_distrib]

omit [Fintype V] in
theorem secondAxisEnergy_add_left (S : SpinSystem V E) (h k l : E → ℝ)
    (σ : V → RP2.Spin) :
    S.secondAxisEnergy (h+k) l σ = S.secondAxisEnergy h l σ + S.secondAxisEnergy k l σ := by
  simp only [secondAxisEnergy, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  abel

omit [Fintype V] in
theorem secondAxisEnergy_symm (S : SpinSystem V E) (h k : E → ℝ)
    (σ : V → RP2.Spin) : S.secondAxisEnergy h k σ = S.secondAxisEnergy k h σ := by
  simp only [secondAxisEnergy, mul_comm]

omit [Fintype V] in
@[fun_prop] theorem continuous_secondPolynomial (S : SpinSystem V E) (h k : E → ℝ) :
    Continuous (fun σ => S.secondAxisEnergy h k σ +
      S.firstEnergy (fun e => h e • axisC) σ * S.firstEnergy (fun e => k e • axisC) σ) := by
  unfold secondAxisEnergy firstEnergy
  fun_prop

@[expose] def secondObservable (S : SpinSystem V E) (h k : E → ℝ) : C((V → RP2.Spin), ℝ) :=
  ⟨_, S.continuous_secondPolynomial h k⟩

@[simp] theorem secondObservable_average (S : SpinSystem V E) (h k : E → ℝ) :
    S.averageLinear (S.secondObservable h k) = S.secondAxisResponse h k := rfl

omit [Fintype V] in
theorem secondObservable_add_left (S : SpinSystem V E) (u v w : E → ℝ) :
    S.secondObservable (u+v) w = S.secondObservable u w + S.secondObservable v w := by
  ext σ
  have hs : (fun e => (u+v) e • axisC) =
      (fun e => u e • axisC) + (fun e => v e • axisC) := by
    funext e
    exact add_smul (u e) (v e) axisC
  simp only [secondObservable, ContinuousMap.coe_mk, ContinuousMap.add_apply,
    secondAxisEnergy_add_left, hs, firstEnergy_add]
  ring

omit [Fintype V] in
theorem secondObservable_symm (S : SpinSystem V E) (u v : E → ℝ) :
    S.secondObservable u v = S.secondObservable v u := by
  ext σ
  simp only [secondObservable, ContinuousMap.coe_mk,
    S.secondAxisEnergy_symm u v, mul_comm]

theorem secondAxisResponse_add_left (S : SpinSystem V E) (u v w : E → ℝ) :
    S.secondAxisResponse (u+v) w = S.secondAxisResponse u w + S.secondAxisResponse v w := by
  have h := congrArg S.averageLinear (S.secondObservable_add_left u v w)
  simpa only [map_add, secondObservable_average] using h

theorem secondAxisResponse_symm (S : SpinSystem V E) (u v : E → ℝ) :
    S.secondAxisResponse u v = S.secondAxisResponse v u :=
  congrArg S.averageLinear (S.secondObservable_symm u v)

theorem secondAxisResponse_add_right (S : SpinSystem V E) (u v w : E → ℝ) :
    S.secondAxisResponse u (v+w) = S.secondAxisResponse u v + S.secondAxisResponse u w := by
  rw [S.secondAxisResponse_symm, S.secondAxisResponse_add_left,
    S.secondAxisResponse_symm v, S.secondAxisResponse_symm w]

omit [Fintype V] [Fintype E] in
@[expose] def scalarHessianCoefficient (S : SpinSystem V E) (g : SpinOperator 3)
    (σ : V → RP2.Spin) (e : E) : ℝ :=
  2 * S.strength e *
    (⟪(σ (S.left e)).val, g (σ (S.right e)).val⟫_ℝ ^ 2 +
      ⟪(σ (S.left e)).val, (σ (S.right e)).val⟫_ℝ *
        ⟪(σ (S.left e)).val, (g ^ 2) (σ (S.right e)).val⟫_ℝ)

/-- Complex-linear combination of the second-derivative coefficients. -/
@[expose] def complexHessian (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℂ) (σ : V → RP2.Spin) : ℂ :=
  MixedAlgebra.weighted (fun e => (S.scalarHessianCoefficient g σ e : ℂ)) h

omit [Fintype V] in
@[fun_prop] theorem continuous_complexHessian (S : SpinSystem V E)
    (g : SpinOperator 3) (h : E → ℂ) : Continuous (S.complexHessian g h) := by
  unfold complexHessian MixedAlgebra.weighted scalarHessianCoefficient
  fun_prop

omit [Fintype V] in
theorem complexCurrent_ofReal (S : SpinSystem V E) (g : SpinOperator 3)
    (h : E → ℝ) (σ : V → RP2.Spin) :
    S.complexCurrent g (fun e => (h e : ℂ)) σ =
      (S.firstEnergy (fun e => h e • g) σ : ℂ) := by
  apply Complex.ext
  · rfl
  · simp [complexCurrent, firstEnergy]

omit [Fintype V] in
theorem complexHessian_ofReal_mul (S : SpinSystem V E) (h k : E → ℝ)
    (σ : V → RP2.Spin) :
    S.complexHessian axisC (fun e => ((h e*k e : ℝ) : ℂ)) σ =
      (S.secondAxisEnergy h k σ : ℂ) := by
  simp only [complexHessian, MixedAlgebra.weighted, scalarHessianCoefficient,
    secondAxisEnergy, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

omit [Fintype V] in
@[simp] theorem complexHessian_add (S : SpinSystem V E) (g : SpinOperator 3)
    (u v : E → ℂ) (σ : V → RP2.Spin) :
    S.complexHessian g (u+v) σ = S.complexHessian g u σ + S.complexHessian g v σ :=
  MixedAlgebra.weighted_add _ u v

omit [Fintype V] in
@[simp] theorem complexHessian_smul (S : SpinSystem V E) (g : SpinOperator 3)
    (u : E → ℂ) (r : ℂ) (σ : V → RP2.Spin) :
    S.complexHessian g (r • u) σ = r * S.complexHessian g u σ :=
  MixedAlgebra.weighted_smul _ u r

omit [Fintype V] in
@[fun_prop] theorem continuous_complexSecondPolynomial (S : SpinSystem V E)
    (u v : E → ℂ) : Continuous (fun σ => S.complexHessian axisC (u*v) σ +
      S.complexCurrent axisC u σ * S.complexCurrent axisC v σ) :=
  (S.continuous_complexHessian _ _).add
    ((S.continuous_complexCurrent _ _).mul (S.continuous_complexCurrent _ _))

@[expose] def complexSecondObservable (S : SpinSystem V E) (u v : E → ℂ) : C((V → RP2.Spin), ℂ) :=
  ⟨_, S.continuous_complexSecondPolynomial u v⟩

@[expose] def complexSecondResponse (S : SpinSystem V E) (u v : E → ℂ) : ℂ :=
  S.averageComplexLinear (S.complexSecondObservable u v)

theorem complexSecondResponse_ofReal (S : SpinSystem V E) (u v : E → ℝ) :
    S.complexSecondResponse (fun e => (u e : ℂ)) (fun e => (v e : ℂ)) =
      (S.secondAxisResponse u v : ℂ) := by
  have hp : S.complexSecondObservable (fun e => (u e : ℂ)) (fun e => (v e : ℂ)) =
      ofRealObservable (S.secondObservable u v) := by
    ext σ
    change S.complexHessian axisC ((fun e => (u e : ℂ)) * (fun e => (v e : ℂ))) σ +
      S.complexCurrent axisC (fun e => (u e : ℂ)) σ *
        S.complexCurrent axisC (fun e => (v e : ℂ)) σ = _
    rw [show ((fun e => (u e : ℂ)) * (fun e => (v e : ℂ))) =
      (fun e => ((u e*v e : ℝ) : ℂ)) from by ext; simp]
    simp only [complexHessian_ofReal_mul, complexCurrent_ofReal,
      ← Complex.ofReal_add, ← Complex.ofReal_mul]
    rfl
  unfold complexSecondResponse
  rw [hp, S.averageComplex_ofReal, S.secondObservable_average]

theorem complexSecondResponse_add_left (S : SpinSystem V E) (u v w : E → ℂ) :
    S.complexSecondResponse (u+v) w = S.complexSecondResponse u w + S.complexSecondResponse v w := by
  have hp : S.complexSecondObservable (u+v) w =
      S.complexSecondObservable u w + S.complexSecondObservable v w := by
    ext σ
    change S.complexHessian axisC ((u+v)*w) σ +
      S.complexCurrent axisC (u+v) σ * S.complexCurrent axisC w σ =
      (S.complexHessian axisC (u*w) σ +
        S.complexCurrent axisC u σ * S.complexCurrent axisC w σ) +
      (S.complexHessian axisC (v*w) σ +
        S.complexCurrent axisC v σ * S.complexCurrent axisC w σ)
    rw [add_mul, complexHessian_add, complexCurrent_add]
    ring
  unfold complexSecondResponse
  rw [hp, map_add]

theorem complexSecondResponse_symm (S : SpinSystem V E) (u v : E → ℂ) :
    S.complexSecondResponse u v = S.complexSecondResponse v u := by
  have hp : S.complexSecondObservable u v = S.complexSecondObservable v u := by
    ext σ
    change S.complexHessian axisC (u*v) σ +
      S.complexCurrent axisC u σ * S.complexCurrent axisC v σ =
      S.complexHessian axisC (v*u) σ +
        S.complexCurrent axisC v σ * S.complexCurrent axisC u σ
    rw [mul_comm u v, mul_comm (S.complexCurrent axisC u σ)]
  exact congrArg S.averageComplexLinear hp

theorem complexSecondResponse_add_right (S : SpinSystem V E) (u v w : E → ℂ) :
    S.complexSecondResponse u (v+w) = S.complexSecondResponse u v + S.complexSecondResponse u w := by
  rw [S.complexSecondResponse_symm, S.complexSecondResponse_add_left,
    S.complexSecondResponse_symm v, S.complexSecondResponse_symm w]

theorem complexSecondResponse_smul_left (S : SpinSystem V E) (u v : E → ℂ) (r : ℂ) :
    S.complexSecondResponse (r • u) v = r * S.complexSecondResponse u v := by
  have hp : S.complexSecondObservable (r • u) v = r • S.complexSecondObservable u v := by
    ext σ
    change S.complexHessian axisC ((r • u)*v) σ +
      S.complexCurrent axisC (r • u) σ * S.complexCurrent axisC v σ =
      r * (S.complexHessian axisC (u*v) σ +
        S.complexCurrent axisC u σ * S.complexCurrent axisC v σ)
    rw [smul_mul_assoc, complexHessian_smul, complexCurrent_smul]
    ring
  unfold complexSecondResponse
  rw [hp, map_smul, smul_eq_mul]

theorem complexSecondResponse_smul_right (S : SpinSystem V E) (u v : E → ℂ) (r : ℂ) :
    S.complexSecondResponse u (r • v) = r * S.complexSecondResponse u v := by
  rw [S.complexSecondResponse_symm, S.complexSecondResponse_smul_left,
    S.complexSecondResponse_symm v]

omit [Fintype V] [Fintype E] in
@[expose] def complexCross (S : SpinSystem V E) (f g : V → ℂ) : E → ℂ :=
  fun e => f (S.left e)*g (S.right e) - g (S.left e)*f (S.right e)

omit [Fintype V] [Fintype E] in
theorem complexCross_ofReal (S : SpinSystem V E) (f g : V → ℝ) :
    S.complexCross (fun x => (f x : ℂ)) (fun x => (g x : ℂ)) =
      fun e => (S.crossForm f g e : ℂ) := by
  ext e
  simp [complexCross, crossForm]

omit [Fintype V] [Fintype E] in
theorem edgeGradient_ofReal (S : SpinSystem V E) (f : V → ℝ) :
    S.edgeGradient (fun x => (f x : ℂ)) = fun e => (S.edgeGradient (𝕜 := ℝ) f e : ℂ) := by
  ext e
  simp [edgeGradient]

omit [Fintype V] [Fintype E] in
theorem complexCross_add_left (S : SpinSystem V E) (f g h : V → ℂ) :
    S.complexCross (f+h) g = S.complexCross f g + S.complexCross h g := by
  ext e
  simp only [complexCross, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_smul_left (S : SpinSystem V E) (f g : V → ℂ) (r : ℂ) :
    S.complexCross (r • f) g = r • S.complexCross f g := by
  ext e
  simp only [complexCross, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_add_right (S : SpinSystem V E) (f g h : V → ℂ) :
    S.complexCross f (g+h) = S.complexCross f g + S.complexCross f h := by
  ext e
  simp only [complexCross, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexCross_smul_right (S : SpinSystem V E) (f g : V → ℂ) (r : ℂ) :
    S.complexCross f (r • g) = r • S.complexCross f g := by
  ext e
  simp only [complexCross, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype V] [Fintype E] in
theorem complexDifferential_add (S : SpinSystem V E) (f g : V → ℂ) :
    S.edgeGradient (f+g) = S.edgeGradient f + S.edgeGradient g := by
  ext e
  simp only [edgeGradient, Pi.add_apply]
  ring

omit [Fintype V] [Fintype E] in
theorem complexDifferential_smul (S : SpinSystem V E) (f : V → ℂ) (r : ℂ) :
    S.edgeGradient (r • f) = r • S.edgeGradient f := by
  ext e
  simp only [edgeGradient, Pi.smul_apply, smul_eq_mul]
  ring


end SpinSystem
end
end RP2.Quadratic
