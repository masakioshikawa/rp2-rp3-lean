module

public import RP3.FourierAll
public import RP3.QuadraticSecondBound

public section

/-! Fourier modes on the actual pinned squared-interaction spin system. -/
namespace RP3
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Quadratic.SpinSystem
variable {V E : Type*} [Fintype V] [Fintype E]

theorem response_imaginary_multiple (S : SpinSystem V E) (u : E → ℝ) (r : ℝ) :
    (S.complexSecondResponse (fun e => -Complex.I*((r*u e:ℝ):ℂ))
      (fun e => conj (-Complex.I*((r*u e:ℝ):ℂ)))).re = r^2*S.secondAxisResponse u u := by
  have hf : (fun e => -Complex.I*((r*u e:ℝ):ℂ)) = (-Complex.I*(r:ℂ)) • (fun e => (u e:ℂ)) := by
    ext e; simp only [Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  have hg : (fun e => conj (-Complex.I*((r*u e:ℝ):ℂ))) = (Complex.I*(r:ℂ)) • (fun e => (u e:ℂ)) := by
    ext e; simp only [map_mul,map_neg,Complex.conj_I,neg_neg,Complex.conj_ofReal,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]; ring
  rw [hf,hg,S.complexSecondResponse_smul_left,S.complexSecondResponse_smul_right,S.complexSecondResponse_ofReal]
  simp only [Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im]
  ring
end Quadratic.SpinSystem

namespace Fourier.LatticeGraph

@[expose] def spinSystem (G : LatticeGraph) (b : G.edges → ℝ) (P : G.vertices → Option RP3.Spin) :
    Quadratic.SpinSystem G.vertices G.edges := ⟨fun e => e.val.1, fun e => e.val.2, b, P⟩

@[expose] def BoundaryPins (G : LatticeGraph) (k : ℕ) (P : G.vertices → Option RP3.Spin) : Prop :=
  ∀ x s, P x=some s →
    (|(scaledSite k x.val).1| ≤ 1 ∧ |(scaledSite k x.val).2| ≤ 1) ∨
    (2 ≤ |(scaledSite k x.val).1| ∨ 2 ≤ |(scaledSite k x.val).2|)

theorem modes_zero_pins (G : LatticeGraph) (k : ℕ) (P : G.vertices → Option RP3.Spin)
    (hP : G.BoundaryPins k P) (i : ModeIndex k) (x : G.vertices) (s : RP3.Spin) (hs : P x=some s) :
    G.modes i x=0 := by
  have hp : squareProfile i.1.1 i.1.2 (scaledSite k x.val)=0 := by
    rcases hP x s hs with h | h
    · exact squareProfile_zero_inner _ _ _ h.1 h.2
    · exact squareProfile_zero_outer _ _ _ h
  simp [modes,latticeMode,hp]

theorem system_modes_commutator (G : LatticeGraph) (k : ℕ) (b : G.edges → ℝ)
    (P : G.vertices → Option RP3.Spin) :
    (∑ i : ModeIndex k, (G.spinSystem b P).commutatorForm (G.modes i) (fun x => conj (G.modes i x))) =
      (fun e => -Complex.I*((dyadicLambda k*G.profileEdge k e:ℝ):ℂ)) := by
  ext e
  rw [Finset.sum_apply]
  convert G.modes_commutator e using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Quadratic.SpinSystem.commutatorForm,Quadratic.SpinSystem.complexCross,
    Pi.smul_apply,smul_eq_mul,spinSystem,modes,modeCommutator]
  ring

end Fourier.LatticeGraph
end
end RP3
