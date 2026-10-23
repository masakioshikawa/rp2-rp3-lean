module

public import RP3.Fourier.ModelModes
public import RP3.Fourier.ResponseTransfer
public import RP3.QuadraticFamily

public section

/-!
# Uniform inverse-logarithmic annular response of the RP³ model

This file substitutes the actual squared-interaction response in the proved
Fourier estimates. All pins are arbitrary directors, including at intermediate
rotation angles. The graph may omit vertices and edges.
-/
namespace RP3.Fourier
noncomputable section
open scoped BigOperators ComplexConjugate
namespace LatticeGraph

theorem profile_response_bound (G : LatticeGraph) (k : ℕ) (hk : 0 < k)
    (hG : G.WithinDyadicBox k) (β : ℝ) (hβ : 0 ≤ β)
    (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (P : G.vertices → Option RP3.Spin) (hP : G.BoundaryPins k P)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖) :
    -(G.spinSystem b P).secondAxisResponse (G.profileEdge k) (G.profileEdge k) ≤
      rotationCostConstant (16*β) C/(k:ℝ) := by
  have h := (G.spinSystem b P).rotation_family_bound β hβ hb (G.modes (k := k))
    (fun i x s hs => G.modes_zero_pins k P hP i x s hs)
  have hd : (fun i : ModeIndex k => (G.spinSystem b P).edgeGradient (G.modes i)) =
      G.modeDifferences := rfl
  rw [G.system_modes_commutator k b P,
    (G.spinSystem b P).response_imaginary_multiple, hd] at h
  have hde (i : ModeIndex k) (e : G.edges) :
      (G.spinSystem b P).edgeGradient (G.modes i) e = G.modeDifferences i e := rfl
  simp only [hde] at h
  apply G.profile_response_bound_of_family k hk hG (16*β) (by positivity) C hC hv hLip
  refine le_trans (by simpa only [neg_mul] using h) ?_
  gcongr <;> linarith

theorem theta_response_bound (G : LatticeGraph) (k : ℕ) (hk : 0 < k)
    (hG : G.WithinDyadicBox k) (β : ℝ) (hβ : 0 ≤ β)
    (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (P : G.vertices → Option RP3.Spin) (hP : G.BoundaryPins k P)
    (C L D : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3) :
    -(G.spinSystem b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤
      rotationCostConstant (16*β) C/(k:ℝ)+transferCostConstant (16*β) L D/(2:ℝ)^k := by
  let a := rotationCostConstant (16*β) C/(k:ℝ)
  have ha : 0 ≤ a := div_nonneg (rotationCostConstant_nonneg _ _ (by positivity)) (Nat.cast_nonneg _)
  have hp := G.profile_response_bound k hk hG β hβ b hb P hP C hC hv hLip
  have ht := (G.spinSystem b P).real_response_transfer β a hβ ha hb
    (G.thetaEdge k) (G.profileEdge k) hp
  apply G.theta_response_bound_of_transfer k hG (16*β) L D a
    ((G.spinSystem b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k))
    (by positivity) hL hD he
  apply ht.trans
  gcongr <;> linarith

/-- The analytic input is now proved for the actual RP³ Gibbs expectation,
uniformly over all finite retained annular graphs and all pinned directors. -/
theorem annulus_response_inverse_scale (β : ℝ) (hβ : 0 ≤ β) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (k : ℕ), 4 ≤ k →
      ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e, |b e| ≤ β) →
      ∀ (P : G.vertices → Option RP3.Spin), G.BoundaryPins k P →
        -(G.spinSystem b P).secondAxisResponse (G.thetaEdge k) (G.thetaEdge k) ≤ K/(k:ℝ) := by
  obtain ⟨C,hC,hv,hLip⟩ := profiles_uniform_bound
  obtain ⟨L,D,hL,hD,he⟩ := theta_edge_bounds
  let A := rotationCostConstant (16*β) C
  let B := transferCostConstant (16*β) L D
  have hA : 0 ≤ A := rotationCostConstant_nonneg _ _ (by positivity)
  have hB : 0 ≤ B := transferCostConstant_nonneg _ _ _ (by positivity) hL hD
  refine ⟨A+B, add_nonneg hA hB, ?_⟩
  intro k hk G hG b hb P hP
  exact (G.theta_response_bound k (by omega) hG β hβ b hb P hP C L D (by linarith)
    hL hD hv hLip (he G k hk)).trans (dyadic_error_le_inverse_scale k (by omega) A B hB)

end LatticeGraph
end
end RP3.Fourier
