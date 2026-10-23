import RP3.ThinEdgeResponse
import RP3.ThinCosts
import RP3.ThinSupport

/-! Uniform response estimates for the actual pinned RP³ Gibbs system on a
thin square annulus.  No analytic estimate remains as an input hypothesis. -/
namespace RP3.Fourier.LatticeGraph
noncomputable section
open scoped BigOperators Classical

/-- The constants are chosen before the shell, graph, couplings and arbitrary
pinned directors. The first error is inverse logarithmic with one inverse
power of the relative width; the mesh remainder costs six inverse powers. -/
theorem thin_annulus_response (β : ℝ) (hβ : 0 ≤ β) :
    ∃ K V : ℝ, 0 ≤ K ∧ 0 ≤ V ∧
      ∀ (k h : ℕ), 0 < k → 2*h ≤ k →
      ∀ (a δ : ℝ), 0 < δ → δ ≤ 1 → δ ≤ a →
        1/(2:ℝ)^h ≤ δ → 1/(2:ℝ)^k ≤ δ/16 →
      ∀ (R S : ℤ), (2:ℤ)^k ≤ R → R < S → S ≤ 2*(2:ℤ)^k →
        (R:ℝ) = a*(2:ℝ)^k → (S:ℝ) = (a+δ)*(2:ℝ)^k →
      ∀ (G : LatticeGraph), G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ), (∀ e, |b e| ≤ β) →
      ∀ (P : G.vertices → Option RP3.Spin), G.ThinBoundaryPins k a δ P →
      -(G.spinSystem b P).secondAxisResponse
        (G.thinThetaEdge k a δ) (G.thinThetaEdge k a δ) ≤
          K/δ/(k:ℝ)+V/δ^6/(2:ℝ)^k := by
  obtain ⟨P0,hP0,hprofiles⟩ := thinProfile_uniform_bounds
  obtain ⟨L0,D0,hL0,hD0,hedges⟩ := thinTheta_edge_bounds
  let K := thinRotationCost (16*β) P0 (2*modeBlockConstant P0)
    (64*(P0+P0*(Real.pi/4))^2)
  let V := transferCostConstant (16*β) L0 D0
  have hK : 0 ≤ K := thinRotationCost_nonneg _ _ _ _ (by positivity) (by positivity)
  have hV : 0 ≤ V := transferCostConstant_nonneg _ _ _ (by positivity) hL0 hD0
  refine ⟨K,V,hK,hV,?_⟩
  intro k h hk hh a δ hδ hδ1 ha hfreq hmesh R S hNR hRS hSN hR hS G hG b hb pins hpins
  obtain ⟨hval,hLip⟩ := hprofiles a δ hδ ha
  let C := P0/Real.sqrt δ
  let L := P0/(δ*Real.sqrt δ)
  let A := 2*thinModeBlockConstant C L δ
  let J := 64*δ*(L*δ+C*(Real.pi/4))^2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hcount : ((G.thinKernelEdges R S 0).card:ℝ) ≤ (64*δ)*(2:ℝ)^(2*k) := by
    have hc := G.thinKernelEdges_card_bound (2^k) R S
      (one_le_pow₀ (by norm_num : (1:ℤ) ≤ 2)) hNR hRS hSN
    have hc' : ((G.thinKernelEdges R S 0).card:ℝ) ≤
        64*(2:ℝ)^k*((S:ℝ)-R) := by
      simpa only [Int.cast_pow,Int.cast_ofNat, show ((0,0):Site)=0 from rfl] using hc
    apply hc'.trans_eq
    rw [hR,hS,mul_comm 2 k,pow_mul]
    ring
  have hsupport : ∀ e : G.edges, e ∉ G.thinKernelEdges R S 0 → ∀ m s,
      thinProfile a δ m s (scaledSite k e.val.1.val)=0 ∧
      thinProfile a δ m s (scaledSite k e.val.2.val)=0 := by
    intro e he m s
    simp only [mem_thinKernelEdges,not_or] at he
    exact ⟨G.thinProfile_zero_outside_layer k a δ hδ ha R S hR hS m s _ he.1,
      G.thinProfile_zero_outside_layer k a δ hδ ha R S hR hS m s _ he.2⟩
  have hsb (m s : Bool) :
      SquareBound (fun e (p : DyadicFreq k) =>
        G.thinScaledModeGradient h (thinProfile a δ) m s p e) A :=
    G.thinScaledModes_squareBound hG h (thinProfile a δ) C L δ hδ.le hfreq hval hLip m s
  have hcol (m s : Bool) (p : DyadicFreq k) :
      (∑ e, ‖G.thinScaledModeGradient h (thinProfile a δ) m s p e‖^2) ≤ J :=
    G.thinScaledModes_column_bound h (thinProfile a δ) C L δ (64*δ)
      hC hL hδ.le hfreq hval hLip (G.thinKernelEdges R S 0) hcount hsupport m s p
  have hpin : ∀ x s, pins x=some s → ∀ m t,
      thinProfile a δ m t (scaledSite k x.val)=0 := by
    intro x s hx m t
    exact G.thinProfiles_zero_pins k a δ hδ ha pins hpins m t x s hx
  have hp := G.thin_profile_response_bound k h hk hh β hβ b hb pins
    (thinProfile a δ) hpin C A J hC hJ hval hsb hcol
  have hcost : thinRotationCost (16*β) C A J = K/δ :=
    thin_balanced_rotation_cost (16*β) P0 δ hδ
  rw [hcost] at hp
  have ht := G.thin_actual_response_transfer k hG β hβ b hb pins
    (G.thinThetaEdge k a δ) (G.thinProfileEdge h (thinProfile a δ) k)
    (K/δ/(k:ℝ)) (L0/δ) (D0/δ^3) (by positivity) (by positivity) (by positivity)
    hp (hedges a δ hδ ha G k h hmesh)
  apply ht.trans
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right
    (thin_transfer_cost_le (16*β) L0 D0 δ (by positivity) hL0 hD0 hδ hδ1)
    (by positivity)

end
end RP3.Fourier.LatticeGraph
