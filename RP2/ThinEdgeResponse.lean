module

public import RP2.ThinFourier
public import RP2.ThinProfileLattice

public section

/-! The thin-profile approximation on actual lattice edges and the corresponding
model-specific real-response transfer. -/
namespace RP2.Fourier
noncomputable section
open scoped BigOperators
namespace LatticeGraph

/-- The same two constants work for every location, shell width, mesh and graph. -/
theorem thinTheta_edge_bounds : ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧
    ∀ (a δ : ℝ), 0 < δ → δ ≤ a →
    ∀ (G : LatticeGraph) (k h : ℕ), 1/(2:ℝ)^k ≤ δ/16 → ∀ e : G.edges,
      |G.thinThetaEdge k a δ e| ≤ (L/δ)/(2:ℝ)^k ∧
      |G.thinThetaEdge k a δ e-G.thinProfileEdge h (thinProfile a δ) k e| ≤
        (D/δ^3)/((2:ℝ)^k)^3 := by
  obtain ⟨L,hL,hLip⟩ := thinTheta_lipschitz_bound
  obtain ⟨D,hD,hR⟩ := thinTheta_step_error
  refine ⟨L,D,hL,hD,?_⟩
  intro a δ hδ ha G k h hmesh e
  constructor
  · have ht := hLip a δ hδ ha (scaledSite k e.val.1.val) (scaledSite k e.val.2.val)
    rw [G.scaled_edge_distance] at ht
    exact ht.trans_eq (by ring)
  · have hs : |1/(2:ℝ)^k| ≤ δ/16 := by
      rwa [abs_of_pos (by positivity : 0 < 1/(2:ℝ)^k)]
    have ht := hR a δ hδ ha (G.edgeDirection e) (scaledSite k e.val.1.val) (1/(2:ℝ)^k) hs
    rw [← scaledSite_add_axis, ← G.edge_step e,
      abs_of_pos (by positivity : 0 < 1/(2:ℝ)^k)] at ht
    simpa only [thinThetaEdge, thinThetaPotential, thinProfileEdge,
      div_pow, one_pow, mul_one_div] using ht

/-- Transfer between two explicit real edge fields in the actual pinned model. -/
theorem thin_actual_response_transfer (G : LatticeGraph) (k : ℕ)
    (hG : G.WithinDyadicBox k) (β : ℝ) (hβ : 0 ≤ β)
    (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (P : G.vertices → Option RP2.Spin) (u v : G.edges → ℝ)
    (A L D : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hp : -(G.spinSystem b P).secondAxisResponse v v ≤ A)
    (he : ∀ e : G.edges, |u e| ≤ L/(2:ℝ)^k ∧
      |u e-v e| ≤ D/((2:ℝ)^k)^3) :
    -(G.spinSystem b P).secondAxisResponse u u ≤
      A+transferCostConstant (16*β) L D/(2:ℝ)^k := by
  have ht := (G.spinSystem b P).real_response_transfer β A hβ hA hb u v hp
  apply G.thin_response_bound_of_transfer k hG u v (16*β) L D A
    ((G.spinSystem b P).secondAxisResponse u u) (by positivity) hL hD he
  apply ht.trans
  gcongr <;> linarith

end LatticeGraph
end
end RP2.Fourier
