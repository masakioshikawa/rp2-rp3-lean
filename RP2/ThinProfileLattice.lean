import RP2.ThinProfiles
import RP2.ThinKernel
import RP2.Fourier.ResponseTransfer

/-! The thin smooth cutoffs on actual centered lattice shells. -/
namespace RP2.Fourier
noncomputable section
open scoped BigOperators Classical

theorem scaledSite_norm_radius (k : ℕ) (x : Site) :
    ‖scaledSite k x‖ = (siteRadius 0 x:ℝ)/(2:ℝ)^k := by
  have hN : 0 < (2:ℝ)^k := by positivity
  simp only [scaledSite, Prod.norm_def, Real.norm_eq_abs, abs_div, abs_of_pos hN,
    max_div_div_right hN.le, siteRadius, Prod.fst_zero, Prod.snd_zero, sub_zero,
    Int.cast_max, Int.cast_abs]

theorem scaledSite_thin_inner {k : ℕ} {x : Site} {a : ℝ}
    (h : (siteRadius 0 x:ℝ) ≤ a*(2:ℝ)^k) :
    |(scaledSite k x).1| ≤ a ∧ |(scaledSite k x).2| ≤ a := by
  have hn : ‖scaledSite k x‖ ≤ a := by
    rw [scaledSite_norm_radius, div_le_iff₀ (by positivity : 0 < (2:ℝ)^k)]
    exact h
  simpa only [Prod.norm_def, Real.norm_eq_abs, max_le_iff] using hn

theorem scaledSite_thin_outer {k : ℕ} {x : Site} {a : ℝ}
    (h : a*(2:ℝ)^k ≤ (siteRadius 0 x:ℝ)) :
    a ≤ |(scaledSite k x).1| ∨ a ≤ |(scaledSite k x).2| := by
  have hn : a ≤ ‖scaledSite k x‖ := by
    rw [scaledSite_norm_radius, le_div_iff₀ (by positivity : 0 < (2:ℝ)^k)]
    exact h
  simpa only [Prod.norm_def, Real.norm_eq_abs, le_max_iff] using hn

namespace LatticeGraph

def thinThetaPotential (G : LatticeGraph) (k : ℕ) (a δ : ℝ) (v : G.vertices) : ℝ :=
  thinTheta a δ (scaledSite k v.val)

def thinThetaEdge (G : LatticeGraph) (k : ℕ) (a δ : ℝ) (e : G.edges) : ℝ :=
  G.thinThetaPotential k a δ e.val.2-G.thinThetaPotential k a δ e.val.1

def ThinBoundaryPins (G : LatticeGraph) (k : ℕ) (a δ : ℝ)
    (P : G.vertices → Option RP2.Spin) : Prop :=
  ∀ v s, P v = some s →
    (|(scaledSite k v.val).1| ≤ a ∧ |(scaledSite k v.val).2| ≤ a) ∨
    (a+δ ≤ |(scaledSite k v.val).1| ∨ a+δ ≤ |(scaledSite k v.val).2|)

theorem thinProfiles_zero_pins (G : LatticeGraph) (k : ℕ) (a δ : ℝ)
    (hδ : 0 < δ) (ha : δ ≤ a) (P : G.vertices → Option RP2.Spin)
    (hP : G.ThinBoundaryPins k a δ P) (m s : Bool) (v : G.vertices)
    (t : RP2.Spin) (hv : P v = some t) :
    thinProfile a δ m s (scaledSite k v.val) = 0 := by
  rcases hP v t hv with hh | hh
  · exact thinProfile_zero_inner a δ hδ ha m s _ hh.1 hh.2
  · exact thinProfile_zero_outer a δ hδ ha m s _ hh

theorem thinBoundaryPins_of_radius (G : LatticeGraph) (k : ℕ) (a δ : ℝ)
    (R S : ℤ) (hR : (R:ℝ) = a*(2:ℝ)^k) (hS : (S:ℝ) = (a+δ)*(2:ℝ)^k)
    (P : G.vertices → Option RP2.Spin)
    (hP : ∀ v s, P v = some s → siteRadius 0 v.val = R ∨ siteRadius 0 v.val = S) :
    G.ThinBoundaryPins k a δ P := by
  intro v s hs
  rcases hP v s hs with hh | hh
  · left
    apply scaledSite_thin_inner
    rw [hh,hR]
  · right
    apply scaledSite_thin_outer
    rw [hh,hS]

theorem thinThetaPotential_of_boundary_radius (G : LatticeGraph) (k : ℕ) (a δ : ℝ)
    (hδ : 0 < δ) (ha : δ ≤ a) (R S : ℤ)
    (hR : (R:ℝ) = a*(2:ℝ)^k) (hS : (S:ℝ) = (a+δ)*(2:ℝ)^k)
    (v : G.vertices) (hv : siteRadius 0 v.val = R ∨ siteRadius 0 v.val = S) :
    G.thinThetaPotential k a δ v = if siteRadius 0 v.val ≤ R then 1 else 0 := by
  by_cases hi : siteRadius 0 v.val ≤ R
  · simp only [hi,ite_true,thinThetaPotential]
    have hh : (siteRadius 0 v.val:ℝ) ≤ a*(2:ℝ)^k := by
      rw [←hR]
      exact_mod_cast hi
    exact thinTheta_one a δ hδ ha _ (scaledSite_thin_inner hh).1 (scaledSite_thin_inner hh).2
  · simp only [hi,ite_false,thinThetaPotential]
    have hh : (a+δ)*(2:ℝ)^k ≤ (siteRadius 0 v.val:ℝ) := by
      rw [hv.resolve_left (fun he => hi he.le), hS]
    exact thinTheta_zero a δ hδ ha _ (scaledSite_thin_outer hh)

theorem thinProfile_zero_outside_layer (G : LatticeGraph) (k : ℕ) (a δ : ℝ)
    (hδ : 0 < δ) (ha : δ ≤ a) (R S : ℤ)
    (hR : (R:ℝ) = a*(2:ℝ)^k) (hS : (S:ℝ) = (a+δ)*(2:ℝ)^k)
    (m s : Bool) (v : G.vertices) (hv : v ∉ G.thinLayer R S 0) :
    thinProfile a δ m s (scaledSite k v.val) = 0 := by
  simp only [mem_thinLayer,not_and_or,not_lt] at hv
  rcases hv with hv | hv
  · have hh : (siteRadius 0 v.val:ℝ) ≤ a*(2:ℝ)^k := by
      rw [←hR]; exact_mod_cast hv
    exact thinProfile_zero_inner a δ hδ ha m s _
      (scaledSite_thin_inner hh).1 (scaledSite_thin_inner hh).2
  · have hh : (a+δ)*(2:ℝ)^k ≤ (siteRadius 0 v.val:ℝ) := by
      rw [←hS]; exact_mod_cast hv
    exact thinProfile_zero_outer a δ hδ ha m s _ (scaledSite_thin_outer hh)

theorem thin_transfer_sum_bounds (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k)
    (u v : G.edges → ℝ) (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (he : ∀ e : G.edges, |u e| ≤ L/(2:ℝ)^k ∧
      |u e-v e| ≤ D/((2:ℝ)^k)^3) :
    (∑ e, |u e-v e|) ≤ 512*D/(2:ℝ)^k ∧
    (∑ e, |u e|^2) ≤ 512*L^2 ∧
    (∑ e, |u e-v e| *
      (|u e| + |v e|)) ≤ 512*D*(2*L+D)/((2:ℝ)^k)^2 := by
  let N : ℝ := (2:ℝ)^k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hcount := G.edge_card_bound k hG
  change (Fintype.card G.edges:ℝ) ≤ 512*N^2 at hcount
  have hv (e : G.edges) : |v e| ≤ (L+D)/N := by
    have htri : |v e| ≤ |u e| + |u e-v e| := by
      simpa only [add_sub_cancel, abs_sub_comm] using abs_add_le (u e) (v e-u e)
    have hpow : N ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
    calc _ ≤ L/N+D/N^3 := htri.trans (add_le_add (he e).1 (he e).2)
         _ ≤ L/N+D/N := add_le_add_right (div_le_div_of_nonneg_left hD hN hpow) _
         _ = _ := by ring
  have hs1 : (∑ e, |u e-v e|) ≤ (Fintype.card G.edges:ℝ)*(D/N^3) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun e _ => (he e).2)
  have hs2 : (∑ e, |u e|^2) ≤ (Fintype.card G.edges:ℝ)*(L/N)^2 := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => pow_le_pow_left₀ (abs_nonneg _) (he e).1 2)
  have hs3 : (∑ e, |u e-v e| *(|u e| + |v e|)) ≤
      (Fintype.card G.edges:ℝ)*(D/N^3*((2*L+D)/N)) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => mul_le_mul (he e).2 (show |u e| + |v e| ≤ (2*L+D)/N from
        (add_le_add (he e).1 (hv e)).trans_eq (by ring)) (by positivity) (by positivity))
  refine ⟨hs1.trans ?_,hs2.trans ?_,hs3.trans ?_⟩
  all_goals
    calc _ ≤ 512*N^2*_ := mul_le_mul_of_nonneg_right hcount (by positivity)
         _ = _ := by dsimp only [N]; field_simp

theorem thin_response_bound_of_transfer (G : LatticeGraph) (k : ℕ)
    (hG : G.WithinDyadicBox k) (u v : G.edges → ℝ) (M L D a R : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (he : ∀ e : G.edges, |u e| ≤ L/(2:ℝ)^k ∧
      |u e-v e| ≤ D/((2:ℝ)^k)^3)
    (htransfer : -R ≤ a +
      M*(∑ e, |u e-v e| *
        (|u e|+|v e|)) +
      (M*∑ e, |u e-v e|) *
        (M*(∑ e, (u e)^2)+1) +
      (M*∑ e, |u e-v e|)^2) :
    -R ≤ a+transferCostConstant M L D/(2:ℝ)^k := by
  let N : ℝ := (2:ℝ)^k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  obtain ⟨hs1,hs2,hs3⟩ := G.thin_transfer_sum_bounds k hG u v L D hL hD he
  simp only [sq_abs] at hs2
  have h1n : 0 ≤ M*∑ e, |u e-v e| := by positivity
  have hh : -R ≤ a + M*(512*D*(2*L+D)/N^2) +
      (M*(512*D/N))*(M*(512*L^2)+1)+(M*(512*D/N))^2 := by
    apply htransfer.trans
    apply add_le_add
    · apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs3 hM)
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hs1 hM)
          (add_le_add (mul_le_mul_of_nonneg_left hs2 hM) le_rfl) (by positivity) (by positivity)
    · exact pow_le_pow_left₀ h1n (mul_le_mul_of_nonneg_left hs1 hM) 2
  apply hh.trans
  rw [add_assoc a, add_assoc a]
  apply add_le_add le_rfl
  have hN2 : N ≤ N^2 := by nlinarith
  have hQ : 0 ≤ M*(512*D*(2*L+D))+(M*512*D)^2 := by positivity
  calc _ = (M*(512*D*(2*L+D))+(M*512*D)^2)/N^2+
        ((M*512*D)*(M*(512*L^2)+1))/N := by ring
    _ ≤ (M*(512*D*(2*L+D))+(M*512*D)^2)/N+
        ((M*512*D)*(M*(512*L^2)+1))/N :=
      add_le_add (div_le_div_of_nonneg_left hQ hN hN2) le_rfl
    _ = _ := by unfold transferCostConstant; dsimp only [N]; ring


end LatticeGraph
end
end RP2.Fourier
