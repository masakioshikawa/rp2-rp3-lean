module

public import RP3.FourierAll
public import RP3.Fourier.ModelModes
public import RP3.QuadraticFamily

public section

/-! Truncated Fourier families for thin annuli. The low shells are represented
by zero modes, retaining the existing finite index and its exact symmetries. -/
namespace RP3.Fourier
noncomputable section
open scoped BigOperators ComplexConjugate

variable {k : ℕ}

@[expose] def tailWeight (h : ℕ) (p : DyadicFreq k) : ℝ :=
  if h ≤ p.1.val then dyadicWeight p else 0

@[expose] def tailReciprocal (h : ℕ) (p : DyadicFreq k) : ℝ :=
  if h ≤ p.1.val then 1 / (dyadicRadius p : ℝ) else 0

theorem tailWeight_nonneg (h : ℕ) (p : DyadicFreq k) : 0 ≤ tailWeight h p := by
  unfold tailWeight; split_ifs
  · exact (dyadicWeight_pos p).le
  · rfl

theorem tailWeight_le (h : ℕ) (p : DyadicFreq k) : tailWeight h p ≤ dyadicWeight p := by
  unfold tailWeight; split_ifs
  · rfl
  · exact (dyadicWeight_pos p).le

theorem tailWeight_sq (h : ℕ) (p : DyadicFreq k) :
    tailWeight h p ^ 2 = if h ≤ p.1.val then (1 / (dyadicRadius p : ℝ))^3 else 0 := by
  unfold tailWeight
  split_ifs <;> simp [dyadicWeight_sq]

theorem tailWeight_mul_sqrt (h : ℕ) (p : DyadicFreq k) :
    tailWeight h p * Real.sqrt (dyadicRadius p : ℝ) = tailReciprocal h p := by
  unfold tailWeight tailReciprocal
  split_ifs <;> simp [dyadicWeight_mul_sqrt]

theorem tailReciprocal_nonneg (h : ℕ) (p : DyadicFreq k) : 0 ≤ tailReciprocal h p := by
  unfold tailReciprocal; split_ifs <;> positivity

theorem tailReciprocal_le (h : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hh : 1 / (2:ℝ)^h ≤ δ) (p : DyadicFreq k) : tailReciprocal h p ≤ δ := by
  unfold tailReciprocal
  split_ifs with hp
  · apply le_trans _ hh
    have hr : (2:ℝ)^h ≤ (dyadicRadius p:ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by decide : 1 ≤ 2) hp
    exact one_div_le_one_div_of_le (by positivity) hr
  · exact hδ

@[expose] def tailLambda (k h : ℕ) : ℝ :=
  (2:ℝ)^k * ∑ p : DyadicFreq k,
    tailWeight h p ^ 2 * Real.sin (dyadicAngle k (dyadicPoint p).1)

theorem tailLambda_lower (k h : ℕ) : ((k-h:ℕ):ℝ)/2 ≤ tailLambda k h := by
  have hp (p : DyadicFreq k) :
      (if h ≤ p.1.val then (1/(dyadicRadius p:ℝ))^2/4 else 0) ≤
        (2:ℝ)^k*(tailWeight h p ^ 2*Real.sin (dyadicAngle k (dyadicPoint p).1)) := by
    rw [tailWeight_sq]
    split_ifs with hj
    · have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
      have hpr : (dyadicRadius p:ℝ) ≤ ((dyadicPoint p).1:ℝ) := by
        exact_mod_cast (dyadicPoint_bounds p).1
      have hs := dyadic_sin_lower k ((dyadicPoint p).1:ℝ) (by linarith) (dyadicPoint_fst_le_N p)
      calc _ = (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*((dyadicRadius p:ℝ)/(4*(2:ℝ)^k))) := by field_simp
           _ ≤ _ := by gcongr; exact (div_le_div_of_nonneg_right hpr (by positivity)).trans hs
    · simp
  have hs : (∑ j : Fin k, if h ≤ j.val then (1/2:ℝ) else 0) = ((k-h:ℕ):ℝ)/2 := by
    rw [← Finset.sum_range (fun j => if h ≤ j then (1/2:ℝ) else 0)]
    rw [← Finset.sum_filter]
    have hf : (Finset.range k).filter (fun j => h ≤ j) = Finset.Ico h k := by
      ext j; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
    rw [hf]
    simp [Nat.card_Ico, nsmul_eq_mul, div_eq_mul_inv]
  unfold tailLambda
  rw [Finset.mul_sum]
  calc _ = ∑ j : Fin k, if h ≤ j.val then (1/2:ℝ) else 0 := hs.symm
       _ ≤ ∑ p : DyadicFreq k, if h ≤ p.1.val then (1/(dyadicRadius p:ℝ))^2/4 else 0 := by
         rw [Fintype.sum_sigma]
         apply Finset.sum_le_sum
         intro j _
         by_cases hj : h ≤ j.val
         · simp only [hj, ↓reduceIte, dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
           have hr : (0:ℝ)<(2^j.val:ℕ) := by positivity
           have hc : 2*((2^j.val:ℕ):ℝ)^2 ≤ (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) := by
             exact_mod_cast (dyadic_shell_card_bounds j.val).1
           calc (1/2:ℝ) = (2*((2^j.val:ℕ):ℝ)^2)*((1/((2^j.val:ℕ):ℝ))^2/4) := by field_simp; norm_num
                _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
         · simp [hj]
       _ ≤ _ := Finset.sum_le_sum fun p _ => hp p

theorem tailLambda_lower_quarter (k h : ℕ) (hh : 2*h ≤ k) : (k:ℝ)/4 ≤ tailLambda k h := by
  have hc : k ≤ 2*(k-h) := by omega
  have hc' : (k:ℝ) ≤ 2*((k-h:ℕ):ℝ) := by exact_mod_cast hc
  exact le_trans (by linarith) (tailLambda_lower k h)

theorem tail_sin_cancel (k h : ℕ) :
    (∑ p : DyadicFreq k, tailWeight h p ^ 2 *
      Real.sin (dyadicAngle k (dyadicPoint p).2)) = 0 := by
  let e : DyadicFreq k ≃ DyadicFreq k :=
    ⟨dyadicReflect, dyadicReflect, dyadicReflect_involution, dyadicReflect_involution⟩
  have he := Equiv.sum_comp e
    (fun p : DyadicFreq k => tailWeight h p ^ 2 * Real.sin (dyadicAngle k (dyadicPoint p).2))
  have hw (p : DyadicFreq k) : tailWeight h (dyadicReflect p) = tailWeight h p := by
    rfl
  change (∑ p : DyadicFreq k, tailWeight h (dyadicReflect p) ^ 2 *
    Real.sin (dyadicAngle k (dyadicPoint (dyadicReflect p)).2)) = _ at he
  simp only [hw, dyadicReflect_point, Int.cast_neg, dyadicAngle_neg,
    Real.sin_neg, mul_neg, Finset.sum_neg_distrib] at he
  linarith

theorem tail_sine_main_sum (k h : ℕ) :
    (∑ p : DyadicFreq k, tailWeight h p ^ 2 * Real.sin (dyadicAngle k (dyadicPoint p).1)) =
      tailLambda k h/(2:ℝ)^k := by
  simp only [tailLambda]
  rw [mul_div_cancel_left₀ _ (by positivity : (2:ℝ)^k ≠ 0)]

theorem tail_grouped_sine_sum (h : ℕ) (m s j : Bool) :
    (∑ p : DyadicFreq k, tailWeight h p ^ 2 *
      Real.sin (dyadicAngle k (if j then (groupedPoint m s p).2 else (groupedPoint m s p).1))) =
      if m=j then (if s then -(tailLambda k h/(2:ℝ)^k) else tailLambda k h/(2:ℝ)^k) else 0 := by
  have h1 := tail_sine_main_sum k h
  have h2 := tail_sin_cancel k h
  cases m <;> cases s <;> cases j <;> simp_all [groupedPoint]

/-- The column energy is retained instead of bounded by the operator norm. -/
theorem SquareBound.gram_weighted_columns
    {X P : Type*} [Fintype X] [Fintype P] {U : X → P → ℂ} {a : ℝ}
    (h : SquareBound U a) (d : P → ℂ) :
    (∑ x, ∑ y, ‖∑ p, U x p*d p*conj (U y p)‖^2) ≤
      a^2*∑ p, ‖d p‖^2*(∑ y, ‖U y p‖^2) := by
  calc _ = ∑ y, ∑ x, ‖∑ p, U x p*(d p*conj (U y p))‖^2 := by
          simp only [mul_assoc]; exact Finset.sum_comm
       _ ≤ ∑ y, a^2*∑ p, ‖d p*conj (U y p)‖^2 :=
          Finset.sum_le_sum fun y _ => h (fun p => d p*conj (U y p))
       _ = _ := by
          simp only [norm_mul, Complex.norm_conj, mul_pow, Finset.mul_sum]
          rw [Finset.sum_comm]

theorem SquareBound.gram_weighted_column_bound
    {X P : Type*} [Fintype X] [Fintype P] {U : X → P → ℂ} {a J : ℝ}
    (h : SquareBound U a) (hc : ∀ p, (∑ y, ‖U y p‖^2) ≤ J) (d : P → ℂ) :
    (∑ x, ∑ y, ‖∑ p, U x p*d p*conj (U y p)‖^2) ≤
      a^2*J*∑ p, ‖d p‖^2 := by
  apply (h.gram_weighted_columns d).trans
  calc _ ≤ a^2*∑ p, ‖d p‖^2*J := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hc p) (sq_nonneg _)
       _ = _ := by rw [← Finset.sum_mul]; ring


@[expose] def thinLatticeMode (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (m s : Bool) (p : DyadicFreq k) (x : Site) : ℂ :=
  (tailWeight h p:ℂ) * (f m s (scaledSite k x):ℂ) *
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) x)

theorem thinLatticeMode_norm_bound (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (m s : Bool) (p : DyadicFreq k) (x : Site) (C : ℝ)
    (hC : 0 ≤ C) (hv : |f m s (scaledSite k x)| ≤ C) :
    ‖thinLatticeMode h f m s p x‖ ≤ dyadicWeight p*C := by
  simp only [thinLatticeMode, norm_mul, torusWave_norm, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (tailWeight_nonneg h p)]
  exact mul_le_mul (tailWeight_le h p) hv (abs_nonneg _) (dyadicWeight_pos p).le

theorem tailWave_multiplier_bound (h : ℕ) (m s j : Bool) (p : DyadicFreq k) :
    ‖(tailReciprocal h p:ℂ) *
      (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j))-1)‖ ≤
        Real.pi/(4*(2:ℝ)^k) := by
  unfold tailReciprocal
  split_ifs
  · simpa only [Complex.ofReal_div, Complex.ofReal_one] using groupedWave_multiplier_bound m s j p
  · simp only [Complex.ofReal_zero, zero_mul, norm_zero]; positivity

namespace LatticeGraph

@[expose] def thinModeGradient (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  thinLatticeMode h f m s p e.val.2.val-thinLatticeMode h f m s p e.val.1.val

@[expose] def thinScaledModeGradient (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (Real.sqrt (dyadicRadius p:ℝ):ℂ)*G.thinModeGradient h f m s p e

theorem thinScaledModeGradient_formula (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.thinScaledModeGradient h f m s p e =
      (tailReciprocal h p:ℂ) *
      ((f m s (scaledSite k e.val.2.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e))) -
       (f m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val)) := by
  have hw := congrArg Complex.ofReal (tailWeight_mul_sqrt h p)
  push_cast at hw
  simp only [thinScaledModeGradient, thinModeGradient, thinLatticeMode]
  rw [G.edge_step e, latticeTorus_add]
  linear_combination ( ((f m s (scaledSite k (e.val.1.val+latticeAxis (G.edgeDirection e))):ℂ)*
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)))) -
    ((f m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)) ) * hw

@[expose] def thinModeBlockConstant (C L δ : ℝ) : ℝ :=
  Real.sqrt (512*((L*δ)^2+C^2*(Real.pi/4)^2))

theorem thinScaledModes_direction_bound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (C L δ : ℝ)
    (hδ : 0 ≤ δ) (hh : 1/(2:ℝ)^h ≤ δ)
    (hval : ∀ m s z, |f m s z| ≤ C)
    (hLip : ∀ m s z w, |f m s w-f m s z| ≤ L*‖w-z‖)
    (m s j : Bool) :
    SquareBound (fun (e : G.DirectionalEdges j) (p : DyadicFreq k) =>
      G.thinScaledModeGradient h f m s p e.val) (thinModeBlockConstant C L δ) := by
  classical
  have hN : (2:ℝ)^k ≠ 0 := by positivity
  have hd (e : G.DirectionalEdges j) :
      ‖(f m s (scaledSite k e.val.val.2.val):ℂ)-
        (f m s (scaledSite k e.val.val.1.val):ℂ)‖ ≤ L/(2:ℝ)^k := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [G.scaled_edge_distance, div_eq_mul_inv, one_mul] using
      hLip m s (scaledSite k e.val.val.1.val) (scaledSite k e.val.val.2.val)
  have hv (e : G.DirectionalEdges j) :
      ‖(f m s (scaledSite k e.val.val.2.val):ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hval m s (scaledSite k e.val.val.2.val)
  have ha (p : DyadicFreq k) : ‖(tailReciprocal h p:ℂ)‖ ≤ δ := by
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tailReciprocal_nonneg h p)] using tailReciprocal_le h δ hδ hh p
  have hb := edge_cutoff_squareBound (groupedTorusPoint m s) (groupedTorusPoint_injective m s)
    (fun e : G.DirectionalEdges j => latticeTorus (16*2^k) e.val.val.1.val)
    (G.directional_torus_injective k hG j) (latticeTorus (16*2^k) (latticeAxis j))
    (fun e => (f m s (scaledSite k e.val.val.1.val):ℂ))
    (fun e => (f m s (scaledSite k e.val.val.2.val):ℂ))
    (fun p => (tailReciprocal h p:ℂ)) (L/(2:ℝ)^k) C δ (Real.pi/(4*(2:ℝ)^k))
    hd hv ha (tailWave_multiplier_bound h m s j)
  have hc : Real.sqrt (2*((16*2^k:ℕ):ℝ)^2*((L/(2:ℝ)^k)^2*δ^2+C^2*(Real.pi/(4*(2:ℝ)^k))^2)) =
      thinModeBlockConstant C L δ := by
    congr 1
    push_cast
    field_simp [hN]
    ring
  rw [hc] at hb
  have hdir (e : G.DirectionalEdges j) : G.edgeDirection e.val=j := e.property
  exact fun v => by simpa only [G.thinScaledModeGradient_formula, hdir] using hb v

theorem thinScaledModes_squareBound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (C L δ : ℝ)
    (hδ : 0 ≤ δ) (hh : 1/(2:ℝ)^h ≤ δ)
    (hval : ∀ m s z, |f m s z| ≤ C)
    (hLip : ∀ m s z w, |f m s w-f m s z| ≤ L*‖w-z‖) (m s : Bool) :
    SquareBound (fun e (p : DyadicFreq k) => G.thinScaledModeGradient h f m s p e)
      (2*thinModeBlockConstant C L δ) := by
  apply SquareBound.combine_directions _ G.edgeDirection
  exact fun j => G.thinScaledModes_direction_bound hG h f C L δ hδ hh hval hLip m s j


theorem thinScaledModeGradient_norm_le (G : LatticeGraph)
    (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (C L δ : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hh : 1/(2:ℝ)^h ≤ δ)
    (hval : ∀ m s z, |f m s z| ≤ C)
    (hLip : ∀ m s z w, |f m s w-f m s z| ≤ L*‖w-z‖)
    (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    ‖G.thinScaledModeGradient h f m s p e‖ ≤ (L*δ+C*(Real.pi/4))/(2:ℝ)^k := by
  let W := torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)
  let Z := torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)))
  let f₀ := f m s (scaledSite k e.val.1.val)
  let f₁ := f m s (scaledSite k e.val.2.val)
  have heq : G.thinScaledModeGradient h f m s p e =
      (tailReciprocal h p:ℂ)*((f₁-f₀:ℝ):ℂ)*W +
      (f₁:ℂ)*W*((tailReciprocal h p:ℂ)*(Z-1)) := by
    rw [G.thinScaledModeGradient_formula, torusWave_add]
    dsimp only [W, Z, f₀, f₁]
    push_cast
    ring
  have hd : |f₁-f₀| ≤ L/(2:ℝ)^k := by
    simpa only [f₀, f₁, G.scaled_edge_distance, div_eq_mul_inv, one_mul] using
      hLip m s (scaledSite k e.val.1.val) (scaledSite k e.val.2.val)
  have hw : ‖W‖=1 := torusWave_norm _ _
  rw [heq]
  calc _ ≤ ‖(tailReciprocal h p:ℂ)*((f₁-f₀:ℝ):ℂ)*W‖ +
      ‖(f₁:ℂ)*W*((tailReciprocal h p:ℂ)*(Z-1))‖ := norm_add_le _ _
       _ = tailReciprocal h p*|f₁-f₀| + |f₁| *‖(tailReciprocal h p:ℂ)*(Z-1)‖ := by
         simp only [norm_mul, hw, mul_one, Complex.norm_real, Real.norm_eq_abs,
           abs_of_nonneg (tailReciprocal_nonneg h p)]
       _ ≤ δ*(L/(2:ℝ)^k)+C*(Real.pi/(4*(2:ℝ)^k)) :=
         add_le_add (mul_le_mul (tailReciprocal_le h δ hδ hh p) hd (abs_nonneg _) hδ)
           (mul_le_mul (hval m s _) (tailWave_multiplier_bound h m s (G.edgeDirection e) p)
             (norm_nonneg _) hC)
       _ = _ := by ring

/-- Only edges in the explicit support set contribute to a column. -/
theorem thinScaledModes_column_bound (G : LatticeGraph)
    (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (C L δ K : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hh : 1/(2:ℝ)^h ≤ δ)
    (hval : ∀ m s z, |f m s z| ≤ C)
    (hLip : ∀ m s z w, |f m s w-f m s z| ≤ L*‖w-z‖)
    (S : Finset G.edges) (hcount : (S.card:ℝ) ≤ K*(2:ℝ)^(2*k))
    (hsupport : ∀ e : G.edges, e ∉ S → ∀ m s,
      f m s (scaledSite k e.val.1.val)=0 ∧ f m s (scaledSite k e.val.2.val)=0)
    (m s : Bool) (p : DyadicFreq k) :
    (∑ e, ‖G.thinScaledModeGradient h f m s p e‖^2) ≤ K*(L*δ+C*(Real.pi/4))^2 := by
  classical
  have hz (e : G.edges) (he : e ∉ S) : G.thinScaledModeGradient h f m s p e=0 := by
    obtain ⟨hl,hr⟩ := hsupport e he m s
    simp [thinScaledModeGradient, thinModeGradient, thinLatticeMode, hl, hr]
  calc _ = ∑ e ∈ S, ‖G.thinScaledModeGradient h f m s p e‖^2 := by
          symm
          apply Finset.sum_subset (Finset.subset_univ S)
          intro e _ he
          simp [hz e he]
       _ ≤ ∑ _e ∈ S, ((L*δ+C*(Real.pi/4))/(2:ℝ)^k)^2 :=
          Finset.sum_le_sum fun e _ => pow_le_pow_left₀ (norm_nonneg _)
            (G.thinScaledModeGradient_norm_le h f C L δ hC hL hδ hh hval hLip m s p e) 2
       _ = (S.card:ℝ)*((L*δ+C*(Real.pi/4))/(2:ℝ)^k)^2 := by simp
       _ ≤ (K*(2:ℝ)^(2*k))*((L*δ+C*(Real.pi/4))/(2:ℝ)^k)^2 :=
          mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
       _ = _ := by rw [mul_comm 2 k, pow_mul]; field_simp

theorem thinMode_gradient_square_sum_le (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (J : ℝ)
    (hc : ∀ p : DyadicFreq k, (∑ e, ‖G.thinScaledModeGradient h f m s p e‖^2) ≤ J)
    (p : DyadicFreq k) :
    (∑ e, ‖G.thinModeGradient h f m s p e‖^2) ≤ J/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hd := hc p
  simp only [thinScaledModeGradient, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr.le] at hd
  rw [← Finset.mul_sum] at hd
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hd)

theorem thinMode_sup_square_le (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (p : DyadicFreq k)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ z, |f m s z| ≤ C) :
    ‖(fun x : G.vertices => thinLatticeMode h f m s p x.val)‖^2 ≤ C^2*(1/(dyadicRadius p:ℝ))^3 := by
  have hnorm : ‖(fun x : G.vertices => thinLatticeMode h f m s p x.val)‖ ≤ dyadicWeight p*C := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (dyadicWeight_pos p).le hC)).mpr
    exact fun x => thinLatticeMode_norm_bound h f m s p x.val C hC (hv _)
  calc _ ≤ (dyadicWeight p*C)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
       _ = _ := by rw [mul_pow, dyadicWeight_sq]; ring
theorem thinMode_gram_reweight (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (e l : G.edges) :
    (∑ p : DyadicFreq k, G.thinScaledModeGradient h f m s p e*((1/(dyadicRadius p:ℝ)):ℂ)*
      conj (G.thinScaledModeGradient h f m s p l)) = ∑ p : DyadicFreq k,
        G.thinModeGradient h f m s p e*conj (G.thinModeGradient h f m s p l) := by
  apply Finset.sum_congr rfl
  intro p _
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : ((Real.sqrt (dyadicRadius p:ℝ):ℂ)*((1/(dyadicRadius p:ℝ)):ℂ)*
      (Real.sqrt (dyadicRadius p:ℝ):ℂ)) = 1 := by
    have hsreal : Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) = 1 := by
      rw [show Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) =
      (Real.sqrt (dyadicRadius p:ℝ))^2/(dyadicRadius p:ℝ) by ring, Real.sq_sqrt hr.le, div_self hr.ne']
    exact_mod_cast hsreal
  simp only [thinScaledModeGradient, map_mul, Complex.conj_ofReal]
  linear_combination G.thinModeGradient h f m s p e*conj (G.thinModeGradient h f m s p l)*hs


theorem thinMode_group_gram_bound (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (a J : ℝ) (hJ : 0 ≤ J)
    (hb : SquareBound (fun e (p : DyadicFreq k) => G.thinScaledModeGradient h f m s p e) a)
    (hc : ∀ p : DyadicFreq k, (∑ e, ‖G.thinScaledModeGradient h f m s p e‖^2) ≤ J) :
    (∑ e, ∑ l, ‖∑ p : DyadicFreq k, G.thinModeGradient h f m s p e*conj (G.thinModeGradient h f m s p l)‖^2)
      ≤ 3*a^2*J*(k:ℝ) := by
  have hh := hb.gram_weighted_column_bound hc (fun p => ((1/(dyadicRadius p:ℝ)):ℂ))
  simp_rw [G.thinMode_gram_reweight h f] at hh
  have he (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖^2 = (1/(dyadicRadius p:ℝ))^2 := by
    have hr : (0:ℝ) ≤ dyadicRadius p := by positivity
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  simp_rw [he] at hh
  have hx := mul_le_mul_of_nonneg_left (dyadic_inverse_square_sum k)
    (by positivity : 0≤a^2*J)
  exact hh.trans (by nlinarith)

@[expose] def thinModes (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (i : ModeIndex k) (x : G.vertices) : ℂ := thinLatticeMode h f i.1.1 i.1.2 i.2 x.val

@[expose] def thinModeDifferences (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (i : ModeIndex k) (e : G.edges) : ℂ := G.thinModeGradient h f i.1.1 i.1.2 i.2 e

theorem thinModes_HS_bound (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (a J : ℝ) (hJ : 0 ≤ J)
    (hb : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.thinScaledModeGradient h f m s p e) a)
    (hc : ∀ m s (p : DyadicFreq k), (∑ e, ‖G.thinScaledModeGradient h f m s p e‖^2) ≤ J) :
    familyHSSquare (G.thinModeDifferences (k := k) h f) ≤ 48*a^2*J*(k:ℝ) := by
  unfold familyHSSquare rowSquare familyKernel thinModeDifferences
  simp only [Fintype.sum_prod_type]
  have hh := gram_groups_bound
    (fun (i : Bool × Bool) e l => ∑ p : DyadicFreq k,
      G.thinModeGradient h f i.1 i.2 p e*conj (G.thinModeGradient h f i.1 i.2 p l))
    (3*a^2*J*(k:ℝ)) (fun i => G.thinMode_group_gram_bound h f i.1 i.2 a J hJ (hb i.1 i.2) (hc i.1 i.2))
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    show ((2:ℝ)*2)^2*(3*a^2*J*(k:ℝ)) = 48*a^2*J*(k:ℝ) by ring] using hh
theorem thinModes_min_bound (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (J C : ℝ) (hJ : 0 ≤ J) (hC : 0 ≤ C)
    (hv : ∀ m s z, |f m s z| ≤ C)
    (hc : ∀ m s (p : DyadicFreq k), (∑ e, ‖G.thinScaledModeGradient h f m s p e‖^2) ≤ J) :
    (∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.thinModes h f i‖^2*∑ e, ‖G.thinModeDifferences h f j e‖^2)
          (‖G.thinModes h f j‖^2*∑ e, ‖G.thinModeDifferences h f i e‖^2)) ≤ 576*C^2*J*(k:ℝ) := by
  have hv' (i : ModeIndex k) : ‖G.thinModes h f i‖^2 ≤ C^2*(1/(dyadicRadius i.2:ℝ))^3 :=
    G.thinMode_sup_square_le h f i.1.1 i.1.2 i.2 C hC (hv i.1.1 i.1.2)
  have hd' (i : ModeIndex k) : (∑ e, ‖G.thinModeDifferences h f i e‖^2) ≤ J/(dyadicRadius i.2:ℝ) :=
    G.thinMode_gradient_square_sum_le h f i.1.1 i.1.2 J (hc i.1.1 i.1.2) i.2
  have hm (i j : ModeIndex k) :
      min (‖G.thinModes h f i‖^2*∑ e, ‖G.thinModeDifferences h f j e‖^2)
          (‖G.thinModes h f j‖^2*∑ e, ‖G.thinModeDifferences h f i e‖^2) ≤
      C^2*J*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                 ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg (sq_nonneg _) hJ)]
    apply min_le_min
    · calc _ ≤ (C^2*(1/(dyadicRadius i.2:ℝ))^3)*(J/(dyadicRadius j.2:ℝ)) :=
            mul_le_mul (hv' i) (hd' j) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
    · calc _ ≤ (C^2*(1/(dyadicRadius j.2:ℝ))^3)*(J/(dyadicRadius i.2:ℝ)) :=
            mul_le_mul (hv' j) (hd' i) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
  calc _ ≤ ∑ i : ModeIndex k, ∑ j : ModeIndex k,
        C^2*J*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                   ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) :=
           Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hm i j
       _ = 16*C^2*J*∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
           min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
               ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ))) := by
          simp only [ModeIndex, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
          ring
       _ ≤ _ := by
          have hd := mul_le_mul_of_nonneg_left (dyadic_min_cost_sum k)
            (by positivity : 0 ≤ 16*C^2*J)
          nlinarith

@[expose] def thinModeCommutator (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (thinLatticeMode h f m s p e.val.1.val*conj (thinLatticeMode h f m s p e.val.2.val)-
    conj (thinLatticeMode h f m s p e.val.1.val)*thinLatticeMode h f m s p e.val.2.val)/2

@[expose] def thinProfileEdge (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (k : ℕ) (e : G.edges) : ℝ :=
  (1/(2:ℝ)^k)*(f (G.edgeDirection e) false (scaledSite k e.val.1.val)*
    f (G.edgeDirection e) false (scaledSite k e.val.2.val)-
    f (G.edgeDirection e) true (scaledSite k e.val.1.val)*
    f (G.edgeDirection e) true (scaledSite k e.val.2.val))

theorem thinModeCommutator_formula (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.thinModeCommutator h f m s p e = -Complex.I *
      ((f m s (scaledSite k e.val.1.val)*f m s (scaledSite k e.val.2.val)*
        ((tailWeight h p)^2*Real.sin (dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))):ℝ):ℂ) := by
  have hy : thinLatticeMode h f m s p e.val.2.val =
      (((tailWeight h p*f m s (scaledSite k e.val.2.val)):ℝ):ℂ)*
        torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)*
        Complex.exp (Complex.I*((dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℝ):ℂ)) := by
    unfold thinLatticeMode
    rw [show latticeTorus (16*2^k) e.val.2.val = latticeTorus (16*2^k) e.val.1.val+
      latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)) by rw [G.edge_step e,latticeTorus_add],
      torusWave_add, groupedWave_axis_sine]
    push_cast
    ring
  have hh := wave_commutator (tailWeight h p)
    (f m s (scaledSite k e.val.1.val)) (f m s (scaledSite k e.val.2.val))
    (dyadicAngle k (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))
    (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val))
    (torusWave_norm _ _)
  unfold thinModeCommutator
  rw [hy]
  simp only [thinLatticeMode, Complex.ofReal_mul] at hh ⊢
  linear_combination hh

theorem thinMode_group_commutator (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (m s : Bool) (e : G.edges) :
    (∑ p : DyadicFreq k, G.thinModeCommutator h f m s p e) = -Complex.I*
      ((f m s (scaledSite k e.val.1.val)*f m s (scaledSite k e.val.2.val)*
        (if m=G.edgeDirection e then (if s then -(tailLambda k h/(2:ℝ)^k) else tailLambda k h/(2:ℝ)^k) else 0):ℝ):ℂ) := by
  simp only [G.thinModeCommutator_formula h f, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [tail_grouped_sine_sum]

theorem thinModes_commutator (G : LatticeGraph) (h : ℕ) (f : Bool → Bool → ℝ × ℝ → ℝ) (e : G.edges) :
    (∑ i : ModeIndex k, G.thinModeCommutator h f i.1.1 i.1.2 i.2 e) =
      -Complex.I*((tailLambda k h*G.thinProfileEdge h f k e:ℝ):ℂ) := by
  simp only [Fintype.sum_prod_type, G.thinMode_group_commutator h f, Fintype.sum_bool]
  cases h : G.edgeDirection e <;>
    simp [thinProfileEdge, h]
  all_goals ring



theorem thinModes_zero_pins (G : LatticeGraph) (h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (P : G.vertices → Option RP3.Spin)
    (hP : ∀ x s, P x=some s → ∀ m t, f m t (scaledSite k x.val)=0)
    (i : ModeIndex k) (x : G.vertices) (s : RP3.Spin) (hs : P x=some s) :
    G.thinModes h f i x=0 := by
  simp [thinModes, thinLatticeMode, hP x s hs i.1.1 i.1.2]

theorem system_thinModes_commutator (G : LatticeGraph) (k h : ℕ)
    (f : Bool → Bool → ℝ × ℝ → ℝ) (b : G.edges → ℝ)
    (P : G.vertices → Option RP3.Spin) :
    (∑ i : ModeIndex k, (G.spinSystem b P).commutatorForm (G.thinModes h f i)
      (fun x => conj (G.thinModes h f i x))) =
      (fun e => -Complex.I*((tailLambda k h*G.thinProfileEdge h f k e:ℝ):ℂ)) := by
  ext e
  rw [Finset.sum_apply]
  convert G.thinModes_commutator h f e using 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [RP3.Quadratic.SpinSystem.commutatorForm, RP3.Quadratic.SpinSystem.complexCross,
    Pi.smul_apply, smul_eq_mul, spinSystem, thinModes, thinModeCommutator]
  ring

@[expose] def thinRotationCost (M C a J : ℝ) : ℝ :=
  16*((6*M^2+4*M*Real.sqrt M+M)*(48*a^2*J)+M*(576*C^2*J))

theorem thinRotationCost_nonneg (M C a J : ℝ) (hM : 0 ≤ M) (hJ : 0 ≤ J) :
    0 ≤ thinRotationCost M C a J := by unfold thinRotationCost; positivity

/-- Actual pinned RP³ response for a low-frequency-truncated family. All
analytic hypotheses concern explicit profiles or their finite Fourier matrix. -/
theorem thin_profile_response_bound (G : LatticeGraph) (k h : ℕ)
    (hk : 0 < k) (hh : 2*h ≤ k) (β : ℝ) (hβ : 0 ≤ β)
    (b : G.edges → ℝ) (hb : ∀ e, |b e| ≤ β)
    (P : G.vertices → Option RP3.Spin) (f : Bool → Bool → ℝ × ℝ → ℝ)
    (hP : ∀ x s, P x=some s → ∀ m t, f m t (scaledSite k x.val)=0)
    (C a J : ℝ) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hv : ∀ m s z, |f m s z| ≤ C)
    (hsb : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.thinScaledModeGradient h f m s p e) a)
    (hcol : ∀ m s (p : DyadicFreq k), (∑ e, ‖G.thinScaledModeGradient h f m s p e‖^2) ≤ J) :
    -(G.spinSystem b P).secondAxisResponse (G.thinProfileEdge h f k) (G.thinProfileEdge h f k) ≤
      thinRotationCost (16*β) C a J/(k:ℝ) := by
  have hfam := (G.spinSystem b P).rotation_family_bound β hβ hb (G.thinModes (k := k) h f)
    (fun i x s hs => G.thinModes_zero_pins h f P hP i x s hs)
  have hd : (fun i : ModeIndex k => (G.spinSystem b P).edgeGradient (G.thinModes h f i)) =
      G.thinModeDifferences h f := rfl
  rw [G.system_thinModes_commutator k h f b P,
    (G.spinSystem b P).response_imaginary_multiple, hd] at hfam
  have hde (i : ModeIndex k) (e : G.edges) :
      (G.spinSystem b P).edgeGradient (G.thinModes h f i) e = G.thinModeDifferences h f i e := rfl
  simp only [hde] at hfam
  let M := 16*β
  let T := (6*M^2+4*M*Real.sqrt M+M)*(48*a^2*J)+M*(576*C^2*J)
  let R := (G.spinSystem b P).secondAxisResponse (G.thinProfileEdge h f k) (G.thinProfileEdge h f k)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hLam := tailLambda_lower_quarter k h hh
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hLp : 0 < tailLambda k h := by linarith
  have hHS := G.thinModes_HS_bound h f a J hJ hsb hcol
  have hmin := G.thinModes_min_bound h f J C hJ hC hv hcol
  have hcoef : 0 ≤ 6*M^2+4*M*Real.sqrt M+M := by positivity
  have hmin0 : 0 ≤ ∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.thinModes h f i‖^2*∑ e, ‖G.thinModeDifferences h f j e‖^2)
          (‖G.thinModes h f j‖^2*∑ e, ‖G.thinModeDifferences h f i e‖^2) := by positivity
  have hfamily : -(tailLambda k h)^2*R ≤ T*(k:ℝ) := by
    have hcost : (6*M^2+4*M*Real.sqrt M+M)*familyHSSquare (G.thinModeDifferences (k := k) h f)+
      M*(∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.thinModes h f i‖^2*∑ e, ‖G.thinModeDifferences h f j e‖^2)
          (‖G.thinModes h f j‖^2*∑ e, ‖G.thinModeDifferences h f i e‖^2)) ≤ T*(k:ℝ) := by
      calc _ ≤ (6*M^2+4*M*Real.sqrt M+M)*(48*a^2*J*(k:ℝ))+M*(576*C^2*J*(k:ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hHS hcoef) (mul_le_mul_of_nonneg_left hmin hM)
        _ = _ := by dsimp only [T]; ring
    apply le_trans _ hcost
    simpa only [R, M, neg_mul] using hfam.trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (show 4*β ≤ 16*β by linarith) hmin0))
  change -R ≤ 16*T/(k:ℝ)
  by_cases hr : R ≤ 0
  · apply (le_div_iff₀ hkR).mpr
    have hsq : (k:ℝ)^2/16 ≤ (tailLambda k h)^2 := by nlinarith
    have hx := mul_le_mul_of_nonneg_right hsq (neg_nonneg.mpr hr)
    nlinarith
  · have hx : 0 ≤ 16*T/(k:ℝ) := by positivity
    linarith

end LatticeGraph
end
end RP3.Fourier
