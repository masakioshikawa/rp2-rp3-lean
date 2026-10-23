module

public import RP3.MathlibImports

public section

/-! Pure Fourier/lattice estimates, concatenated for economical compilation. -/

/-! Module: RP3.Fourier.KernelDefs -/

namespace RP3.Fourier
noncomputable section
universe uI uE
open scoped BigOperators ComplexConjugate
variable {I : Type uI} {E : Type uE} [Fintype I] [Fintype E]

@[expose] def familyKernel (u : I → E → ℂ) (e l : E) : ℂ := ∑ i, u i e * conj (u i l)

@[expose] def rowSquare (u : I → E → ℂ) (e : E) : ℝ := ∑ l, ‖familyKernel u e l‖^2

@[expose] def familyHSSquare (u : I → E → ℂ) : ℝ := ∑ e, rowSquare u e

omit [Fintype E] in
@[simp] theorem familyKernel_conj (u : I → E → ℂ) (e l : E) :
    familyKernel (fun i e => conj (u i e)) e l = conj (familyKernel u e l) := by
  simp [familyKernel]

theorem rowSquare_nonneg (u : I → E → ℂ) (e : E) : 0 ≤ rowSquare u e :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem familyHSSquare_nonneg (u : I → E → ℂ) : 0 ≤ familyHSSquare u :=
  Finset.sum_nonneg fun e _ => rowSquare_nonneg u e

theorem kernel_diag_sq_le_row (u : I → E → ℂ) (e : E) :
    ‖familyKernel u e e‖^2 ≤ rowSquare u e :=
  Finset.single_le_sum (fun l _ => sq_nonneg ‖familyKernel u e l‖) (Finset.mem_univ e)

theorem kernel_diag_norm_le_sqrt (u : I → E → ℂ) (e : E) :
    ‖familyKernel u e e‖ ≤ Real.sqrt (rowSquare u e) :=
  Real.le_sqrt_of_sq_le (kernel_diag_sq_le_row u e)


end
end RP3.Fourier

/-! Module: RP3.Fourier.Geometry -/

namespace RP3.Fourier

abbrev Site := ℤ × ℤ

@[expose] def PositiveNeighbor (x y : Site) : Prop :=
  (y.1 = x.1 + 1 ∧ y.2 = x.2) ∨ (y.1 = x.1 ∧ y.2 = x.2 + 1)

structure LatticeGraph where
  vertices : Finset Site
  edges : Finset (vertices × vertices)
  nearest : ∀ e ∈ edges, PositiveNeighbor e.1.val e.2.val

@[expose] noncomputable def siteDistance (x y : Site) : ℝ :=
  Real.sqrt (((x.1 : ℝ) - (y.1 : ℝ)) ^ 2 + ((x.2 : ℝ) - (y.2 : ℝ)) ^ 2)


end RP3.Fourier

/-! Module: RP3.Fourier.TorusFourier -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

universe uP

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Fourier

abbrev DiscreteTorus (L : ℕ) := ZMod L × ZMod L

@[expose] def torusWave {L : ℕ} [NeZero L] (p x : DiscreteTorus L) : ℂ :=
  ZMod.stdAddChar (p.1*x.1+p.2*x.2)

variable {L : ℕ} [NeZero L]

@[simp] theorem torusWave_norm (p x : DiscreteTorus L) : ‖torusWave p x‖ = 1 :=
  AddChar.norm_apply _ _

@[simp] theorem torusWave_add (p x y : DiscreteTorus L) :
    torusWave p (x+y) = torusWave p x * torusWave p y := by
  unfold torusWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  ring

@[simp] theorem torusWave_zero (p : DiscreteTorus L) : torusWave p 0 = 1 := by
  simp [torusWave]

@[simp] theorem torusWave_conj (p x : DiscreteTorus L) :
    conj (torusWave p x) = torusWave (-p) x := by
  unfold torusWave
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp only [Prod.fst_neg, Prod.snd_neg]
  ring

theorem torusWave_mul_conj (p q x : DiscreteTorus L) :
    torusWave p x*conj (torusWave q x) = torusWave (p-q) x := by
  rw [torusWave_conj]
  unfold torusWave
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.fst_neg, Prod.snd_neg]
  ring

theorem sum_stdAddChar_mul (t : ZMod L) :
    (∑ i : ZMod L, ZMod.stdAddChar (t*i)) = if t=0 then (L:ℂ) else 0 := by
  classical
  split_ifs with h
  · simp [h]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L h)

theorem sum_torusWave (p : DiscreteTorus L) :
    (∑ x : DiscreteTorus L, torusWave p x) = if p=0 then (L:ℂ)^2 else 0 := by
  classical
  simp only [torusWave, Fintype.sum_prod_type, AddChar.map_add_eq_mul]
  rw [← Finset.sum_mul_sum, sum_stdAddChar_mul, sum_stdAddChar_mul]
  by_cases h1 : p.1=0 <;> by_cases h2 : p.2=0 <;>
    simp [h1, h2, Prod.ext_iff, pow_two]

theorem torusWave_orthogonal (p q : DiscreteTorus L) :
    (∑ x : DiscreteTorus L, torusWave p x*conj (torusWave q x)) =
      if p=q then ((L:ℝ)^2 : ℂ) else 0 := by
  simp only [torusWave_mul_conj, sum_torusWave, sub_eq_zero,
    Complex.ofReal_natCast]

theorem torusWave_orthogonal_subfamily {P : Type uP} [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p) (i j : P) :
    (∑ x : DiscreteTorus L, torusWave (p i) x*conj (torusWave (p j) x)) =
      if i=j then ((L:ℝ)^2 : ℂ) else 0 := by
  simp only [torusWave_orthogonal, hp.eq_iff]

theorem torusWave_intCast (p x : ℤ × ℤ) :
    torusWave (L := L) ((p.1:ZMod L),(p.2:ZMod L)) ((x.1:ZMod L),(x.2:ZMod L)) =
      Complex.exp (Complex.I * ((2*Real.pi*((p.1:ℝ)*(x.1:ℝ)+(p.2:ℝ)*(x.2:ℝ))/(L:ℝ)):ℂ)) := by
  unfold torusWave
  simp only [← Int.cast_mul, ← Int.cast_add]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem norm_stdAddChar_intCast_sub_one (p : ℤ) :
    ‖ZMod.stdAddChar (p : ZMod L)-1‖ ≤ (2*Real.pi/(L:ℝ))*|(p:ℝ)| := by
  rw [ZMod.stdAddChar_coe]
  have he : (2*Real.pi*Complex.I*(p:ℂ)/(L:ℂ)) =
      Complex.I*((2*Real.pi/(L:ℝ)*(p:ℝ):ℝ):ℂ) := by push_cast; ring
  rw [he]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi/(L:ℝ)*(p:ℝ))).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg]
  positivity

theorem torus_mode_difference (φ : DiscreteTorus L → ℂ) (p x h : DiscreteTorus L) :
    φ (x+h)*torusWave p (x+h)-φ x*torusWave p x =
      (φ (x+h)-φ x)*torusWave p x +
        φ (x+h)*torusWave p x*(torusWave p h-1) := by
  rw [torusWave_add]
  ring

end Fourier

end

end RP3

/-! Module: RP3.Fourier.DyadicFourier -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier

abbrev DyadicFreq (k : ℕ) := Σ j : Fin k, Fin (2^j.val) × Fin (2*2^j.val+1)

@[expose] def dyadicRadius {k : ℕ} (p : DyadicFreq k) : ℕ := 2^p.1.val

@[expose] def dyadicPoint {k : ℕ} (p : DyadicFreq k) : ℤ × ℤ :=
  ((dyadicRadius p : ℤ)+p.2.1.val, (p.2.2.val:ℤ)-dyadicRadius p)

theorem dyadicRadius_pos {k : ℕ} (p : DyadicFreq k) : 0 < dyadicRadius p := by
  unfold dyadicRadius
  positivity

theorem dyadicRadius_le {k : ℕ} (p : DyadicFreq k) : dyadicRadius p ≤ 2^k := by
  exact Nat.pow_le_pow_right (by decide) p.1.isLt.le

theorem dyadicPoint_bounds {k : ℕ} (p : DyadicFreq k) :
    (dyadicRadius p:ℤ) ≤ (dyadicPoint p).1 ∧ (dyadicPoint p).1 < 2*dyadicRadius p ∧
      -(dyadicRadius p:ℤ) ≤ (dyadicPoint p).2 ∧ (dyadicPoint p).2 ≤ dyadicRadius p := by
  have h1 := p.2.1.isLt
  have h2 := p.2.2.isLt
  simp only [dyadicPoint, dyadicRadius]
  omega

theorem dyadicPoint_injective {k : ℕ} : Function.Injective (dyadicPoint (k := k)) := by
  intro p q he
  have hf := congrArg Prod.fst he
  have hs := congrArg Prod.snd he
  have hp := dyadicPoint_bounds p
  have hq := dyadicPoint_bounds q
  have hj : p.1 = q.1 := by
    apply Fin.ext
    by_contra h
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hr : 2*dyadicRadius p ≤ dyadicRadius q := by
        have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hlt)
        simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
      have hr' : (2*dyadicRadius p:ℤ) ≤ dyadicRadius q := by exact_mod_cast hr
      omega
    · have hr : 2*dyadicRadius q ≤ dyadicRadius p := by
        have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (Nat.succ_le_of_lt hgt)
        simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
      have hr' : (2*dyadicRadius q:ℤ) ≤ dyadicRadius p := by exact_mod_cast hr
      omega
  rcases p with ⟨j,a,b⟩
  rcases q with ⟨j',a',b'⟩
  dsimp only at hj
  subst j'
  have ha : a = a' := by apply Fin.ext; simp only [dyadicPoint, dyadicRadius] at hf; omega
  have hb : b = b' := by apply Fin.ext; simp only [dyadicPoint, dyadicRadius] at hs; omega
  subst a'; subst b'; rfl

theorem zmod_cast_inj_interval (L : ℕ) (c a b : ℤ)
    (ha : c ≤ a ∧ a < c+L) (hb : c ≤ b ∧ b < c+L)
    (he : (a:ZMod L) = (b:ZMod L)) : a=b := by
  have hh : ((a-c:ℤ):ZMod L) = ((b-c:ℤ):ZMod L) := by simpa only [Int.cast_sub] using congrArg (fun z : ZMod L => z-(c:ZMod L)) he
  have ha' : a-c ∈ Set.Ico (0:ℤ) L := by constructor <;> omega
  have hb' : b-c ∈ Set.Ico (0:ℤ) L := by constructor <;> omega
  have hz := CharP.intCast_injOn_Ico (R := ZMod L) L ha' hb' hh
  omega

@[expose] def dyadicTorusPoint {k : ℕ} (p : DyadicFreq k) : DiscreteTorus (16*2^k) :=
  (((dyadicPoint p).1:ZMod (16*2^k)), ((dyadicPoint p).2:ZMod (16*2^k)))

theorem dyadicTorusPoint_injective {k : ℕ} : Function.Injective (dyadicTorusPoint (k := k)) := by
  intro p q he
  apply dyadicPoint_injective
  apply Prod.ext
  · apply zmod_cast_inj_interval (16*2^k) 0 _ _
    · have hp := dyadicPoint_bounds p; have hr := dyadicRadius_le p; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · have hq := dyadicPoint_bounds q; have hr := dyadicRadius_le q; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.fst he
  · apply zmod_cast_inj_interval (16*2^k) (-(2^k:ℕ):ℤ) _ _
    · have hp := dyadicPoint_bounds p; have hr := dyadicRadius_le p; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · have hq := dyadicPoint_bounds q; have hr := dyadicRadius_le q; have hn : 0 < 2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.snd he

theorem dyadic_shell_card_bounds (j : ℕ) :
    2*(2^j)^2 ≤ Fintype.card (Fin (2^j) × Fin (2*2^j+1)) ∧
      Fintype.card (Fin (2^j) × Fin (2*2^j+1)) ≤ 3*(2^j)^2 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  have h : 1 ≤ 2^j := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  constructor <;> nlinarith

end Fourier

end

end RP3

/-! Module: RP3.Fourier.SmoothProfiles -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open Set Function
open scoped Topology ContDiff

namespace Fourier

@[expose] def thetaBump : ContDiffBump (0 : ℝ) := ⟨4/3, 5/3, by norm_num, by norm_num⟩
@[expose] def outerBump : ContDiffBump (0 : ℝ) := ⟨7/4, 15/8, by norm_num, by norm_num⟩
@[expose] def innerBump : ContDiffBump (0 : ℝ) := ⟨9/8, 5/4, by norm_num, by norm_num⟩

@[expose] def squareTheta (z : ℝ × ℝ) : ℝ := thetaBump z.1 * thetaBump z.2

@[expose] def squareCutoff (z : ℝ × ℝ) : ℝ :=
  outerBump z.1 * outerBump z.2 * (1-innerBump z.1*innerBump z.2)

@[expose] def squareGradient (m : Bool) (z : ℝ × ℝ) : ℝ :=
  if m then thetaBump z.1 * deriv thetaBump z.2 else deriv thetaBump z.1 * thetaBump z.2

@[expose] def squareProfile (m sign : Bool) (z : ℝ × ℝ) : ℝ :=
  if sign then (squareCutoff z-squareGradient m z)/2 else
    (squareCutoff z+squareGradient m z)/2

theorem thetaBump_one {x : ℝ} (hx : |x| ≤ 4/3) : thetaBump x = 1 := by
  apply thetaBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, thetaBump] using hx

theorem thetaBump_zero {x : ℝ} (hx : 5/3 ≤ |x|) : thetaBump x = 0 := by
  apply thetaBump.zero_of_le_dist
  simpa [Real.dist_eq, thetaBump] using hx

theorem thetaBump_deriv_zero_inner {x : ℝ} (hx : |x| ≤ 4/3) : deriv thetaBump x = 0 := by
  apply IsLocalMax.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [thetaBump_one hx]
  exact thetaBump.le_one

theorem thetaBump_deriv_zero_outer {x : ℝ} (hx : 5/3 ≤ |x|) : deriv thetaBump x = 0 := by
  apply IsLocalMin.deriv_eq_zero
  apply Filter.Eventually.of_forall
  intro y
  rw [thetaBump_zero hx]
  exact thetaBump.nonneg

theorem outerBump_one {x : ℝ} (hx : |x| ≤ 7/4) : outerBump x = 1 := by
  apply outerBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, outerBump] using hx

theorem outerBump_zero {x : ℝ} (hx : 15/8 ≤ |x|) : outerBump x = 0 := by
  apply outerBump.zero_of_le_dist
  simpa [Real.dist_eq, outerBump] using hx

theorem innerBump_one {x : ℝ} (hx : |x| ≤ 9/8) : innerBump x = 1 := by
  apply innerBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, innerBump] using hx

theorem innerBump_zero {x : ℝ} (hx : 5/4 ≤ |x|) : innerBump x = 0 := by
  apply innerBump.zero_of_le_dist
  simpa [Real.dist_eq, innerBump] using hx

theorem squareTheta_one (z : ℝ × ℝ) (hx : |z.1| ≤ 1) (hy : |z.2| ≤ 1) :
    squareTheta z = 1 := by
  rw [squareTheta, thetaBump_one (by linarith), thetaBump_one (by linarith), mul_one]

theorem squareTheta_zero (z : ℝ × ℝ) (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) :
    squareTheta z = 0 := by
  rcases h with hx | hy
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.1|)]
  · simp [squareTheta, thetaBump_zero (by linarith : 5/3 ≤ |z.2|)]

theorem squareCutoff_gradient (m : Bool) (z : ℝ × ℝ) :
    squareCutoff z * squareGradient m z = squareGradient m z := by
  cases m
  · simp only [squareGradient, Bool.false_eq_true, ↓reduceIte]
    by_cases hg : deriv thetaBump z.1 = 0
    · simp [hg]
    by_cases ht : thetaBump z.2 = 0
    · simp [ht]
    have hx : 4/3 < |z.1| ∧ |z.1| < 5/3 := by
      constructor
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_inner h))
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_outer h))
    have hy : |z.2| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |z.1| ≤ 7/4),
      outerBump_one (by linarith : |z.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |z.1|)]
  · simp only [squareGradient, ↓reduceIte]
    by_cases hg : deriv thetaBump z.2 = 0
    · simp [hg]
    by_cases ht : thetaBump z.1 = 0
    · simp [ht]
    have hy : 4/3 < |z.2| ∧ |z.2| < 5/3 := by
      constructor
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_inner h))
      · exact lt_of_not_ge (fun h => hg (thetaBump_deriv_zero_outer h))
    have hx : |z.1| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |z.1| ≤ 7/4),
      outerBump_one (by linarith : |z.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |z.2|)]

theorem squareProfile_squares (m : Bool) (z : ℝ × ℝ) :
    squareProfile m false z ^ 2 - squareProfile m true z ^ 2 = squareGradient m z := by
  simp only [squareProfile, Bool.false_eq_true, ↓reduceIte]
  have h := squareCutoff_gradient m z
  nlinarith

theorem squareProfile_zero_inner (m s : Bool) (z : ℝ × ℝ)
    (hx : |z.1| ≤ 1) (hy : |z.2| ≤ 1) : squareProfile m s z = 0 := by
  have hc : squareCutoff z = 0 := by
    simp [squareCutoff, innerBump_one (by linarith : |z.1| ≤ 9/8),
      innerBump_one (by linarith : |z.2| ≤ 9/8)]
  have hg : squareGradient m z = 0 := by
    cases m <;> simp [squareGradient,
      thetaBump_deriv_zero_inner (by linarith : |z.1| ≤ 4/3),
      thetaBump_deriv_zero_inner (by linarith : |z.2| ≤ 4/3)]
  cases s <;> simp [squareProfile, hc, hg]

theorem squareProfile_zero_outer (m s : Bool) (z : ℝ × ℝ)
    (h : 2 ≤ |z.1| ∨ 2 ≤ |z.2|) : squareProfile m s z = 0 := by
  have hc : squareCutoff z = 0 := by
    rcases h with hx | hy
    · simp [squareCutoff, outerBump_zero (by linarith : 15/8 ≤ |z.1|)]
    · simp [squareCutoff, outerBump_zero (by linarith : 15/8 ≤ |z.2|)]
  have hg : squareGradient m z = 0 := by
    rcases h with hx | hy
    · cases m <;> simp [squareGradient,
        thetaBump_zero (by linarith : 5/3 ≤ |z.1|),
        thetaBump_deriv_zero_outer (by linarith : 5/3 ≤ |z.1|)]
    · cases m <;> simp [squareGradient,
        thetaBump_zero (by linarith : 5/3 ≤ |z.2|),
        thetaBump_deriv_zero_outer (by linarith : 5/3 ≤ |z.2|)]
  cases s <;> simp [squareProfile, hc, hg]

theorem squareTheta_contDiff : ContDiff ℝ ∞ squareTheta := by
  exact (thetaBump.contDiff.comp contDiff_fst).mul (thetaBump.contDiff.comp contDiff_snd)

theorem squareCutoff_contDiff : ContDiff ℝ ∞ squareCutoff := by
  apply ((outerBump.contDiff.comp contDiff_fst).mul (outerBump.contDiff.comp contDiff_snd)).mul
  exact contDiff_const.sub ((innerBump.contDiff.comp contDiff_fst).mul (innerBump.contDiff.comp contDiff_snd))

theorem squareGradient_contDiff (m : Bool) : ContDiff ℝ ∞ (squareGradient m) := by
  have hd : ContDiff ℝ ∞ (deriv thetaBump) := (contDiff_infty_iff_deriv.mp (thetaBump.contDiff : ContDiff ℝ ∞ thetaBump)).2
  cases m
  · exact (hd.comp contDiff_fst).mul (thetaBump.contDiff.comp contDiff_snd)
  · exact (thetaBump.contDiff.comp contDiff_fst).mul (hd.comp contDiff_snd)

theorem squareProfile_contDiff (m s : Bool) : ContDiff ℝ ∞ (squareProfile m s) := by
  cases s
  · exact (squareCutoff_contDiff.add (squareGradient_contDiff m)).div_const 2
  · exact (squareCutoff_contDiff.sub (squareGradient_contDiff m)).div_const 2

theorem squareProfile_compact (m s : Bool) : HasCompactSupport (squareProfile m s) := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2))
  intro z hz
  apply squareProfile_zero_outer
  by_contra h
  push Not at h
  apply hz
  constructor <;> constructor <;> nlinarith [abs_le.mp h.1.le, abs_le.mp h.2.le]

end Fourier

end

end RP3

/-! Module: RP3.Fourier.SmoothBounds -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

universe uE uF

noncomputable section
open Set Function
open scoped ContDiff
namespace Fourier

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem compact_continuous_norm_bound {f : E → F} (hc : HasCompactSupport f) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C,hC⟩ := (hc.isCompact_range hf).isBounded.exists_norm_le
  exact ⟨max C 0, le_max_right _ _, fun x => (hC _ ⟨x,rfl⟩).trans (le_max_left _ _)⟩

theorem smooth_compact_lipschitz_bound {f : E → F}
    (hc : HasCompactSupport f) (hf : ContDiff ℝ ∞ f) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖f x‖ ≤ C) ∧
      (∀ x y, ‖f y-f x‖ ≤ C*‖y-x‖) := by
  obtain ⟨A,hA,hfA⟩ := compact_continuous_norm_bound hc hf.continuous
  obtain ⟨B,hB,hfB⟩ := compact_continuous_norm_bound (hc.fderiv ℝ)
    (hf.fderiv_right (m := ∞) (by simp)).continuous
  refine ⟨A+B, add_nonneg hA hB, fun x => (hfA x).trans (le_add_of_nonneg_right hB), ?_⟩
  intro x y
  calc ‖f y-f x‖ ≤ B*‖y-x‖ :=
        Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf.differentiable (by simp) z)
          (fun z _ => hfB z) convex_univ (mem_univ x) (mem_univ y)
       _ ≤ (A+B)*‖y-x‖ := by gcongr; exact le_add_of_nonneg_left hA

theorem scalar_lipschitz_of_deriv_bound (f f' : ℝ → ℝ) (C : ℝ)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hC : ∀ x, |f' x| ≤ C) (x y : ℝ) :
    |f y-f x| ≤ C*|y-x| := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hf z).hasDerivWithinAt) (fun z _ => hC z) convex_univ
      (mem_univ x) (mem_univ y)

theorem abs_sub_left_le_of_uIcc {x y z : ℝ} (hz : z ∈ uIcc x y) :
    |z-x| ≤ |y-x| := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr h)]
    linarith [hz.2]
  · rw [uIcc_of_ge h] at hz
    rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr h)]
    linarith [hz.1]

theorem first_remainder_bound (f f' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hL : ∀ x y, |f' y-f' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-f' x*(y-x)| ≤ C*|y-x|^2 := by
  let g := fun z => f z-f' x*z
  have hg (z : ℝ) : HasDerivAt g (f' z-f' x) z := by
    convert (hf z).sub ((hasDerivAt_id z).const_mul (f' x)) using 1 <;> first | rfl | ring
  have hb (z : ℝ) (hz : z ∈ uIcc x y) : |f' z-f' x| ≤ C*|y-x| :=
    (hL x z).trans (mul_le_mul_of_nonneg_left (abs_sub_left_le_of_uIcc hz) hC)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc x y) => (hg z).hasDerivWithinAt)
    (fun z hz => hb z hz) (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  change |g y-g x| ≤ _ at H
  convert H using 1
  · congr 1; ring
  · rw [Real.norm_eq_abs]; ring

theorem second_remainder_bound (f f' f'' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hL : ∀ x y, |f'' y-f'' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2| ≤ C*|y-x|^3 := by
  let g := fun z => f z-f' x*(z-x)-f'' x/2*(z-x)^2
  have hg (z : ℝ) : HasDerivAt g (f' z-f' x-f'' x*(z-x)) z := by
    have ht : HasDerivAt (fun t : ℝ => t-x) 1 z := (hasDerivAt_id z).sub_const x
    have hq := ((hf z).sub (ht.const_mul (f' x))).sub ((ht.pow 2).const_mul (f'' x/2))
    convert hq using 1; first | rfl | ring
  have hb (z : ℝ) (hz : z ∈ uIcc x y) : |f' z-f' x-f'' x*(z-x)| ≤ C*|y-x|^2 := by
    exact (first_remainder_bound f' f'' C hC hf' hL x z).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_le_of_uIcc hz) 2) hC)
  have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc x y) => (hg z).hasDerivWithinAt)
    (fun z hz => hb z hz) (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  change |g y-g x| ≤ _ at H
  convert H using 1
  · congr 1; ring
  · rw [Real.norm_eq_abs]; ring

theorem trapezoid_error_bound (f f' f'' : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hL : ∀ x y, |f'' y-f'' x| ≤ C*|y-x|) (x y : ℝ) :
    |f y-f x-(y-x)/2*(f' x+f' y)| ≤ 2*C*|y-x|^3 := by
  have h1 := second_remainder_bound f f' f'' C hC hf hf' hL x y
  have h2 := first_remainder_bound f' f'' C hC hf' hL x y
  have he : f y-f x-(y-x)/2*(f' x+f' y) =
      (f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2) -
        (y-x)/2*(f' y-f' x-f'' x*(y-x)) := by ring
  rw [he]
  calc _ ≤ |f y-f x-f' x*(y-x)-f'' x/2*(y-x)^2| +
        |(y-x)/2*(f' y-f' x-f'' x*(y-x))| := abs_sub _ _
       _ ≤ C*|y-x|^3+|y-x|/2*(C*|y-x|^2) := by
          rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
          gcongr
       _ ≤ _ := by nlinarith [mul_nonneg hC (pow_nonneg (abs_nonneg (y-x)) 3)]

end Fourier

end

end RP3

/-! Module: RP3.Fourier.ProfileEstimates -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open Set Function
open scoped ContDiff BigOperators
namespace Fourier

@[expose] def squareStep (m : Bool) (ε : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  if m then (z.1,z.2+ε) else (z.1+ε,z.2)

@[simp] theorem squareStep_distance (m : Bool) (ε : ℝ) (z : ℝ × ℝ) :
    ‖squareStep m ε z-z‖ = |ε| := by
  cases m <;> simp [squareStep, Prod.norm_def, Real.norm_eq_abs, abs_nonneg]

theorem profiles_uniform_bound : ∃ C : ℝ, 1 ≤ C ∧
    (∀ m s z, |squareProfile m s z| ≤ C) ∧
    (∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖) := by
  have he (m s : Bool) := smooth_compact_lipschitz_bound
    (squareProfile_compact m s) (squareProfile_contDiff m s)
  choose C hC hval hLip using he
  let M : ℝ := 1+∑ m, ∑ s, C m s
  have hsum : 0 ≤ ∑ m : Bool, ∑ s : Bool, C m s :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun s _ => hC m s
  have hCM (m s : Bool) : C m s ≤ M := by
    have hs := Finset.single_le_sum (fun t _ => hC m t) (Finset.mem_univ s)
    have hm : (∑ t : Bool, C m t) ≤ ∑ u : Bool, ∑ t : Bool, C u t := Finset.single_le_sum (fun t _ => Finset.sum_nonneg fun t' _ => hC t t') (Finset.mem_univ m)
    dsimp only [M]
    linarith
  refine ⟨M, by dsimp only [M]; linarith, fun m s z => (hval m s z).trans (hCM m s), ?_⟩
  intro m s z w
  exact (hLip m s z w).trans (mul_le_mul_of_nonneg_right (hCM m s) (norm_nonneg _))

theorem theta_trapezoid_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ,
    |thetaBump y-thetaBump x-(y-x)/2*(deriv thetaBump x+deriv thetaBump y)| ≤
      C*|y-x|^3 := by
  have hd : ContDiff ℝ ∞ (deriv thetaBump) :=
    (contDiff_infty_iff_deriv.mp (thetaBump.contDiff : ContDiff ℝ ∞ thetaBump)).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv thetaBump)) := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C,hC,_hval,hL⟩ := smooth_compact_lipschitz_bound
    (thetaBump.hasCompactSupport.deriv.deriv) hdd
  refine ⟨2*C, by positivity, fun x y => ?_⟩
  exact trapezoid_error_bound thetaBump (deriv thetaBump) (deriv (deriv thetaBump)) C hC
    (fun t => ((thetaBump.contDiff : ContDiff ℝ ∞ thetaBump).differentiable (by simp) t).hasDerivAt)
    (fun t => (hd.differentiable (by simp) t).hasDerivAt) hL x y

theorem squareCutoff_near_gradient (m : Bool) (z w : ℝ × ℝ)
    (h1 : |w.1-z.1| ≤ 1/16) (h2 : |w.2-z.2| ≤ 1/16)
    (hg : squareGradient m z ≠ 0) : squareCutoff w = 1 := by
  have ha1 : |w.1| ≤ |w.1-z.1|+|z.1| := by simpa only [sub_add_cancel] using (abs_add_le (w.1-z.1) z.1)
  have ha2 : |w.2| ≤ |w.2-z.2|+|z.2| := by simpa only [sub_add_cancel] using (abs_add_le (w.2-z.2) z.2)
  have hb1 : |z.1| ≤ |w.1-z.1|+|w.1| := by
    simpa only [sub_add_cancel, abs_sub_comm] using (abs_add_le (z.1-w.1) w.1)
  have hb2 : |z.2| ≤ |w.2-z.2|+|w.2| := by
    simpa only [sub_add_cancel, abs_sub_comm] using (abs_add_le (z.2-w.2) w.2)
  cases m
  · have hd : deriv thetaBump z.1 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have ht : thetaBump z.2 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have hx : 4/3 < |z.1| ∧ |z.1| < 5/3 := ⟨
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_inner h)),
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_outer h))⟩
    have hy : |z.2| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |w.1| ≤ 7/4),
      outerBump_one (by linarith : |w.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |w.1|)]
  · have hd : deriv thetaBump z.2 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have ht : thetaBump z.1 ≠ 0 := by intro h; apply hg; simp [squareGradient, h]
    have hy : 4/3 < |z.2| ∧ |z.2| < 5/3 := ⟨
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_inner h)),
      lt_of_not_ge (fun h => hd (thetaBump_deriv_zero_outer h))⟩
    have hx : |z.1| < 5/3 := lt_of_not_ge (fun h => ht (thetaBump_zero h))
    simp [squareCutoff, outerBump_one (by linarith : |w.1| ≤ 7/4),
      outerBump_one (by linarith : |w.2| ≤ 7/4), innerBump_zero (by linarith : 5/4 ≤ |w.2|)]

theorem squareProfile_product_difference (m : Bool) (z w : ℝ × ℝ)
    (h1 : |w.1-z.1| ≤ 1/16) (h2 : |w.2-z.2| ≤ 1/16) :
    squareProfile m false z*squareProfile m false w-
      squareProfile m true z*squareProfile m true w =
      (squareGradient m z+squareGradient m w)/2 := by
  have hzw : squareGradient m z*squareCutoff w = squareGradient m z := by
    by_cases hg : squareGradient m z=0
    · simp [hg]
    · rw [squareCutoff_near_gradient m z w h1 h2 hg, mul_one]
  have hwz : squareCutoff z*squareGradient m w = squareGradient m w := by
    by_cases hg : squareGradient m w=0
    · simp [hg]
    · rw [squareCutoff_near_gradient m w z (by simpa only [abs_sub_comm] using h1)
        (by simpa only [abs_sub_comm] using h2) hg, one_mul]
  simp only [squareProfile, Bool.false_eq_true, ↓reduceIte]
  nlinarith

theorem squareTheta_step_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : Bool) (z : ℝ × ℝ) (ε : ℝ),
    |ε| ≤ 1/16 →
    |squareTheta (squareStep m ε z)-squareTheta z-
      ε*(squareProfile m false z*squareProfile m false (squareStep m ε z)-
           squareProfile m true z*squareProfile m true (squareStep m ε z))| ≤ C*|ε|^3 := by
  obtain ⟨C,hC,hT⟩ := theta_trapezoid_bound
  refine ⟨C,hC,?_⟩
  intro m z ε hε
  have hp := squareProfile_product_difference m z (squareStep m ε z)
    (by cases m
        · simpa only [squareStep, Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left] using hε
        · simp [squareStep])
    (by cases m
        · simp [squareStep]
        · simpa only [squareStep, ↓reduceIte, add_sub_cancel_left] using hε)
  rw [hp]
  have hb (x : ℝ) : |thetaBump x| ≤ 1 := by rw [abs_of_nonneg thetaBump.nonneg]; exact thetaBump.le_one
  cases m
  · have h := hT z.1 (z.1+ε)
    simp only [add_sub_cancel_left] at h
    have he : squareTheta (squareStep false ε z)-squareTheta z-
        ε*((squareGradient false z+squareGradient false (squareStep false ε z))/2) =
        thetaBump z.2*(thetaBump (z.1+ε)-thetaBump z.1-ε/2*(deriv thetaBump z.1+deriv thetaBump (z.1+ε))) := by
      simp only [squareTheta, squareStep, squareGradient, Bool.false_eq_true, ↓reduceIte]
      ring
    rw [he, abs_mul]
    calc _ ≤ 1*(C*|ε|^3) := mul_le_mul (hb z.2) h (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _
  · have h := hT z.2 (z.2+ε)
    simp only [add_sub_cancel_left] at h
    have he : squareTheta (squareStep true ε z)-squareTheta z-
        ε*((squareGradient true z+squareGradient true (squareStep true ε z))/2) =
        thetaBump z.1*(thetaBump (z.2+ε)-thetaBump z.2-ε/2*(deriv thetaBump z.2+deriv thetaBump (z.2+ε))) := by
      simp only [squareTheta, squareStep, squareGradient, ↓reduceIte]
      ring
    rw [he, abs_mul]
    calc _ ≤ 1*(C*|ε|^3) := mul_le_mul (hb z.1) h (abs_nonneg _) (by norm_num)
         _ = _ := one_mul _

end Fourier

end

end RP3

/-! Module: RP3.Fourier.DyadicSine -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators
namespace Fourier

@[expose] def dyadicAngle (k : ℕ) (t : ℝ) : ℝ := 2*Real.pi*t/(16*(2:ℝ)^k)

@[expose] def dyadicLambda (k : ℕ) : ℝ :=
  (2:ℝ)^k * ∑ p : DyadicFreq k,
    (1/(dyadicRadius p:ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint p).1)

@[simp] theorem dyadicAngle_neg (k : ℕ) (t : ℝ) : dyadicAngle k (-t) = -dyadicAngle k t := by
  unfold dyadicAngle; ring

theorem dyadic_sin_lower (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hN : t ≤ (2:ℝ)^k) :
    t/(4*(2:ℝ)^k) ≤ Real.sin (dyadicAngle k t) := by
  have hpow : (0:ℝ) < 2^k := by positivity
  have ha : 0 ≤ dyadicAngle k t := by unfold dyadicAngle; positivity
  have hb : dyadicAngle k t ≤ Real.pi/2 := by
    unfold dyadicAngle
    rw [div_le_iff₀ (by positivity : (0:ℝ)<16*2^k)]
    nlinarith [Real.pi_pos, mul_le_mul_of_nonneg_left hN Real.pi_pos.le]
  have h := Real.mul_le_sin ha hb
  convert h using 1
  unfold dyadicAngle
  field_simp
  ring

theorem dyadicPoint_fst_le_N {k : ℕ} (p : DyadicFreq k) :
    ((dyadicPoint p).1:ℝ) ≤ (2:ℝ)^k := by
  have hr : 2*dyadicRadius p ≤ 2^k := by
    have hh := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) p.1.isLt
    simpa only [dyadicRadius, pow_succ, Nat.mul_comm] using hh
  have hp := (dyadicPoint_bounds p).2.1
  have hz : (dyadicPoint p).1 ≤ (2^k:ℕ) := by omega
  exact_mod_cast hz

theorem dyadicLambda_lower (k : ℕ) : (k:ℝ)/2 ≤ dyadicLambda k := by
  have hN : (0:ℝ)<2^k := by positivity
  have hp (p : DyadicFreq k) :
      (1/(dyadicRadius p:ℝ))^2/4 ≤
        (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*Real.sin (dyadicAngle k (dyadicPoint p).1)) := by
    have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
    have hpr : (dyadicRadius p:ℝ) ≤ ((dyadicPoint p).1:ℝ) := by exact_mod_cast (dyadicPoint_bounds p).1
    have hs := dyadic_sin_lower k ((dyadicPoint p).1:ℝ) (by linarith) (dyadicPoint_fst_le_N p)
    calc _ = (2:ℝ)^k*((1/(dyadicRadius p:ℝ))^3*((dyadicRadius p:ℝ)/(4*(2:ℝ)^k))) := by field_simp
         _ ≤ _ := by gcongr; exact (div_le_div_of_nonneg_right hpr (by positivity)).trans hs
  unfold dyadicLambda
  rw [Finset.mul_sum]
  calc _ ≤ ∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^2/4 := by
          rw [Fintype.sum_sigma]
          calc _ = ∑ _j : Fin k, (1/2:ℝ) := by simp; ring
               _ ≤ _ := by
                 apply Finset.sum_le_sum
                 intro j _
                 simp only [dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
                 have hr : (0:ℝ)<(2^j.val:ℕ) := by positivity
                 have hc : 2*((2^j.val:ℕ):ℝ)^2 ≤ (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) := by
                   exact_mod_cast (dyadic_shell_card_bounds j.val).1
                 calc (1/2:ℝ) = (2*((2^j.val:ℕ):ℝ)^2)*((1/((2^j.val:ℕ):ℝ))^2/4) := by field_simp; norm_num
                      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
       _ ≤ _ := Finset.sum_le_sum fun p _ => hp p

@[expose] def dyadicReflect {k : ℕ} (p : DyadicFreq k) : DyadicFreq k :=
  ⟨p.1, p.2.1, p.2.2.rev⟩

@[simp] theorem dyadicReflect_radius {k : ℕ} (p : DyadicFreq k) :
    dyadicRadius (dyadicReflect p) = dyadicRadius p := rfl

@[simp] theorem dyadicReflect_point {k : ℕ} (p : DyadicFreq k) :
    (dyadicPoint (dyadicReflect p)).2 = -(dyadicPoint p).2 := by
  simp only [dyadicPoint, dyadicReflect, dyadicRadius, Fin.val_rev]
  have h := p.2.2.isLt
  omega

@[simp] theorem dyadicReflect_involution {k : ℕ} (p : DyadicFreq k) :
    dyadicReflect (dyadicReflect p) = p := by
  simp [dyadicReflect]

theorem dyadic_sin_cancel (k : ℕ) :
    (∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^3 *
      Real.sin (dyadicAngle k (dyadicPoint p).2)) = 0 := by
  let e : DyadicFreq k ≃ DyadicFreq k := ⟨dyadicReflect, dyadicReflect, dyadicReflect_involution, dyadicReflect_involution⟩
  have he := Equiv.sum_comp e
    (fun p : DyadicFreq k => (1/(dyadicRadius p:ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint p).2))
  change (∑ p : DyadicFreq k, (1/(dyadicRadius (dyadicReflect p):ℝ))^3 * Real.sin (dyadicAngle k (dyadicPoint (dyadicReflect p)).2)) = _ at he
  simp only [dyadicReflect_radius, dyadicReflect_point,
    Int.cast_neg, dyadicAngle_neg, Real.sin_neg, mul_neg, Finset.sum_neg_distrib] at he
  linarith

end Fourier

end

end RP3

/-! Module: RP3.Fourier.LatticeGeometry -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators
namespace Fourier

@[expose] def latticeAxis (m : Bool) : Site := if m then (0,1) else (1,0)

@[expose] def latticeTorus (L : ℕ) (x : Site) : DiscreteTorus L := ((x.1:ZMod L),(x.2:ZMod L))

@[simp] theorem latticeTorus_add (L : ℕ) (x y : Site) :
    latticeTorus L (x+y) = latticeTorus L x+latticeTorus L y := by
  ext <;> simp [latticeTorus]

@[expose] def scaledSite (k : ℕ) (x : Site) : ℝ × ℝ :=
  ((x.1:ℝ)/(2:ℝ)^k, (x.2:ℝ)/(2:ℝ)^k)

@[simp] theorem scaledSite_add_axis (k : ℕ) (x : Site) (m : Bool) :
    scaledSite k (x+latticeAxis m) = squareStep m (1/(2:ℝ)^k) (scaledSite k x) := by
  cases m <;> ext <;> simp [scaledSite, latticeAxis, squareStep, add_div]

namespace LatticeGraph

@[expose] def edgeDirection (G : LatticeGraph) (e : G.edges) : Bool :=
  decide (e.val.2.val.1 = e.val.1.val.1)

theorem edge_step (G : LatticeGraph) (e : G.edges) :
    e.val.2.val = e.val.1.val+latticeAxis (G.edgeDirection e) := by
  rcases G.nearest e.val e.property with h | h
  · have hn : e.val.2.val.1 ≠ e.val.1.val.1 := by omega
    simp only [edgeDirection, decide_eq_false hn, latticeAxis, Bool.false_eq_true, ↓reduceIte]
    exact Prod.ext h.1 (by simpa using h.2)
  · simp only [edgeDirection, h.1, decide_true, latticeAxis, ↓reduceIte]
    exact Prod.ext (by simpa using h.1) h.2

abbrev DirectionalEdges (G : LatticeGraph) (m : Bool) := {e : G.edges // G.edgeDirection e=m}

theorem directional_origin_injective (G : LatticeGraph) (m : Bool) :
    Function.Injective (fun e : G.DirectionalEdges m => e.val.val.1) := by
  intro e f h
  change e.val.val.1 = f.val.val.1 at h
  have he := G.edge_step e.val
  have hf := G.edge_step f.val
  rw [e.property] at he
  rw [f.property] at hf
  have hy : e.val.val.2 = f.val.val.2 := by
    apply Subtype.ext
    rw [he, hf, h]
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext h hy

@[expose] def WithinDyadicBox (G : LatticeGraph) (k : ℕ) : Prop :=
  ∀ x : G.vertices, |x.val.1| ≤ 2*(2^k:ℕ) ∧ |x.val.2| ≤ 2*(2^k:ℕ)

theorem torus_site_injective (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) :
    Function.Injective (fun x : G.vertices => latticeTorus (16*2^k) x.val) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply zmod_cast_inj_interval (16*2^k) (-(2*(2^k:ℕ)):ℤ) _ _
    · have hx := abs_le.mp (hG x).1; have hN : 0<2^k := by positivity
      constructor <;> omega
    · have hy := abs_le.mp (hG y).1; have hN : 0<2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.fst h
  · apply zmod_cast_inj_interval (16*2^k) (-(2*(2^k:ℕ)):ℤ) _ _
    · have hx := abs_le.mp (hG x).2; have hN : 0<2^k := by positivity
      constructor <;> omega
    · have hy := abs_le.mp (hG y).2; have hN : 0<2^k := by positivity
      constructor <;> omega
    · exact congrArg Prod.snd h

theorem directional_torus_injective (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) (m : Bool) :
    Function.Injective (fun e : G.DirectionalEdges m => latticeTorus (16*2^k) e.val.val.1.val) :=
  (G.torus_site_injective k hG).comp (G.directional_origin_injective m)

theorem edge_card_bound (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k) :
    (Fintype.card G.edges:ℝ) ≤ 512*((2:ℝ)^k)^2 := by
  let i := fun e : G.edges => (G.edgeDirection e, latticeTorus (16*2^k) e.val.1.val)
  have hi : Function.Injective i := by
    intro e f h
    have hm : G.edgeDirection e = G.edgeDirection f := congrArg Prod.fst h
    have hx := (G.torus_site_injective k hG) (congrArg Prod.snd h)
    have he := G.edge_step e
    have hf := G.edge_step f
    have hy : e.val.2 = f.val.2 := by
      apply Subtype.ext
      rw [he,hf,hm,hx]
    apply Subtype.ext
    exact Prod.ext hx hy
  have hc := Fintype.card_le_of_injective i hi
  simp only [Fintype.card_prod, Fintype.card_bool, ZMod.card] at hc
  have hh : (Fintype.card G.edges:ℝ) ≤ 2*((16*(2:ℝ)^k)*(16*(2:ℝ)^k)) := by exact_mod_cast hc
  nlinarith

theorem scaled_edge_distance (G : LatticeGraph) (k : ℕ) (e : G.edges) :
    ‖scaledSite k e.val.2.val-scaledSite k e.val.1.val‖ = 1/(2:ℝ)^k := by
  rw [G.edge_step e, scaledSite_add_axis, squareStep_distance, abs_of_pos (by positivity)]

end LatticeGraph
end Fourier

end

end RP3

/-! Module: RP3.Fourier.DyadicModes -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier

variable {k : ℕ}

@[expose] def groupedPoint (m s : Bool) (p : DyadicFreq k) : ℤ × ℤ :=
  let q := if m then (dyadicPoint p).swap else dyadicPoint p
  if s then -q else q

@[expose] def groupedTorusPoint (m s : Bool) (p : DyadicFreq k) : DiscreteTorus (16*2^k) :=
  (((groupedPoint m s p).1:ZMod (16*2^k)), ((groupedPoint m s p).2:ZMod (16*2^k)))

@[expose] instance dyadicModulus_neZero (k : ℕ) : NeZero (16*2^k) := ⟨by positivity⟩

theorem groupedTorusPoint_injective (m s : Bool) :
    Function.Injective (groupedTorusPoint (k := k) m s) := by
  have hs := dyadicTorusPoint_injective (k := k)
  cases m <;> cases s <;> intro p q h <;> apply hs
  · exact h
  · simpa [groupedTorusPoint, groupedPoint, dyadicTorusPoint, Prod.ext_iff] using h
  · exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · have h' : (dyadicTorusPoint p).swap = (dyadicTorusPoint q).swap := by
      simpa [groupedTorusPoint, groupedPoint, dyadicTorusPoint, Prod.ext_iff] using h
    exact Prod.swap_injective h'

@[expose] def dyadicWeight (p : DyadicFreq k) : ℝ :=
  1/((dyadicRadius p:ℝ)*Real.sqrt (dyadicRadius p:ℝ))

theorem dyadicWeight_pos (p : DyadicFreq k) : 0 < dyadicWeight p := by
  have h : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  unfold dyadicWeight
  positivity

@[simp] theorem dyadicWeight_sq (p : DyadicFreq k) :
    dyadicWeight p^2 = (1/(dyadicRadius p:ℝ))^3 := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  unfold dyadicWeight
  rw [div_pow, mul_pow, Real.sq_sqrt hr.le]
  field_simp

@[simp] theorem dyadicWeight_mul_sqrt (p : DyadicFreq k) :
    dyadicWeight p*Real.sqrt (dyadicRadius p:ℝ) = 1/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : Real.sqrt (dyadicRadius p:ℝ) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  unfold dyadicWeight
  field_simp

theorem wave_commutator (a b c θ : ℝ) (w : ℂ) (hw : ‖w‖=1) :
    ((a*b:ℝ):ℂ)*w * conj (((a*c:ℝ):ℂ)*w*Complex.exp (Complex.I*(θ:ℂ))) / 2 -
      conj (((a*b:ℝ):ℂ)*w) * (((a*c:ℝ):ℂ)*w*Complex.exp (Complex.I*(θ:ℂ))) / 2 =
        -Complex.I * ((a^2*b*c*Real.sin θ:ℝ):ℂ) := by
  have hww : w*conj w=1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [mul_comm Complex.I (θ:ℂ), Complex.exp_ofReal_mul_I]
  simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  linear_combination -Complex.I*(a:ℂ)^2*(b:ℂ)*(c:ℂ)*(Complex.sin (θ:ℂ)) * hww

end Fourier

end

end RP3

/-! Module: RP3.Fourier.MatrixSquare -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

universe uP uX

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Fourier

@[expose] def SquareBound {X : Type uX} {P : Type uP} [Fintype X] [Fintype P]
    (U : X → P → ℂ) (a : ℝ) : Prop :=
  ∀ v : P → ℂ, (∑ x, ‖∑ p, U x p*v p‖^2) ≤ a^2*∑ p, ‖v p‖^2

variable {X : Type uX} {P : Type uP} [Fintype X] [Fintype P]

theorem SquareBound.column {U : X → P → ℂ} {a : ℝ} (h : SquareBound U a) (p : P) :
    ∑ x, ‖U x p‖^2 ≤ a^2 := by
  classical
  have hs : (∑ q : P, ‖((Pi.single p (1:ℂ)) : P → ℂ) q‖^2) = 1 := by
    simp only [Pi.single_apply, apply_ite, norm_one, norm_zero, ite_pow, one_pow,
      zero_pow (by decide : 2 ≠ 0), Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have he := h (Pi.single p 1)
  rw [hs, mul_one] at he
  simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using he

theorem SquareBound.gram_weighted {U : X → P → ℂ} {a : ℝ}
    (h : SquareBound U a) (d : P → ℂ) :
    (∑ x, ∑ y, ‖∑ p, U x p*d p*conj (U y p)‖^2) ≤ a^4*∑ p, ‖d p‖^2 := by
  calc _ = ∑ y, ∑ x, ‖∑ p, U x p*(d p*conj (U y p))‖^2 := by
          simp only [mul_assoc]
          exact Finset.sum_comm
       _ ≤ ∑ y, a^2*∑ p, ‖d p*conj (U y p)‖^2 :=
          Finset.sum_le_sum fun y _ => h (fun p => d p*conj (U y p))
       _ = a^2*∑ p, ‖d p‖^2*(∑ y, ‖U y p‖^2) := by
          simp only [norm_mul, Complex.norm_conj, mul_pow, Finset.mul_sum]
          rw [Finset.sum_comm]
       _ ≤ a^2*∑ p, ‖d p‖^2*a^2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (h.column p) (sq_nonneg _)
       _ = _ := by rw [← Finset.sum_mul]; ring

theorem sum_norm_add_sq_le (f g : X → ℂ) :
    (∑ x, ‖f x+g x‖^2) ≤ 2*(∑ x, ‖f x‖^2)+2*(∑ x, ‖g x‖^2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hv := norm_add_le (f x) (g x)
  have hsq := sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr hv
  nlinarith [sq_nonneg (‖f x‖-‖g x‖)]

theorem parseval_of_orthogonal [DecidableEq P] (W : X → P → ℂ) (M : ℝ)
    (ho : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (v : P → ℂ) :
    (∑ x, ‖∑ p, W x p*v p‖^2) = M*∑ p, ‖v p‖^2 := by
  classical
  have he : (∑ x, (∑ p, W x p*v p)*conj (∑ q, W x q*v q)) =
      (M:ℂ)*∑ p, v p*conj (v p) := by
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    calc
      (∑ x, ∑ q, ∑ p, W x p*v p*(conj (W x q)*conj (v q))) =
          ∑ q, ∑ p, ∑ x, W x p*v p*(conj (W x q)*conj (v q)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun q _ => Finset.sum_comm)
      _ = ∑ p, ∑ q, (∑ x, W x p*conj (W x q))*(v p*conj (v q)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by simp [ho]
  have hr := congrArg Complex.re he
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_re, ← Complex.ofReal_sum, ← Complex.ofReal_mul] at hr
  exact hr

theorem parseval_diagonal_bound [DecidableEq P] (W : X → P → ℂ) (M c : ℝ) (hM : 0 ≤ M)
    (ho : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (d v : P → ℂ) (hd : ∀ p, ‖d p‖ ≤ c) :
    (∑ x, ‖∑ p, W x p*(d p*v p)‖^2) ≤ (M*c^2)*∑ p, ‖v p‖^2 := by
  rw [parseval_of_orthogonal W M ho, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hM
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd p) 2) (sq_nonneg _)

end Fourier

end

end RP3

/-! Module: RP3.Fourier.FourierOperator -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

universe uP uX uY

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier

variable {X : Type uX} {P : Type uP} {Y : Type uY} [Fintype X] [Fintype P] [Fintype Y]

theorem sum_norm_pointwise_mul_sq_le (d v : X → ℂ) (c : ℝ) (hd : ∀ x, ‖d x‖ ≤ c) :
    (∑ x, ‖d x*v x‖^2) ≤ c^2*∑ x, ‖v x‖^2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun x _ => by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hd x) 2) (sq_nonneg _)

theorem sum_norm_sq_restrict (i : Y → X) (hi : Function.Injective i) (v : X → ℂ) :
    (∑ y, ‖v (i y)‖^2) ≤ ∑ x, ‖v x‖^2 := by
  classical
  calc _ = ∑ x ∈ Finset.univ.image i, ‖v x‖^2 := (Finset.sum_image (fun a _ b _ h => hi h)).symm
       _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg fun x => sq_nonneg _

theorem modulated_fourier_bound [DecidableEq P] (W : X → P → ℂ) (M C A : ℝ)
    (hM : 0 ≤ M)
    (hW : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (d : X → ℂ) (a v : P → ℂ) (hd : ∀ x, ‖d x‖ ≤ C) (ha : ∀ p, ‖a p‖ ≤ A) :
    (∑ x, ‖d x*(∑ p, W x p*(a p*v p))‖^2) ≤ (C^2*M*A^2)*∑ p, ‖v p‖^2 := by
  calc _ ≤ C^2*∑ x, ‖∑ p, W x p*(a p*v p)‖^2 := sum_norm_pointwise_mul_sq_le _ _ C hd
       _ ≤ C^2*((M*A^2)*∑ p, ‖v p‖^2) := mul_le_mul_of_nonneg_left
          (parseval_diagonal_bound W M A hM hW a v ha) (sq_nonneg _)
       _ = _ := by ring

theorem cutoff_fourier_difference_bound {L : ℕ} [NeZero L] [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (φ : DiscreteTorus L → ℂ) (h : DiscreteTorus L) (a v : P → ℂ)
    (D C A B : ℝ) (hD : ∀ x, ‖φ (x+h)-φ x‖ ≤ D)
    (hC : ∀ x, ‖φ (x+h)‖ ≤ C) (hA : ∀ q, ‖a q‖ ≤ A)
    (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    (∑ x, ‖∑ q, (a q*(φ (x+h)*torusWave (p q) (x+h)-φ x*torusWave (p q) x))*v q‖^2) ≤
      (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))*∑ q, ‖v q‖^2 := by
  let f := fun x => (φ (x+h)-φ x)*(∑ q, torusWave (p q) x*(a q*v q))
  let g := fun x => φ (x+h)*(∑ q, torusWave (p q) x*((a q*(torusWave (p q) h-1))*v q))
  have he (x : DiscreteTorus L) :
      (∑ q, a q*(φ (x+h)*torusWave (p q) (x+h)-φ x*torusWave (p q) x)*v q) = f x+g x := by
    simp only [f, g, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [torus_mode_difference]
    ring
  simp_rw [he]
  have hf := modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) D A
    (sq_nonneg _) (fun i j => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp i j) (fun x => φ (x+h)-φ x) a v hD hA
  have hg := modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) C B
    (sq_nonneg _) (fun i j => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp i j) (fun x => φ (x+h))
    (fun q => a q*(torusWave (p q) h-1)) v hC hB
  have ht := sum_norm_add_sq_le f g
  dsimp only [f, g] at ht ⊢
  linarith

theorem restricted_cutoff_squareBound {L : ℕ} [NeZero L] [DecidableEq P]
    (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (φ : DiscreteTorus L → ℂ) (h : DiscreteTorus L) (a : P → ℂ)
    (i : Y → DiscreteTorus L) (hi : Function.Injective i)
    (D C A B : ℝ) (hD : ∀ x, ‖φ (x+h)-φ x‖ ≤ D)
    (hC : ∀ x, ‖φ (x+h)‖ ≤ C) (hA : ∀ q, ‖a q‖ ≤ A)
    (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    SquareBound (fun y q => a q*(φ (i y+h)*torusWave (p q) (i y+h)-φ (i y)*torusWave (p q) (i y)))
      (Real.sqrt (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))) := by
  intro v
  rw [Real.sq_sqrt (by positivity)]
  exact (sum_norm_sq_restrict i hi _).trans
    (cutoff_fourier_difference_bound p hp φ h a v D C A B hD hC hA hB)

end Fourier

end

end RP3

/-! Module: RP3.Fourier.EdgeOperators -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

universe uP uX uY

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier

theorem restricted_modulated_fourier_bound {X : Type uX} {P : Type uP} {Y : Type uY}
    [Fintype X] [Fintype P] [Fintype Y] [DecidableEq P]
    (W : X → P → ℂ) (M C A : ℝ) (hM : 0 ≤ M)
    (hW : ∀ p q, (∑ x, W x p*conj (W x q)) = if p=q then (M:ℂ) else 0)
    (i : Y → X) (hi : Function.Injective i) (d : Y → ℂ) (a v : P → ℂ)
    (hd : ∀ y, ‖d y‖ ≤ C) (ha : ∀ p, ‖a p‖ ≤ A) :
    (∑ y, ‖d y*(∑ p, W (i y) p*(a p*v p))‖^2) ≤ (C^2*M*A^2)*∑ p, ‖v p‖^2 := by
  calc _ ≤ C^2*∑ y, ‖∑ p, W (i y) p*(a p*v p)‖^2 := sum_norm_pointwise_mul_sq_le _ _ C hd
       _ ≤ C^2*∑ x, ‖∑ p, W x p*(a p*v p)‖^2 :=
          mul_le_mul_of_nonneg_left (sum_norm_sq_restrict i hi (fun x => ∑ p, W x p*(a p*v p))) (sq_nonneg _)
       _ ≤ C^2*((M*A^2)*∑ p, ‖v p‖^2) := mul_le_mul_of_nonneg_left
          (parseval_diagonal_bound W M A hM hW a v ha) (sq_nonneg _)
       _ = _ := by ring

theorem edge_cutoff_squareBound {P : Type uP} {Y : Type uY} [Fintype P] [Fintype Y] [DecidableEq P]
    {L : ℕ} [NeZero L] (p : P → DiscreteTorus L) (hp : Function.Injective p)
    (i : Y → DiscreteTorus L) (hi : Function.Injective i) (h : DiscreteTorus L)
    (φ₀ φ₁ : Y → ℂ) (a : P → ℂ)
    (D C A B : ℝ) (hD : ∀ y, ‖φ₁ y-φ₀ y‖ ≤ D) (hC : ∀ y, ‖φ₁ y‖ ≤ C)
    (hA : ∀ q, ‖a q‖ ≤ A) (hB : ∀ q, ‖a q*(torusWave (p q) h-1)‖ ≤ B) :
    SquareBound (fun y q => a q*(φ₁ y*torusWave (p q) (i y+h)-φ₀ y*torusWave (p q) (i y)))
      (Real.sqrt (2*(L:ℝ)^2*(D^2*A^2+C^2*B^2))) := by
  intro v
  rw [Real.sq_sqrt (by positivity)]
  let f := fun y => (φ₁ y-φ₀ y)*(∑ q, torusWave (p q) (i y)*(a q*v q))
  let g := fun y => φ₁ y*(∑ q, torusWave (p q) (i y)*((a q*(torusWave (p q) h-1))*v q))
  have he (y : Y) :
      (∑ q, a q*(φ₁ y*torusWave (p q) (i y+h)-φ₀ y*torusWave (p q) (i y))*v q) = f y+g y := by
    simp only [f, g, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    rw [torusWave_add]
    ring
  simp_rw [he]
  have hf := restricted_modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) D A
    (sq_nonneg _) (fun q r => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp q r)
    i hi (fun y => φ₁ y-φ₀ y) a v hD hA
  have hg := restricted_modulated_fourier_bound (fun x q => torusWave (p q) x) ((L:ℝ)^2) C B
    (sq_nonneg _) (fun q r => by simpa only [Complex.ofReal_pow] using torusWave_orthogonal_subfamily p hp q r)
    i hi φ₁ (fun q => a q*(torusWave (p q) h-1)) v hC hB
  have ht := sum_norm_add_sq_le f g
  dsimp only [f, g] at ht ⊢
  linarith

end Fourier

end

end RP3

/-! Module: RP3.Fourier.SquareEstimates -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

universe uI uP uX

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier

variable {X : Type uX} {P : Type uP} {I : Type uI} [Fintype X] [Fintype P] [Fintype I]

theorem norm_sum_sq_le_card (f : I → ℂ) :
    ‖∑ i, f i‖^2 ≤ (Fintype.card I:ℝ)*∑ i, ‖f i‖^2 := by
  calc _ ≤ (∑ i, ‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
       _ ≤ _ := by
          have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R := ℝ)
            (s := Finset.univ) (r := fun i => ‖f i‖) (f := fun _ => 1)
            (g := fun i => ‖f i‖^2) (fun _ _ => by norm_num) (fun i _ => sq_nonneg _)
            (fun i _ => le_of_eq (one_mul _).symm)
          simpa using h

theorem SquareBound.mono {U : X → P → ℂ} {a b : ℝ}
    (ha : SquareBound U a) (hab : a^2 ≤ b^2) : SquareBound U b := by
  intro v
  exact (ha v).trans (mul_le_mul_of_nonneg_right hab (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem sum_by_fibers [DecidableEq I] (d : X → I) (f : X → ℝ) :
    (∑ x, f x) = ∑ i, ∑ x : {x // d x=i}, f x := by
  classical
  simpa only [Fintype.sum_sigma, Equiv.sigmaFiberEquiv_apply] using
    (Equiv.sum_comp (Equiv.sigmaFiberEquiv d) f).symm

theorem SquareBound.combine_directions (U : X → P → ℂ) (d : X → Bool) (a : ℝ)
    (h : ∀ m : Bool, SquareBound (fun (x : {x // d x=m}) p => U x p) a) :
    SquareBound U (2*a) := by
  intro v
  rw [sum_by_fibers d]
  calc _ ≤ ∑ _m : Bool, a^2*∑ p, ‖v p‖^2 :=
          Finset.sum_le_sum fun m _ => h m v
       _ ≤ (2*a)^2*∑ p, ‖v p‖^2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul, Nat.cast_ofNat]
          have hs : 0 ≤ ∑ p : P, ‖v p‖^2 := Finset.sum_nonneg fun p _ => sq_nonneg ‖v p‖
          nlinarith [mul_nonneg (sq_nonneg a) hs]

theorem gram_groups_bound (T : I → X → X → ℂ) (C : ℝ)
    (h : ∀ i, (∑ x, ∑ y, ‖T i x y‖^2) ≤ C) :
    (∑ x, ∑ y, ‖∑ i, T i x y‖^2) ≤ (Fintype.card I:ℝ)^2*C := by
  calc _ ≤ ∑ x, ∑ y, (Fintype.card I:ℝ)*∑ i, ‖T i x y‖^2 :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => norm_sum_sq_le_card _
       _ = (Fintype.card I:ℝ)*∑ i, ∑ x, ∑ y, ‖T i x y‖^2 := by
          simp only [← Finset.mul_sum]
          congr 1
          calc (∑ x, ∑ y, ∑ i, ‖T i x y‖^2) = ∑ x, ∑ i, ∑ y, ‖T i x y‖^2 :=
                Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
               _ = _ := Finset.sum_comm
       _ ≤ (Fintype.card I:ℝ)*∑ _i : I, C := by gcongr with i; exact h i
       _ = _ := by simp; ring

end Fourier

end

end RP3

/-! Module: RP3.Fourier.LatticeModes -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier

variable {k : ℕ}

@[expose] def latticeMode (m s : Bool) (p : DyadicFreq k) (x : Site) : ℂ :=
  (dyadicWeight p:ℂ) * (squareProfile m s (scaledSite k x):ℂ) *
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) x)

theorem groupedPoint_abs_bound (m s : Bool) (p : DyadicFreq k) :
    |(groupedPoint m s p).1| ≤ 2*(dyadicRadius p:ℤ) ∧
    |(groupedPoint m s p).2| ≤ 2*(dyadicRadius p:ℤ) := by
  have hp := dyadicPoint_bounds p
  have hr : (0:ℤ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have h1 : |(dyadicPoint p).1| ≤ 2*(dyadicRadius p:ℤ) := abs_le.mpr (by constructor <;> omega)
  have h2 : |(dyadicPoint p).2| ≤ 2*(dyadicRadius p:ℤ) := abs_le.mpr (by constructor <;> omega)
  cases m <;> cases s
  · simpa [groupedPoint] using And.intro h1 h2
  · simpa [groupedPoint] using And.intro h1 h2
  · simpa [groupedPoint] using And.intro h2 h1
  · simpa [groupedPoint] using And.intro h2 h1

theorem groupedWave_axis (m s j : Bool) (p : DyadicFreq k) :
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j)) =
      ZMod.stdAddChar ((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ZMod (16*2^k)) := by
  cases j <;> simp [torusWave, groupedTorusPoint, latticeTorus, latticeAxis]

theorem groupedWave_axis_sine (m s j : Bool) (p : DyadicFreq k) :
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j)) =
      Complex.exp (Complex.I*((dyadicAngle k ((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ):ℂ)) := by
  rw [groupedWave_axis]
  cases j <;> simp only [Bool.false_eq_true, ↓reduceIte]
  all_goals
    rw [ZMod.stdAddChar_coe]
    congr 1
    unfold dyadicAngle
    push_cast
    ring

theorem groupedWave_multiplier_bound (m s j : Bool) (p : DyadicFreq k) :
    ‖((1/(dyadicRadius p:ℝ)):ℂ) *
      (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) (latticeAxis j))-1)‖ ≤
        Real.pi/(4*(2:ℝ)^k) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hp : |((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ)| ≤
      2*(dyadicRadius p:ℤ) := by
    cases j
    · exact (groupedPoint_abs_bound m s p).1
    · exact (groupedPoint_abs_bound m s p).2
  have hp' : |(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)| ≤ 2*(dyadicRadius p:ℝ) := by exact_mod_cast hp
  simp only [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [groupedWave_axis]
  have hchar : ‖ZMod.stdAddChar (if j then ((groupedPoint m s p).2:ZMod (16*2^k)) else ((groupedPoint m s p).1:ZMod (16*2^k)))-1‖ ≤
      (2*Real.pi/(16*2^k:ℕ))*|(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)| := by
    cases j <;> exact norm_stdAddChar_intCast_sub_one (L := 16*2^k) _
  calc _ ≤ (1/(dyadicRadius p:ℝ))*((2*Real.pi/(16*2^k:ℕ))*|(((if j then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℤ):ℝ)|) :=
          mul_le_mul_of_nonneg_left hchar (by positivity)
       _ ≤ (1/(dyadicRadius p:ℝ))*((2*Real.pi/(16*2^k:ℕ))*(2*(dyadicRadius p:ℝ))) := by gcongr
       _ = Real.pi/(4*(2:ℝ)^k) := by push_cast; field_simp [ne_of_gt hr]; ring

theorem latticeMode_norm_bound (m s : Bool) (p : DyadicFreq k) (x : Site) (C : ℝ)
    (hC : |squareProfile m s (scaledSite k x)| ≤ C) : ‖latticeMode m s p x‖ ≤ dyadicWeight p*C := by
  simp only [latticeMode, norm_mul, torusWave_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_pos (dyadicWeight_pos p)]
  exact mul_le_mul_of_nonneg_left hC (dyadicWeight_pos p).le

namespace LatticeGraph

@[expose] def modeGradient (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  latticeMode m s p e.val.2.val-latticeMode m s p e.val.1.val

@[expose] def scaledModeGradient (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (Real.sqrt (dyadicRadius p:ℝ):ℂ)*G.modeGradient m s p e

theorem scaledModeGradient_formula (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.scaledModeGradient m s p e =
      ((1/(dyadicRadius p:ℝ)):ℂ) *
      ((squareProfile m s (scaledSite k e.val.2.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e))) -
       (squareProfile m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p)
        (latticeTorus (16*2^k) e.val.1.val)) := by
  have h := congrArg Complex.ofReal (dyadicWeight_mul_sqrt p)
  push_cast at h
  simp only [scaledModeGradient, modeGradient, latticeMode]
  rw [G.edge_step e, latticeTorus_add]
  linear_combination ( ((squareProfile m s (scaledSite k (e.val.1.val+latticeAxis (G.edgeDirection e))):ℂ)*
    torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val+latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)))) -
    ((squareProfile m s (scaledSite k e.val.1.val):ℂ)*torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)) ) * h

end LatticeGraph
end Fourier

end

end RP3

/-! Module: RP3.Fourier.DyadicSums -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators
namespace Fourier

theorem dyadic_inverse_square_sum (k : ℕ) :
    (∑ p : DyadicFreq k, (1/(dyadicRadius p:ℝ))^2) ≤ 3*(k:ℝ) := by
  rw [Fintype.sum_sigma]
  calc _ ≤ ∑ j : Fin k, (3:ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          simp only [dyadicRadius, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hr : (0:ℝ) < (2^j.val:ℕ) := by positivity
          have hc : (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) ≤ 3*((2^j.val:ℕ):ℝ)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds j.val).2
          calc _ ≤ (3*((2^j.val:ℕ):ℝ)^2)*(1/((2^j.val:ℕ):ℝ))^2 :=
                mul_le_mul_of_nonneg_right hc (sq_nonneg _)
               _ = 3 := by field_simp
       _ = _ := by simp; ring

theorem sum_dyadic_ratio_lower (k i : ℕ) :
    (∑ j ∈ Finset.range k, if j ≤ i then (2:ℝ)^j/2^i else 0) ≤ 2 := by
  classical
  rw [← Finset.sum_filter]
  have hs : (Finset.range k).filter (fun j => j ≤ i) ⊆ Finset.range (i+1) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  calc _ ≤ ∑ j ∈ Finset.range (i+1), (2:ℝ)^j/2^i :=
          Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => by positivity)
       _ ≤ 2 := by
          rw [← Finset.sum_div]
          have hh := geom_sum_mul (2:ℝ) (i+1)
          have hp : (0:ℝ) < 2^i := by positivity
          rw [div_le_iff₀ hp]
          simp only [show (2:ℝ)-1=1 by norm_num, mul_one,
            pow_succ] at hh
          linarith

theorem dyadic_min_ratio_sum (k : ℕ) :
    (∑ i : Fin k, ∑ j : Fin k, min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val)) ≤ 4*(k:ℝ) := by
  classical
  have point (i j : Fin k) : min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val) ≤
      (if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0)+
      (if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0) := by
    by_cases h : j.val ≤ i.val
    · rw [ite_eq_left h]
      exact (min_le_right _ _).trans (le_add_of_nonneg_right (by split_ifs <;> positivity))
    · have hh : i.val ≤ j.val := by omega
      rw [ite_eq_right h, ite_eq_left hh, zero_add]
      exact min_le_left _ _
  have hs : (∑ i : Fin k, ∑ j : Fin k, if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0) ≤ 2*(k:ℝ) := by
    calc _ ≤ ∑ _i : Fin k, (2:ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            rw [← Finset.sum_range (fun j => if j ≤ i.val then (2:ℝ)^j/2^i.val else 0)]
            exact sum_dyadic_ratio_lower k i.val
         _ = _ := by simp; ring
  calc _ ≤ ∑ i : Fin k, ∑ j : Fin k,
          ((if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0)+
           (if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0)) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => point i j
       _ = 2*∑ i : Fin k, ∑ j : Fin k, if j.val ≤ i.val then (2:ℝ)^j.val/2^i.val else 0 := by
          simp only [Finset.sum_add_distrib]
          rw [Finset.sum_comm (f := fun i j : Fin k => if i.val ≤ j.val then (2:ℝ)^i.val/2^j.val else 0)]
          ring
       _ ≤ _ := by linarith

theorem weighted_dyadic_min_pair (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    a^2*b^2*min ((1/a)^3*(1/b)) ((1/b)^3*(1/a)) = min (b/a) (a/b) := by
  rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ a^2*b^2)]
  congr 1 <;> field_simp

theorem dyadic_min_cost_sum (k : ℕ) :
    (∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
      min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
          ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ)))) ≤ 36*(k:ℝ) := by
  simp only [Fintype.sum_sigma]
  have he : (∑ i : Fin k, ∑ a : Fin (2^i.val) × Fin (2*2^i.val+1),
      ∑ j : Fin k, ∑ b : Fin (2^j.val) × Fin (2*2^j.val+1),
      min ((1/(dyadicRadius ⟨i,a⟩:ℝ))^3*(1/(dyadicRadius ⟨j,b⟩:ℝ)))
          ((1/(dyadicRadius ⟨j,b⟩:ℝ))^3*(1/(dyadicRadius ⟨i,a⟩:ℝ)))) =
      ∑ i : Fin k, ∑ j : Fin k,
      (Fintype.card (Fin (2^i.val) × Fin (2*2^i.val+1)):ℝ)*
      (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ)*
      min ((1/(2:ℝ)^i.val)^3*(1/(2:ℝ)^j.val))
          ((1/(2:ℝ)^j.val)^3*(1/(2:ℝ)^i.val)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    simp only [dyadicRadius, Nat.cast_pow, Nat.cast_ofNat, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [he]
  calc _ ≤ ∑ i : Fin k, ∑ j : Fin k, 9*min ((2:ℝ)^i.val/2^j.val) (2^j.val/2^i.val) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          have hi : (Fintype.card (Fin (2^i.val) × Fin (2*2^i.val+1)):ℝ) ≤ 3*((2:ℝ)^i.val)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds i.val).2
          have hj : (Fintype.card (Fin (2^j.val) × Fin (2*2^j.val+1)):ℝ) ≤ 3*((2:ℝ)^j.val)^2 := by
            exact_mod_cast (dyadic_shell_card_bounds j.val).2
          calc _ ≤ (3*((2:ℝ)^i.val)^2)*(3*((2:ℝ)^j.val)^2)*
                min ((1/(2:ℝ)^i.val)^3*(1/(2:ℝ)^j.val)) ((1/(2:ℝ)^j.val)^3*(1/(2:ℝ)^i.val)) := by
                  gcongr
               _ = _ := by
                  rw [show (3*((2:ℝ)^i.val)^2)*(3*((2:ℝ)^j.val)^2) = 9*(((2:ℝ)^i.val)^2*((2:ℝ)^j.val)^2) by ring,
                    mul_assoc, weighted_dyadic_min_pair _ _ (by positivity) (by positivity), min_comm]
       _ ≤ _ := by
          simp only [← Finset.mul_sum]
          have hs := dyadic_min_ratio_sum k
          linarith

end Fourier

end

end RP3

/-! Module: RP3.Fourier.ModeBounds -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier
namespace LatticeGraph
variable {k : ℕ}

@[expose] def modeBlockConstant (C : ℝ) : ℝ := Real.sqrt (512*(C^2+C^2*(Real.pi/4)^2))

theorem scaledModes_direction_bound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (C : ℝ)
    (hval : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (m s j : Bool) :
    SquareBound (fun (e : G.DirectionalEdges j) (p : DyadicFreq k) => G.scaledModeGradient m s p e.val)
      (modeBlockConstant C) := by
  classical
  have hN : (2:ℝ)^k ≠ 0 := by positivity
  have hd (e : G.DirectionalEdges j) :
      ‖(squareProfile m s (scaledSite k e.val.val.2.val):ℂ)-
        (squareProfile m s (scaledSite k e.val.val.1.val):ℂ)‖ ≤ C/(2:ℝ)^k := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simpa only [G.scaled_edge_distance, div_eq_mul_inv, one_mul] using
      hLip m s (scaledSite k e.val.val.1.val) (scaledSite k e.val.val.2.val)
  have hv (e : G.DirectionalEdges j) :
      ‖(squareProfile m s (scaledSite k e.val.val.2.val):ℂ)‖ ≤ C := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hval m s (scaledSite k e.val.val.2.val)
  have ha (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖ ≤ 1 := by
    have hp : (1:ℝ) ≤ dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ dyadicRadius p)]
    exact (div_le_one (by positivity)).mpr hp
  have hh := edge_cutoff_squareBound (groupedTorusPoint m s) (groupedTorusPoint_injective m s)
    (fun e : G.DirectionalEdges j => latticeTorus (16*2^k) e.val.val.1.val)
    (G.directional_torus_injective k hG j) (latticeTorus (16*2^k) (latticeAxis j))
    (fun e => (squareProfile m s (scaledSite k e.val.val.1.val):ℂ))
    (fun e => (squareProfile m s (scaledSite k e.val.val.2.val):ℂ))
    (fun p => ((1/(dyadicRadius p:ℝ)):ℂ)) (C/(2:ℝ)^k) C 1 (Real.pi/(4*(2:ℝ)^k))
    hd hv ha (groupedWave_multiplier_bound m s j)
  have hc : Real.sqrt (2*((16*2^k:ℕ):ℝ)^2*((C/(2:ℝ)^k)^2*1^2+C^2*(Real.pi/(4*(2:ℝ)^k))^2)) = modeBlockConstant C := by
    congr 1
    push_cast
    field_simp [hN]
    ring
  rw [hc] at hh
  have hdir (e : G.DirectionalEdges j) : G.edgeDirection e.val=j := e.property
  exact fun v => by simpa only [G.scaledModeGradient_formula, hdir] using hh v

theorem scaledModes_squareBound (G : LatticeGraph) (hG : G.WithinDyadicBox k)
    (C : ℝ)
    (hval : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (m s : Bool) :
    SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) (2*modeBlockConstant C) := by
  apply SquareBound.combine_directions _ G.edgeDirection
  exact fun j => G.scaledModes_direction_bound hG C hval hLip m s j

end LatticeGraph
end Fourier

end

end RP3

/-! Module: RP3.Fourier.ModeCosts -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier
namespace LatticeGraph
variable {k : ℕ}

theorem mode_gradient_square_sum_le (G : LatticeGraph) (m s : Bool) (a : ℝ)
    (h : SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) (p : DyadicFreq k) :
    (∑ e, ‖G.modeGradient m s p e‖^2) ≤ a^2/(dyadicRadius p:ℝ) := by
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hh := h.column p
  simp only [scaledModeGradient, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hr.le] at hh
  rw [← Finset.mul_sum] at hh
  exact (le_div_iff₀ hr).mpr (by simpa only [mul_comm] using hh)

theorem mode_sup_square_le (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ z, |squareProfile m s z| ≤ C) :
    ‖(fun x : G.vertices => latticeMode m s p x.val)‖^2 ≤ C^2*(1/(dyadicRadius p:ℝ))^3 := by
  have hnorm : ‖(fun x : G.vertices => latticeMode m s p x.val)‖ ≤ dyadicWeight p*C := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (dyadicWeight_pos p).le hC)).mpr
    exact fun x => latticeMode_norm_bound m s p x.val C (hv _)
  calc _ ≤ (dyadicWeight p*C)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
       _ = _ := by rw [mul_pow, dyadicWeight_sq]; ring

theorem mode_gram_reweight (G : LatticeGraph) (m s : Bool) (e l : G.edges) :
    (∑ p : DyadicFreq k, G.scaledModeGradient m s p e*((1/(dyadicRadius p:ℝ)):ℂ)*
      conj (G.scaledModeGradient m s p l)) = ∑ p : DyadicFreq k,
        G.modeGradient m s p e*conj (G.modeGradient m s p l) := by
  apply Finset.sum_congr rfl
  intro p _
  have hr : (0:ℝ)<dyadicRadius p := by exact_mod_cast dyadicRadius_pos p
  have hs : ((Real.sqrt (dyadicRadius p:ℝ):ℂ)*((1/(dyadicRadius p:ℝ)):ℂ)*
      (Real.sqrt (dyadicRadius p:ℝ):ℂ)) = 1 := by
    have hsreal : Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) = 1 := by
      rw [show Real.sqrt (dyadicRadius p:ℝ)*(1/(dyadicRadius p:ℝ))*Real.sqrt (dyadicRadius p:ℝ) =
      (Real.sqrt (dyadicRadius p:ℝ))^2/(dyadicRadius p:ℝ) by ring, Real.sq_sqrt hr.le, div_self hr.ne']
    exact_mod_cast hsreal
  simp only [scaledModeGradient, map_mul, Complex.conj_ofReal]
  linear_combination G.modeGradient m s p e*conj (G.modeGradient m s p l)*hs

theorem mode_group_gram_bound (G : LatticeGraph) (m s : Bool) (a : ℝ)
    (h : SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    (∑ e, ∑ l, ‖∑ p : DyadicFreq k, G.modeGradient m s p e*conj (G.modeGradient m s p l)‖^2)
      ≤ 3*a^4*(k:ℝ) := by
  have hh := h.gram_weighted (fun p => ((1/(dyadicRadius p:ℝ)):ℂ))
  simp_rw [G.mode_gram_reweight] at hh
  have he (p : DyadicFreq k) : ‖((1/(dyadicRadius p:ℝ)):ℂ)‖^2 = (1/(dyadicRadius p:ℝ))^2 := by
    have hr : (0:ℝ) ≤ dyadicRadius p := by positivity
    simp only [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  simp_rw [he] at hh
  exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left (dyadic_inverse_square_sum k) (by positivity : 0≤a^4)])

abbrev ModeIndex (k : ℕ) := (Bool × Bool) × DyadicFreq k

@[expose] def modes (G : LatticeGraph) (i : ModeIndex k) (x : G.vertices) : ℂ :=
  latticeMode i.1.1 i.1.2 i.2 x.val

@[expose] def modeDifferences (G : LatticeGraph) (i : ModeIndex k) (e : G.edges) : ℂ :=
  G.modeGradient i.1.1 i.1.2 i.2 e

theorem modes_HS_bound (G : LatticeGraph) (a : ℝ)
    (h : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    familyHSSquare (G.modeDifferences (k := k)) ≤ 48*a^4*(k:ℝ) := by
  unfold familyHSSquare rowSquare familyKernel modeDifferences
  simp only [Fintype.sum_prod_type]
  have hh := gram_groups_bound
    (fun (i : Bool × Bool) e l => ∑ p : DyadicFreq k,
      G.modeGradient i.1 i.2 p e*conj (G.modeGradient i.1 i.2 p l))
    (3*a^4*(k:ℝ)) (fun i => G.mode_group_gram_bound i.1 i.2 a (h i.1 i.2))
  simpa only [Fintype.sum_prod_type, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    show ((2:ℝ)*2)^2*(3*a^4*(k:ℝ)) = 48*a^4*(k:ℝ) by ring] using hh

theorem modes_min_bound (G : LatticeGraph) (a C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (h : ∀ m s, SquareBound (fun e (p : DyadicFreq k) => G.scaledModeGradient m s p e) a) :
    (∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2)) ≤ 576*C^2*a^2*(k:ℝ) := by
  have hv' (i : ModeIndex k) : ‖G.modes i‖^2 ≤ C^2*(1/(dyadicRadius i.2:ℝ))^3 :=
    G.mode_sup_square_le i.1.1 i.1.2 i.2 C hC (hv i.1.1 i.1.2)
  have hd' (i : ModeIndex k) : (∑ e, ‖G.modeDifferences i e‖^2) ≤ a^2/(dyadicRadius i.2:ℝ) :=
    G.mode_gradient_square_sum_le i.1.1 i.1.2 a (h i.1.1 i.1.2) i.2
  have hm (i j : ModeIndex k) :
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2) ≤
      C^2*a^2*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                 ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) := by
    rw [mul_min_of_nonneg _ _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    apply min_le_min
    · calc _ ≤ (C^2*(1/(dyadicRadius i.2:ℝ))^3)*(a^2/(dyadicRadius j.2:ℝ)) :=
            mul_le_mul (hv' i) (hd' j) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
    · calc _ ≤ (C^2*(1/(dyadicRadius j.2:ℝ))^3)*(a^2/(dyadicRadius i.2:ℝ)) :=
            mul_le_mul (hv' j) (hd' i) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
           _ = _ := by ring
  calc _ ≤ ∑ i : ModeIndex k, ∑ j : ModeIndex k,
        C^2*a^2*min ((1/(dyadicRadius i.2:ℝ))^3*(1/(dyadicRadius j.2:ℝ)))
                   ((1/(dyadicRadius j.2:ℝ))^3*(1/(dyadicRadius i.2:ℝ))) :=
           Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hm i j
       _ = 16*C^2*a^2*∑ p : DyadicFreq k, ∑ q : DyadicFreq k,
           min ((1/(dyadicRadius p:ℝ))^3*(1/(dyadicRadius q:ℝ)))
               ((1/(dyadicRadius q:ℝ))^3*(1/(dyadicRadius p:ℝ))) := by
          simp only [ModeIndex, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
            Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, nsmul_eq_mul, Nat.cast_ofNat, ← Finset.mul_sum]
          ring
       _ ≤ _ := by
          have hd := mul_le_mul_of_nonneg_left (dyadic_min_cost_sum k)
            (by positivity : 0 ≤ 16*C^2*a^2)
          nlinarith

end LatticeGraph
end Fourier

end

end RP3

/-! Module: RP3.Fourier.ModeCommutator -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Fourier
variable {k : ℕ}

theorem dyadic_sine_main_sum (k : ℕ) :
    (∑ p : DyadicFreq k, (dyadicWeight p)^2*Real.sin (dyadicAngle k (dyadicPoint p).1)) =
      dyadicLambda k/(2:ℝ)^k := by
  simp only [dyadicWeight_sq, dyadicLambda]
  rw [mul_div_cancel_left₀ _ (by positivity : (2:ℝ)^k ≠ 0)]

theorem grouped_sine_sum (m s j : Bool) :
    (∑ p : DyadicFreq k, (dyadicWeight p)^2*
      Real.sin (dyadicAngle k (if j then (groupedPoint m s p).2 else (groupedPoint m s p).1))) =
      if m=j then (if s then -(dyadicLambda k/(2:ℝ)^k) else dyadicLambda k/(2:ℝ)^k) else 0 := by
  have h1 := dyadic_sine_main_sum k
  have h2 := dyadic_sin_cancel k
  cases m <;> cases s <;> cases j <;>
    simp_all [groupedPoint]

namespace LatticeGraph

@[expose] def modeCommutator (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) : ℂ :=
  (latticeMode m s p e.val.1.val*conj (latticeMode m s p e.val.2.val)-
    conj (latticeMode m s p e.val.1.val)*latticeMode m s p e.val.2.val)/2

@[expose] def profileEdge (G : LatticeGraph) (k : ℕ) (e : G.edges) : ℝ :=
  (1/(2:ℝ)^k)*(squareProfile (G.edgeDirection e) false (scaledSite k e.val.1.val)*
    squareProfile (G.edgeDirection e) false (scaledSite k e.val.2.val)-
    squareProfile (G.edgeDirection e) true (scaledSite k e.val.1.val)*
    squareProfile (G.edgeDirection e) true (scaledSite k e.val.2.val))

@[expose] def thetaEdge (G : LatticeGraph) (k : ℕ) (e : G.edges) : ℝ :=
  squareTheta (scaledSite k e.val.2.val)-squareTheta (scaledSite k e.val.1.val)

theorem modeCommutator_formula (G : LatticeGraph) (m s : Bool) (p : DyadicFreq k) (e : G.edges) :
    G.modeCommutator m s p e = -Complex.I *
      ((squareProfile m s (scaledSite k e.val.1.val)*squareProfile m s (scaledSite k e.val.2.val)*
        ((dyadicWeight p)^2*Real.sin (dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))):ℝ):ℂ) := by
  have hy : latticeMode m s p e.val.2.val =
      (((dyadicWeight p*squareProfile m s (scaledSite k e.val.2.val)):ℝ):ℂ)*
        torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val)*
        Complex.exp (Complex.I*((dyadicAngle k
          (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1):ℝ):ℂ)) := by
    unfold latticeMode
    rw [show latticeTorus (16*2^k) e.val.2.val = latticeTorus (16*2^k) e.val.1.val+
      latticeTorus (16*2^k) (latticeAxis (G.edgeDirection e)) by rw [G.edge_step e,latticeTorus_add],
      torusWave_add, groupedWave_axis_sine]
    push_cast
    ring
  have hh := wave_commutator (dyadicWeight p)
    (squareProfile m s (scaledSite k e.val.1.val)) (squareProfile m s (scaledSite k e.val.2.val))
    (dyadicAngle k (if G.edgeDirection e then (groupedPoint m s p).2 else (groupedPoint m s p).1))
    (torusWave (groupedTorusPoint m s p) (latticeTorus (16*2^k) e.val.1.val))
    (torusWave_norm _ _)
  unfold modeCommutator
  rw [hy]
  simp only [latticeMode, Complex.ofReal_mul] at hh ⊢
  linear_combination hh

theorem mode_group_commutator (G : LatticeGraph) (m s : Bool) (e : G.edges) :
    (∑ p : DyadicFreq k, G.modeCommutator m s p e) = -Complex.I*
      ((squareProfile m s (scaledSite k e.val.1.val)*squareProfile m s (scaledSite k e.val.2.val)*
        (if m=G.edgeDirection e then (if s then -(dyadicLambda k/(2:ℝ)^k) else dyadicLambda k/(2:ℝ)^k) else 0):ℝ):ℂ) := by
  simp only [G.modeCommutator_formula, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [grouped_sine_sum]

theorem modes_commutator (G : LatticeGraph) (e : G.edges) :
    (∑ i : ModeIndex k, G.modeCommutator i.1.1 i.1.2 i.2 e) =
      -Complex.I*((dyadicLambda k*G.profileEdge k e:ℝ):ℂ) := by
  simp only [Fintype.sum_prod_type, G.mode_group_commutator, Fintype.sum_bool]
  cases h : G.edgeDirection e <;>
    simp [profileEdge, h]
  all_goals ring

end LatticeGraph
end Fourier

end

end RP3

/-! Module: RP3.Fourier.ThetaEstimates -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open Set
open scoped BigOperators ComplexConjugate
namespace Fourier

theorem squareTheta_compact : HasCompactSupport squareTheta := by
  apply HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (-2:ℝ) 2 ×ˢ Icc (-2:ℝ) 2))
  intro z hz
  apply squareTheta_zero
  by_contra h
  push Not at h
  apply hz
  constructor <;> constructor <;> nlinarith [abs_le.mp h.1.le, abs_le.mp h.2.le]

theorem theta_lipschitz_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ z w,
    |squareTheta w-squareTheta z| ≤ C*‖w-z‖ := by
  obtain ⟨C,hC,_,hL⟩ := smooth_compact_lipschitz_bound squareTheta_compact squareTheta_contDiff
  exact ⟨C,hC,by simpa only [Real.norm_eq_abs] using hL⟩

namespace LatticeGraph

theorem theta_edge_bounds : ∃ L D : ℝ, 0 ≤ L ∧ 0 ≤ D ∧
    ∀ (G : LatticeGraph) (k : ℕ), 4 ≤ k → ∀ e : G.edges,
      |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3 := by
  obtain ⟨L,hL,hLip⟩ := theta_lipschitz_bound
  obtain ⟨D,hD,hR⟩ := squareTheta_step_error
  refine ⟨L,D,hL,hD,?_⟩
  intro G k hk e
  constructor
  · have h := hLip (scaledSite k e.val.1.val) (scaledSite k e.val.2.val)
    rw [G.scaled_edge_distance] at h
    exact h.trans_eq (by ring)
  · have hN : (16:ℝ) ≤ (2:ℝ)^k := by
      calc (16:ℝ) = (2:ℝ)^4 := by norm_num
           _ ≤ _ := pow_le_pow_right₀ (by norm_num) hk
    have hmesh : |1/(2:ℝ)^k| ≤ 1/16 := by
      rw [abs_of_pos (by positivity)]
      exact one_div_le_one_div_of_le (by norm_num) hN
    have h := hR (G.edgeDirection e) (scaledSite k e.val.1.val) (1/(2:ℝ)^k) hmesh
    rw [← scaledSite_add_axis, ← G.edge_step e,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^k)] at h
    simpa only [thetaEdge,profileEdge,div_pow,one_pow,mul_one_div] using h

theorem theta_sum_bounds (G : LatticeGraph) (k : ℕ) (hG : G.WithinDyadicBox k)
    (L D : ℝ) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3) :
    (∑ e, |G.thetaEdge k e-G.profileEdge k e|) ≤ 512*D/(2:ℝ)^k ∧
    (∑ e, |G.thetaEdge k e|^2) ≤ 512*L^2 ∧
    (∑ e, |G.thetaEdge k e-G.profileEdge k e| *
      (|G.thetaEdge k e| + |G.profileEdge k e|)) ≤ 512*D*(2*L+D)/((2:ℝ)^k)^2 := by
  let N : ℝ := (2:ℝ)^k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hcount := G.edge_card_bound k hG
  change (Fintype.card G.edges:ℝ) ≤ 512*N^2 at hcount
  have hv (e : G.edges) : |G.profileEdge k e| ≤ (L+D)/N := by
    have htri : |G.profileEdge k e| ≤ |G.thetaEdge k e| + |G.thetaEdge k e-G.profileEdge k e| := by
      simpa only [add_sub_cancel, abs_sub_comm] using abs_add_le (G.thetaEdge k e) (G.profileEdge k e-G.thetaEdge k e)
    have hpow : N ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
    calc _ ≤ L/N+D/N^3 := htri.trans (add_le_add (he e).1 (he e).2)
         _ ≤ L/N+D/N := add_le_add_right (div_le_div_of_nonneg_left hD hN hpow) _
         _ = _ := by ring
  have hs1 : (∑ e, |G.thetaEdge k e-G.profileEdge k e|) ≤ (Fintype.card G.edges:ℝ)*(D/N^3) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ) (fun e _ => (he e).2)
  have hs2 : (∑ e, |G.thetaEdge k e|^2) ≤ (Fintype.card G.edges:ℝ)*(L/N)^2 := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => pow_le_pow_left₀ (abs_nonneg _) (he e).1 2)
  have hs3 : (∑ e, |G.thetaEdge k e-G.profileEdge k e| *(|G.thetaEdge k e| + |G.profileEdge k e|)) ≤
      (Fintype.card G.edges:ℝ)*(D/N^3*((2*L+D)/N)) := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using Finset.sum_le_sum (s := Finset.univ)
      (fun e _ => mul_le_mul (he e).2 (show |G.thetaEdge k e| + |G.profileEdge k e| ≤ (2*L+D)/N from
        (add_le_add (he e).1 (hv e)).trans_eq (by ring)) (by positivity) (by positivity))
  refine ⟨hs1.trans ?_,hs2.trans ?_,hs3.trans ?_⟩
  all_goals
    calc _ ≤ 512*N^2*_ := mul_le_mul_of_nonneg_right hcount (by positivity)
         _ = _ := by dsimp only [N]; field_simp

end LatticeGraph
end Fourier

end

end RP3

/-! Module: RP3.Fourier.LatticeRestriction -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open Set
open scoped Classical
namespace Fourier.LatticeGraph

@[expose] def restrictVertices (G : LatticeGraph) (P : Site → Prop) : Finset Site := G.vertices.filter P

@[expose] def restrictVertex (G : LatticeGraph) (P : Site → Prop) (v : G.restrictVertices P) : G.vertices :=
  ⟨v.val,(Finset.mem_filter.mp v.property).1⟩

@[expose] def restrict (G : LatticeGraph) (P : Site → Prop) : LatticeGraph where
  vertices := G.restrictVertices P
  edges := Finset.univ.filter (fun e : G.restrictVertices P × G.restrictVertices P =>
    (G.restrictVertex P e.1,G.restrictVertex P e.2)∈G.edges)
  nearest _e he := G.nearest _ (Finset.mem_filter.mp he).2

@[expose] def restrictEdge (G : LatticeGraph) (P : Site → Prop) (e : (G.restrict P).edges) : G.edges :=
  ⟨(G.restrictVertex P e.val.1,G.restrictVertex P e.val.2),(Finset.mem_filter.mp e.property).2⟩

@[expose] def restrictVertexEquiv (G : LatticeGraph) (P : Site → Prop) :
    {v : G.vertices // P v.val} ≃ (G.restrict P).vertices where
  toFun v := ⟨v.val.val,Finset.mem_filter.mpr ⟨v.val.property,v.property⟩⟩
  invFun v := ⟨G.restrictVertex P v,(Finset.mem_filter.mp v.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def restrictEdgeEquiv (G : LatticeGraph) (P : Site → Prop) :
    {e : G.edges // P e.val.1.val ∧ P e.val.2.val} ≃ (G.restrict P).edges where
  toFun e := ⟨(⟨e.val.val.1.val,Finset.mem_filter.mpr ⟨e.val.val.1.property,e.property.1⟩⟩,
    ⟨e.val.val.2.val,Finset.mem_filter.mpr ⟨e.val.val.2.property,e.property.2⟩⟩),
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.val.property⟩⟩
  invFun e := ⟨G.restrictEdge P e,(Finset.mem_filter.mp e.val.1.property).2,
    (Finset.mem_filter.mp e.val.2.property).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem restrictVertexEquiv_val (G : LatticeGraph) (P : Site → Prop)
    (v : {v : G.vertices // P v.val}) : (G.restrictVertexEquiv P v).val=v.val.val := rfl

@[simp] theorem restrictEdgeEquiv_left (G : LatticeGraph) (P : Site → Prop)
    (e : {e : G.edges // P e.val.1.val ∧ P e.val.2.val}) :
    (G.restrictEdgeEquiv P e).val.1=G.restrictVertexEquiv P ⟨e.val.val.1,e.property.1⟩ := rfl

@[simp] theorem restrictEdgeEquiv_right (G : LatticeGraph) (P : Site → Prop)
    (e : {e : G.edges // P e.val.1.val ∧ P e.val.2.val}) :
    (G.restrictEdgeEquiv P e).val.2=G.restrictVertexEquiv P ⟨e.val.val.2,e.property.2⟩ := rfl

@[expose] def translateVertexEquiv (G : LatticeGraph) (z : Site) :
    G.vertices ≃ G.vertices.map (Equiv.addRight (-z)).toEmbedding :=
  Finset.equivMap (Equiv.addRight (-z)).toEmbedding G.vertices

@[expose] def translate (G : LatticeGraph) (z : Site) : LatticeGraph where
  vertices := G.vertices.map (Equiv.addRight (-z)).toEmbedding
  edges := G.edges.map ((Equiv.prodCongr (G.translateVertexEquiv z) (G.translateVertexEquiv z)).toEmbedding)
  nearest e he := by
    obtain ⟨e',he',rfl⟩ := Finset.mem_map.mp he
    have h := G.nearest e' he'
    change PositiveNeighbor (e'.1.val+-z) (e'.2.val+-z)
    rcases h with h | h
    · left
      constructor <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
      · omega
      · omega
    · right
      constructor <;> simp only [Prod.fst_add,Prod.snd_add,Prod.fst_neg,Prod.snd_neg]
      · omega
      · omega

@[expose] def translateEdgeEquiv (G : LatticeGraph) (z : Site) : G.edges ≃ (G.translate z).edges :=
  Finset.equivMap ((Equiv.prodCongr (G.translateVertexEquiv z) (G.translateVertexEquiv z)).toEmbedding) G.edges

@[simp] theorem translateVertexEquiv_val (G : LatticeGraph) (z : Site) (v : G.vertices) :
    (G.translateVertexEquiv z v).val=v.val-z := rfl

@[simp] theorem translateEdgeEquiv_left (G : LatticeGraph) (z : Site) (e : G.edges) :
    (G.translateEdgeEquiv z e).val.1=G.translateVertexEquiv z e.val.1 := rfl

@[simp] theorem translateEdgeEquiv_right (G : LatticeGraph) (z : Site) (e : G.edges) :
    (G.translateEdgeEquiv z e).val.2=G.translateVertexEquiv z e.val.2 := rfl

end Fourier.LatticeGraph

end

end RP3

/-! Module: RP3.Fourier.LatticeRadius -/

/-! Interaction-independent Fourier and lattice analysis, adapted from the
OpenAI ClassicalON formalization (commit adc7f1241b42e322a6451854ab7e4b4c146bf78a). -/

namespace RP3

noncomputable section
open Set
open scoped Classical
namespace Fourier

@[expose] def siteRadius (z v : Site) : ℤ := max |v.1-z.1| |v.2-z.2|

@[simp] theorem siteRadius_self (z : Site) : siteRadius z z=0 := by simp [siteRadius]

theorem siteRadius_nonneg (z v : Site) : 0≤ siteRadius z v := le_trans (abs_nonneg _) (le_max_left _ _)

theorem siteRadius_symm (z v : Site) : siteRadius z v=siteRadius v z := by
  simp only [siteRadius,abs_sub_comm]

theorem siteRadius_le_iff (z v : Site) (N : ℤ) :
    siteRadius z v≤N ↔ |v.1-z.1|≤N ∧ |v.2-z.2|≤N := max_le_iff

theorem siteRadius_triangle (x y z : Site) : siteRadius x z≤ siteRadius x y+siteRadius y z := by
  apply max_le
  · have h := abs_add_le (y.1-x.1) (z.1-y.1)
    have h1 : |y.1-x.1|≤ siteRadius x y := le_max_left _ _
    have h2 : |z.1-y.1|≤ siteRadius y z := le_max_left _ _
    have he : (y.1-x.1)+(z.1-y.1)=z.1-x.1 := by ring
    rw [he] at h
    omega
  · have h := abs_add_le (y.2-x.2) (z.2-y.2)
    have h1 : |y.2-x.2|≤ siteRadius x y := le_max_right _ _
    have h2 : |z.2-y.2|≤ siteRadius y z := le_max_right _ _
    have he : (y.2-x.2)+(z.2-y.2)=z.2-x.2 := by ring
    rw [he] at h
    omega

theorem siteRadius_neighbor {x y : Site} (h : PositiveNeighbor x y) : siteRadius x y=1 := by
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> simp [siteRadius,h1,h2]

theorem siteRadius_neighbor_step (z : Site) {x y : Site} (h : PositiveNeighbor x y ∨ PositiveNeighbor y x) :
    siteRadius z y≤ siteRadius z x+1 ∧ siteRadius z x≤ siteRadius z y+1 := by
  have hh : siteRadius x y=1 := by
    rcases h with h | h
    · exact siteRadius_neighbor h
    · rw [siteRadius_symm]; exact siteRadius_neighbor h
  constructor
  · simpa only [hh] using siteRadius_triangle z x y
  · have := siteRadius_triangle z y x
    rwa [siteRadius_symm y x,hh] at this

@[expose] def annulusSites (N : ℤ) (z : Site) : Set Site := {v | N≤ siteRadius z v ∧ siteRadius z v≤2*N}

@[expose] def annulusBoundary (N : ℤ) (z : Site) : Set Site := {v | siteRadius z v=N ∨ siteRadius z v=2*N}

@[expose] def annulusInterior (N : ℤ) (z : Site) : Set Site := {v | N<siteRadius z v ∧ siteRadius z v<2*N}

theorem annulusSites_not_boundary (N : ℤ) (z v : Site) :
    v∈annulusSites N z ∧ v∉annulusBoundary N z ↔ v∈annulusInterior N z := by
  simp only [annulusSites,annulusBoundary,annulusInterior,mem_ofPred_eq]
  omega

theorem neighbor_in_annulus {N : ℤ} {z x y : Site} (hx : x∈annulusInterior N z)
    (hxy : PositiveNeighbor x y ∨ PositiveNeighbor y x) : y∈annulusSites N z := by
  have hh := siteRadius_neighbor_step z hxy
  change N<siteRadius z x ∧ siteRadius z x<2*N at hx
  change N≤ siteRadius z y ∧ siteRadius z y≤2*N
  omega

theorem annuli_disjoint {N : ℤ} {x y : Site} (hxy : 4*N<siteRadius x y) :
    Disjoint (annulusSites N x) (annulusSites N y) := by
  apply Set.disjoint_left.mpr
  intro z hx hy
  have ht := siteRadius_triangle x z y
  rw [siteRadius_symm z y] at ht
  change N≤ siteRadius x z ∧ siteRadius x z≤2*N at hx
  change N≤ siteRadius y z ∧ siteRadius y z≤2*N at hy
  omega

namespace LatticeGraph

@[expose] def annulusGraph (G : LatticeGraph) (N : ℤ) (z : Site) := G.restrict (·∈annulusSites N z)

@[expose] def annulusInner (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  {v | siteRadius z v.val=N}

@[expose] def annulusOuter (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  {v | siteRadius z v.val=2*N}

@[expose] def annulusPins (G : LatticeGraph) (N : ℤ) (z : Site) : Set (G.annulusGraph N z).vertices :=
  G.annulusInner N z∪G.annulusOuter N z

@[expose] def annulusCoupling (G : LatticeGraph) (b : G.edges → ℝ) (N : ℤ) (z : Site) :
    (G.annulusGraph N z).edges → ℝ := fun e => b (G.restrictEdge _ e)

end LatticeGraph
end Fourier

end

end RP3
/-! Module: RP3.Fourier.ResponseEstimates -/

/-!
# Quantitative numerical consequences of the Fourier family construction

These intermediate lemmas keep the response argument explicit; the actual
RP³ response is substituted in the model-specific analytic assembly.
-/
namespace RP3.Fourier
noncomputable section
open scoped BigOperators
namespace LatticeGraph

@[expose] def rotationCostConstant (M C : ℝ) : ℝ :=
  4*((6*M^2+4*M*Real.sqrt M+M)*(48*(2*modeBlockConstant C)^4)+
        M*(576*C^2*(2*modeBlockConstant C)^2))

@[expose] def transferCostConstant (M L D : ℝ) : ℝ :=
  M*(512*D*(2*L+D)) + (M*512*D)*(M*(512*L^2)+1) + (M*512*D)^2

theorem rotationCostConstant_nonneg (M C : ℝ) (hM : 0 ≤ M) :
    0 ≤ rotationCostConstant M C := by unfold rotationCostConstant; positivity

theorem transferCostConstant_nonneg (M L D : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    0 ≤ transferCostConstant M L D := by unfold transferCostConstant; positivity

/-- The Fourier normalization converts a family bound of order k into a
single profile response bound of order 1/k. -/
theorem profile_response_bound_of_family (G : LatticeGraph) (k : ℕ) (hk : 0 < k)
    (hG : G.WithinDyadicBox k) (M : ℝ) (hM : 0 ≤ M)
    (C : ℝ) (hC : 0 ≤ C) (hv : ∀ m s z, |squareProfile m s z| ≤ C)
    (hLip : ∀ m s z w, |squareProfile m s w-squareProfile m s z| ≤ C*‖w-z‖)
    (R : ℝ)
    (hfamily : -(dyadicLambda k)^2 * R ≤
      (6*M^2+4*M*Real.sqrt M+M)*familyHSSquare (G.modeDifferences (k := k)) +
        M * (∑ i : ModeIndex k, ∑ j : ModeIndex k,
          min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
            (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2))) :
    -R ≤ rotationCostConstant M C/(k:ℝ) := by
  let a := 2*modeBlockConstant C
  let T := (6*M^2+4*M*Real.sqrt M+M)*(48*a^4)+M*(576*C^2*a^2)
  have ha (m s : Bool) := G.scaledModes_squareBound hG C hv hLip m s
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hLam : (k:ℝ)/2 ≤ dyadicLambda k := dyadicLambda_lower k
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hLp : 0 < dyadicLambda k := by linarith
  have hHS := G.modes_HS_bound a ha
  have hmin := G.modes_min_bound a C hC hv ha
  have hK : 0 ≤ 6*M^2+4*M*Real.sqrt M+M := by positivity
  have hcost : (6*M^2+4*M*Real.sqrt M+M)*familyHSSquare (G.modeDifferences (k := k))+
      M*(∑ i : ModeIndex k, ∑ j : ModeIndex k,
      min (‖G.modes i‖^2*∑ e, ‖G.modeDifferences j e‖^2)
          (‖G.modes j‖^2*∑ e, ‖G.modeDifferences i e‖^2)) ≤ T*(k:ℝ) := by
    calc _ ≤ (6*M^2+4*M*Real.sqrt M+M)*(48*a^4*(k:ℝ))+M*(576*C^2*a^2*(k:ℝ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hHS hK) (mul_le_mul_of_nonneg_left hmin hM)
      _ = _ := by dsimp only [T]; ring
  change -R ≤ 4*T/(k:ℝ)
  by_cases hr : R ≤ 0
  · apply (le_div_iff₀ hkR).mpr
    have hsq : (k:ℝ)^2/4 ≤ (dyadicLambda k)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right hsq (neg_nonneg.mpr hr)
    have ht := hfamily.trans hcost
    nlinarith
  · have hh : 0 ≤ 4*T/(k:ℝ) := by positivity
    linarith

/-- Real-response transfer with a common derivative bound M. -/
theorem theta_response_bound_of_transfer (G : LatticeGraph) (k : ℕ)
    (hG : G.WithinDyadicBox k) (M L D a R : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (he : ∀ e : G.edges, |G.thetaEdge k e| ≤ L/(2:ℝ)^k ∧
      |G.thetaEdge k e-G.profileEdge k e| ≤ D/((2:ℝ)^k)^3)
    (htransfer : -R ≤ a +
      M*(∑ e, |G.thetaEdge k e-G.profileEdge k e| *
        (|G.thetaEdge k e|+|G.profileEdge k e|)) +
      (M*∑ e, |G.thetaEdge k e-G.profileEdge k e|) *
        (M*(∑ e, (G.thetaEdge k e)^2)+1) +
      (M*∑ e, |G.thetaEdge k e-G.profileEdge k e|)^2) :
    -R ≤ a+transferCostConstant M L D/(2:ℝ)^k := by
  let N : ℝ := (2:ℝ)^k
  have hN : 0 < N := by dsimp [N]; positivity
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  obtain ⟨hs1,hs2,hs3⟩ := G.theta_sum_bounds k hG L D hL hD he
  simp only [sq_abs] at hs2
  have h1n : 0 ≤ M*∑ e, |G.thetaEdge k e-G.profileEdge k e| := by positivity
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

/-- A scale-uniform 1/k form is convenient for nesting annuli. -/
theorem dyadic_error_le_inverse_scale (k : ℕ) (hk : 0 < k) (A B : ℝ) (hB : 0 ≤ B) :
    A/(k:ℝ)+B/(2:ℝ)^k ≤ (A+B)/(k:ℝ) := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hpow : (k:ℝ) ≤ (2:ℝ)^k := by exact_mod_cast k.lt_two_pow_self.le
  calc _ ≤ A/(k:ℝ)+B/(k:ℝ) :=
      add_le_add le_rfl (div_le_div_of_nonneg_left hB hkR hpow)
    _ = _ := by ring

end LatticeGraph
end
end RP3.Fourier