module

public import RP2.RotationGeometry
public import RP2.PinnedKernel
public import RP2.NestedCuts

public section

/-!
# Concrete continuity and symmetry of pinned RP² kernels

The lemmas here discharge the continuity, boundary locality, and simultaneous
rotation obligations for the actual pinned partition function. They do not
assert the annular analytic estimate or a lattice factorisation.
-/
namespace RP2
noncomputable section
open MeasureTheory
open scoped InnerProductSpace

variable {V E G : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- The pinned partition function depends continuously on every boundary spin. -/
theorem continuous_pinnedPartition (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) : Continuous (pinnedPartition edge b pins) := by
  have hfill : Continuous (fun z : Configuration V × Configuration V =>
      fillPins pins z.1 z.2) := by
    apply continuous_pi
    intro v
    by_cases hv : v ∈ pins <;> simp only [fillPins, ContinuousMap.coe_mk, hv,
      ite_true, ite_false] <;> fun_prop
  have hf : Continuous (Function.uncurry (fun τ σ : Configuration V =>
      Real.exp (interaction edge b (fillPins pins τ σ)))) :=
    (weight edge b).continuous.comp hfill
  have hc := continuous_parametric_integral_of_continuous
    (μ := referenceLaw (V := V)) hf isCompact_univ
  change Continuous (fun τ => ∫ σ, Real.exp
    (interaction edge b (fillPins pins τ σ)) ∂referenceLaw)
  simpa only [Measure.restrict_univ] using hc

/-- The actual pinned partition function as a continuous boundary kernel. -/
@[expose] def pinnedKernel (edge : E → V × V) (b : E → ℝ) (pins : Finset V) :
    C(Configuration V, ℝ) :=
  ⟨pinnedPartition edge b pins, continuous_pinnedPartition edge b pins⟩

@[simp] theorem pinnedKernel_apply (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (τ : Configuration V) :
    pinnedKernel edge b pins τ = pinnedPartition edge b pins τ := rfl

/-- Values at unpinned sites are dummy boundary variables. -/
theorem pinnedPartition_congr (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) {τ υ : Configuration V}
    (h : ∀ v ∈ pins, τ v = υ v) :
    pinnedPartition edge b pins τ = pinnedPartition edge b pins υ := by
  have hfill : fillPins pins τ = fillPins pins υ := by
    ext σ v
    by_cases hv : v ∈ pins
    · simp [fillPins, hv, h v hv]
    · simp [fillPins, hv]
  simp only [pinnedPartition, pinnedWeight, hfill]

/-- A common orthogonal rotation preserves every squared edge interaction. -/
theorem interaction_globalRotation (edge : E → V × V) (b : E → ℝ)
    (R : E3 ≃ₗᵢ[ℝ] E3) (σ : Configuration V) :
    interaction edge b (fun v => Rotation.spinRotation R (σ v)) =
      interaction edge b σ := by
  unfold interaction
  apply Finset.sum_congr rfl
  intro e _
  simp only [Rotation.spinRotation_val, R.inner_map_map]

/-- Arbitrary pinned arrays can be rotated together without changing the kernel. -/
theorem pinnedPartition_globalRotation (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (R : E3 ≃ₗᵢ[ℝ] E3) (τ : Configuration V) :
    pinnedPartition edge b pins (fun v => Rotation.spinRotation R (τ v)) =
      pinnedPartition edge b pins τ := by
  let U := Homeomorph.piCongrRight (fun _ : V => Rotation.spinRotation R)
  have hm : MeasurePreserving U (referenceLaw (V := V)) (referenceLaw (V := V)) := by
    exact measurePreserving_pi _ _ (fun _ => Rotation.spinRotation_preserves_probability R)
  have hfill (σ : Configuration V) :
      fillPins pins (fun v => Rotation.spinRotation R (τ v)) (U σ) =
        fun v => Rotation.spinRotation R (fillPins pins τ σ v) := by
    funext v
    by_cases hv : v ∈ pins <;> simp [fillPins, U, hv]
  change (∫ σ, Real.exp (interaction edge b
    (fillPins pins (fun v => Rotation.spinRotation R (τ v)) σ)) ∂referenceLaw) =
      ∫ σ, Real.exp (interaction edge b (fillPins pins τ σ)) ∂referenceLaw
  rw [← hm.integral_comp U.measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with σ
  rw [hfill, interaction_globalRotation]

/-- Filling some coordinates from each of two independent configurations
preserves the product reference probability. -/
theorem fillPins_product_measurePreserving (pins : Finset V) :
    MeasurePreserving
      (fun z : Configuration V × Configuration V => fillPins pins z.1 z.2)
      ((referenceLaw (V := V)).prod referenceLaw) referenceLaw := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Spin Spin V
  have he := measurePreserving_arrowProdEquivProdArrow Spin Spin V
    (fun _ => sphereProbability) (fun _ => sphereProbability)
  have hc : ∀ v : V, MeasurePreserving
      (fun z : Spin × Spin => if v ∈ pins then z.1 else z.2)
      (sphereProbability.prod sphereProbability) sphereProbability := by
    intro v
    by_cases hv : v ∈ pins
    · simpa only [hv, ite_true] using
        (measurePreserving_fst : MeasurePreserving Prod.fst
          (sphereProbability.prod sphereProbability) sphereProbability)
    · simpa only [hv, ite_false] using
        (measurePreserving_snd : MeasurePreserving Prod.snd
          (sphereProbability.prod sphereProbability) sphereProbability)
  exact (measurePreserving_pi _ _ hc).comp (MeasurePreserving.symm e he)

/-- Exact elimination of dummy boundary integration variables. -/
theorem integral_fillPins (pins : Finset V) (f : C(Configuration V, ℝ)) :
    (∫ τ, ∫ σ, f (fillPins pins τ σ) ∂referenceLaw ∂referenceLaw) =
      ∫ σ, f σ ∂referenceLaw := by
  have hc : Continuous (fun z : Configuration V × Configuration V =>
      f (fillPins pins z.1 z.2)) := by
    apply f.continuous.comp
    apply continuous_pi
    intro v
    by_cases hv : v ∈ pins <;> simp only [fillPins, ContinuousMap.coe_mk, hv,
      ite_true, ite_false] <;> fun_prop
  rw [← integral_prod _ (hc.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _))]
  have hm := fillPins_product_measurePreserving pins
  have hi := integral_map_of_stronglyMeasurable
    (μ := (referenceLaw (V := V)).prod referenceLaw) hm.measurable
    f.continuous.stronglyMeasurable
  rw [hm.map_eq] at hi
  exact hi.symm

/-- Fubini factorisation for one actual annular kernel. The other factor may
contain the observable as well as arbitrary exterior interactions. -/
theorem pinnedKernel_weighted_factorization (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) (outside : C(Configuration V, ℝ))
    (hout : ∀ τ σ, outside (fillPins pins τ σ) = outside τ) :
    (∫ τ, outside τ * pinnedKernel edge b pins τ ∂referenceLaw) =
      ∫ σ, outside σ * weight edge b σ ∂referenceLaw := by
  calc
    _ = ∫ τ, ∫ σ, (outside * weight edge b) (fillPins pins τ σ)
          ∂referenceLaw ∂referenceLaw := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [pinnedKernel_apply, pinnedPartition, pinnedWeight,
        integralOnCompact, ContinuousMap.mul_apply, ContinuousMap.comp_apply, hout]
      exact (integral_const_mul _ _).symm
    _ = _ := integral_fillPins pins (outside * weight edge b)

/-- A continuous function depends only on the specified coordinates. -/
@[expose] def DependsOnPins (pins : Finset V) (f : C(Configuration V, ℝ)) : Prop :=
  ∀ τ σ, f (fillPins pins τ σ) = f τ

/-- Edge weights are local, including when a common edge type is used with
zero couplings to remove the edges outside a chosen region. -/
theorem weight_dependsOnPins (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V)
    (hedge : ∀ e, b e = 0 ∨ ((edge e).1 ∈ pins ∧ (edge e).2 ∈ pins)) :
    DependsOnPins pins (weight edge b) := by
  intro τ σ
  apply congrArg Real.exp
  apply Finset.sum_congr rfl
  intro e _
  rcases hedge e with he | ⟨hl, hr⟩
  · simp only [he, zero_mul]
  · simp only [fillPins, ContinuousMap.coe_mk, hl, hr, ite_true]

theorem observable_dependsOnPins (pins : Finset V) (x y : V)
    (hx : x ∈ pins) (hy : y ∈ pins) :
    DependsOnPins pins (observable x y) := by
  intro τ σ
  simp only [observable, ContinuousMap.coe_mk, fillPins, hx, hy, ite_true]

/-- Integration over the complement of a pin set, with the remaining
coordinates retained as continuous parameters. -/
@[expose] def boundaryAverage (pins : Finset V) (f : C(Configuration V, ℝ)) :
    C(Configuration V, ℝ) where
  toFun τ := ∫ σ, f (fillPins pins τ σ) ∂referenceLaw
  continuous_toFun := by
    have hf : Continuous (Function.uncurry (fun τ σ : Configuration V =>
        f (fillPins pins τ σ))) := by
      apply f.continuous.comp
      apply continuous_pi
      intro v
      by_cases hv : v ∈ pins <;> simp only [fillPins, ContinuousMap.coe_mk, hv,
        ite_true, ite_false] <;> fun_prop
    simpa only [Measure.restrict_univ] using
      (continuous_parametric_integral_of_continuous
        (μ := referenceLaw (V := V)) hf isCompact_univ)

@[simp] theorem boundaryAverage_apply (pins : Finset V)
    (f : C(Configuration V, ℝ)) (τ : Configuration V) :
    boundaryAverage pins f τ = ∫ σ, f (fillPins pins τ σ) ∂referenceLaw := rfl

theorem pinnedKernel_eq_boundaryAverage (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) : pinnedKernel edge b pins = boundaryAverage pins (weight edge b) := rfl

theorem boundaryAverage_dependsOnPins (pins : Finset V)
    (f : C(Configuration V, ℝ)) : DependsOnPins pins (boundaryAverage pins f) := by
  intro τ σ
  apply integral_congr_ae
  filter_upwards with υ
  congr 1
  funext v
  by_cases hv : v ∈ pins <;> simp [fillPins, hv]

theorem pinnedKernel_dependsOnPins (edge : E → V × V) (b : E → ℝ)
    (pins : Finset V) : DependsOnPins pins (pinnedKernel edge b pins) :=
  boundaryAverage_dependsOnPins pins (weight edge b)

theorem DependsOnPins.mul {pins : Finset V} {f g : C(Configuration V, ℝ)}
    (hf : DependsOnPins pins f) (hg : DependsOnPins pins g) :
    DependsOnPins pins (f * g) := by
  intro τ σ
  simp only [ContinuousMap.mul_apply, hf τ σ, hg τ σ]

theorem dependsOnPins_one (pins : Finset V) :
    DependsOnPins pins (1 : C(Configuration V, ℝ)) := fun _ _ => rfl

theorem dependsOnPins_prod {ι : Type*} (s : Finset ι) (pins : Finset V)
    (f : ι → C(Configuration V, ℝ)) (hf : ∀ i ∈ s, DependsOnPins pins (f i)) :
    DependsOnPins pins (∏ i ∈ s, f i) := by
  intro τ σ
  simp only [ContinuousMap.prod_apply]
  exact Finset.prod_congr rfl (fun i hi => hf i hi τ σ)

/-- Averaging other coordinates cannot create a dependence on coordinates
that the original function did not use. -/
theorem DependsOnPins.boundaryAverage {pins : Finset V} {f : C(Configuration V, ℝ)}
    (hf : DependsOnPins pins f) (other : Finset V) :
    DependsOnPins pins (boundaryAverage other f) := by
  intro τ σ
  apply integral_congr_ae
  filter_upwards with υ
  have he : fillPins other (fillPins pins τ σ) υ =
      fillPins pins (fillPins other τ υ) (fillPins other σ υ) := by
    funext v
    by_cases hp : v ∈ pins <;> by_cases ho : v ∈ other <;>
      simp [fillPins, hp, ho]
  rw [he, hf]

/-- Exact conditional integration, with any factor depending only on pins
pulled outside the inner integral. -/
theorem integral_mul_boundaryAverage (pins : Finset V)
    (outside f : C(Configuration V, ℝ)) (hout : DependsOnPins pins outside) :
    (∫ τ, outside τ * boundaryAverage pins f τ ∂referenceLaw) =
      ∫ σ, outside σ * f σ ∂referenceLaw := by
  calc
    _ = ∫ τ, ∫ σ, (outside * f) (fillPins pins τ σ)
          ∂referenceLaw ∂referenceLaw := by
      apply integral_congr_ae
      filter_upwards with τ
      simp only [boundaryAverage_apply, ContinuousMap.mul_apply, hout τ]
      exact (integral_const_mul _ _).symm
    _ = _ := integral_fillPins pins (outside * f)

/-- Exact simultaneous integration of any finite family of noninteracting
interiors. The original factors may share arbitrary boundary coordinates;
statistical independence of the Gibbs measure is not assumed. -/
theorem integral_product_boundaryAverage {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (pins : ι → Finset V) (f : ι → C(Configuration V, ℝ))
    (outside : C(Configuration V, ℝ))
    (hout : ∀ i ∈ s, DependsOnPins (pins i) outside)
    (hcross : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → DependsOnPins (pins i) (f j)) :
    (∫ τ, (outside * ∏ i ∈ s, boundaryAverage (pins i) (f i)) τ ∂referenceLaw) =
      ∫ τ, (outside * ∏ i ∈ s, f i) τ ∂referenceLaw := by
  induction s using Finset.induction_on generalizing outside with
  | empty => simp
  | @insert i s hi ih =>
    have houti := hout i (Finset.mem_insert_self i s)
    have houts : ∀ j ∈ s, DependsOnPins (pins j)
        (outside * boundaryAverage (pins i) (f i)) := by
      intro j hj
      exact (hout j (Finset.mem_insert_of_mem hj)).mul
        ((hcross j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
          (by intro he; subst j; exact hi hj)).boundaryAverage (pins i))
    have hcrosss : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → DependsOnPins (pins a) (f b) :=
      fun a ha b hb hab => hcross a (Finset.mem_insert_of_mem ha)
        b (Finset.mem_insert_of_mem hb) hab
    have hfi : DependsOnPins (pins i) (outside * ∏ j ∈ s, f j) :=
      houti.mul (dependsOnPins_prod s (pins i) f (fun j hj =>
        hcross i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
          (by intro he; subst j; exact hi hj)))
    simp only [Finset.prod_insert hi]
    calc
      _ = ∫ τ, ((outside * boundaryAverage (pins i) (f i)) *
            ∏ j ∈ s, boundaryAverage (pins j) (f j)) τ ∂referenceLaw := by
        congr 1
        ext τ
        simp only [ContinuousMap.mul_apply]
        ring
      _ = ∫ τ, ((outside * boundaryAverage (pins i) (f i)) *
            ∏ j ∈ s, f j) τ ∂referenceLaw := ih _ houts hcrosss
      _ = ∫ τ, (outside * ∏ j ∈ s, f j) τ *
            boundaryAverage (pins i) (f i) τ ∂referenceLaw := by
        congr 1
        ext τ
        simp only [ContinuousMap.mul_apply]
        ring
      _ = ∫ τ, (outside * ∏ j ∈ s, f j) τ * f i τ ∂referenceLaw :=
        integral_mul_boundaryAverage (pins i) _ _ hfi
      _ = _ := by
        congr 1
        ext τ
        simp only [ContinuousMap.mul_apply]
        ring

/-- Pinning additional sites that are not edge endpoints does not alter the
annular kernel. This identifies a reduced boundary kernel with one that uses
the complement of its strict interior as the pin set. -/
theorem pinnedPartition_congr_pins (edge : E → V × V) (b : E → ℝ)
    (pins pins' : Finset V)
    (hleft : ∀ e, (edge e).1 ∈ pins ↔ (edge e).1 ∈ pins')
    (hright : ∀ e, (edge e).2 ∈ pins ↔ (edge e).2 ∈ pins')
    (τ : Configuration V) :
    pinnedPartition edge b pins τ = pinnedPartition edge b pins' τ := by
  change (∫ σ, Real.exp (interaction edge b (fillPins pins τ σ)) ∂referenceLaw) =
    ∫ σ, Real.exp (interaction edge b (fillPins pins' τ σ)) ∂referenceLaw
  apply integral_congr_ae
  filter_upwards with σ
  apply congrArg Real.exp
  apply Finset.sum_congr rfl
  intro e _
  simp only [fillPins, ContinuousMap.coe_mk, hleft e, hright e]

section CutSymmetry
variable [Group G] [Fintype G]
variable (A : FiniteAction G Spin) (ρ : G → E3 ≃ₗᵢ[ℝ] E3)
  (hρ : ∀ g s, A.move g s = Rotation.spinRotation (ρ g) s)
include ρ hρ

/-- A cut rotation leaves a pinned kernel fixed if it contains all pinned sites,
or none of them. This is the concrete locality used for distinct annuli. -/
theorem pinnedKernel_cut_invariant (edge : E → V × V) (b : E → ℝ)
    (pins cut : Finset V) (hsep : pins ⊆ cut ∨ Disjoint pins cut)
    (g : G) (τ : Configuration V) :
    pinnedKernel edge b pins ((A.onCut cut).move g τ) =
      pinnedKernel edge b pins τ := by
  rcases hsep with hin | hout
  · calc
      pinnedKernel edge b pins ((A.onCut cut).move g τ) =
          pinnedPartition edge b pins (fun v => Rotation.spinRotation (ρ g) (τ v)) := by
        apply pinnedPartition_congr
        intro v hv
        simp only [FiniteAction.onCut_apply, hin hv, ite_true, hρ]
      _ = _ := pinnedPartition_globalRotation edge b pins (ρ g) τ
  · apply pinnedPartition_congr
    intro v hv
    have hn : v ∉ cut := fun hc => Finset.disjoint_left.mp hout hv hc
    simp [FiniteAction.onCut_apply, hn]

/-- The corresponding average fixes the actual pinned kernel. -/
theorem pinnedKernel_cut_average (edge : E → V × V) (b : E → ℝ)
    (pins cut : Finset V) (hsep : pins ⊆ cut ∨ Disjoint pins cut) :
    (A.onCut cut).average (pinnedKernel edge b pins) = pinnedKernel edge b pins :=
  (A.onCut cut).average_of_invariant _
    (pinnedKernel_cut_invariant A ρ hρ edge b pins cut hsep)

/-- An ordinary remaining-region weight is invariant under a cut if no
interaction edge crosses that cut. -/
theorem weight_cut_invariant (edge : E → V × V) (b : E → ℝ)
    (cut : Finset V)
    (hcut : ∀ e, b e = 0 ∨ ((edge e).1 ∈ cut ↔ (edge e).2 ∈ cut))
    (g : G) (σ : Configuration V) :
    weight edge b ((A.onCut cut).move g σ) = weight edge b σ := by
  apply congrArg Real.exp
  apply Finset.sum_congr rfl
  intro e _
  rcases hcut e with hb | he
  · simp only [hb, zero_mul]
  by_cases hl : (edge e).1 ∈ cut
  · have hr := he.mp hl
    simp only [FiniteAction.onCut_apply, hl, hr, ite_true, hρ,
      Rotation.spinRotation_val, (ρ g).inner_map_map]
  · have hr : (edge e).2 ∉ cut := fun hh => hl (he.mpr hh)
    simp only [FiniteAction.onCut_apply, hl, hr, ite_false]

/-- No-crossing edge geometry discharges the base-weight averaging obligation. -/
theorem weight_cut_average (edge : E → V × V) (b : E → ℝ)
    (cut : Finset V)
    (hcut : ∀ e, b e = 0 ∨ ((edge e).1 ∈ cut ↔ (edge e).2 ∈ cut)) :
    (A.onCut cut).average (weight edge b) = weight edge b :=
  (A.onCut cut).average_of_invariant _
    (weight_cut_invariant A ρ hρ edge b cut hcut)

/-- No active edge crossing a cut implies invariance of the pinned kernel,
for an arbitrary pin set. The unpinned spins undergo the same change of
variables, so the boundary need not be rotated uniformly across the graph. -/
theorem pinnedKernel_cut_invariant_of_edges (edge : E → V × V) (b : E → ℝ)
    (pins cut : Finset V)
    (hcut : ∀ e, b e = 0 ∨ ((edge e).1 ∈ cut ↔ (edge e).2 ∈ cut))
    (g : G) (τ : Configuration V) :
    pinnedKernel edge b pins ((A.onCut cut).move g τ) =
      pinnedKernel edge b pins τ := by
  have hμ : ∀ g, MeasurePreserving (A.move g) sphereProbability sphereProbability := by
    intro h
    have he : (A.move h : Spin → Spin) = Rotation.spinRotation (ρ h) :=
      funext (hρ h)
    rw [he]
    exact Rotation.spinRotation_preserves_probability (ρ h)
  have hm : MeasurePreserving ((A.onCut cut).move g)
      (referenceLaw (V := V)) referenceLaw :=
    A.onCut_measurePreserving sphereProbability hμ cut g
  have hfill (σ : Configuration V) :
      fillPins pins ((A.onCut cut).move g τ) ((A.onCut cut).move g σ) =
        (A.onCut cut).move g (fillPins pins τ σ) := by
    funext v
    by_cases hp : v ∈ pins <;> by_cases hc : v ∈ cut <;>
      simp [fillPins, FiniteAction.onCut_apply, hp, hc]
  change (∫ σ, weight edge b (fillPins pins ((A.onCut cut).move g τ) σ)
      ∂referenceLaw) = ∫ σ, weight edge b (fillPins pins τ σ) ∂referenceLaw
  rw [← hm.integral_comp ((A.onCut cut).toHomeomorph g).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with σ
  rw [hfill, weight_cut_invariant A ρ hρ edge b cut hcut]

theorem pinnedKernel_cut_average_of_edges (edge : E → V × V) (b : E → ℝ)
    (pins cut : Finset V)
    (hcut : ∀ e, b e = 0 ∨ ((edge e).1 ∈ cut ↔ (edge e).2 ∈ cut)) :
    (A.onCut cut).average (pinnedKernel edge b pins) = pinnedKernel edge b pins :=
  (A.onCut cut).average_of_invariant _
    (pinnedKernel_cut_invariant_of_edges A ρ hρ edge b pins cut hcut)

omit ρ hρ in
/-- Single-spin quadrupole cancellation implies cancellation of the observable
under every cut separating its two sites. -/
theorem observable_cut_average_zero
    (hcancel : ∀ s t : Spin, ∑ g : G, qPair (A.move g s) t = 0)
    (cut : Finset V) (x y : V) (hx : x ∈ cut) (hy : y ∉ cut) :
    (A.onCut cut).average (observable x y) = 0 := by
  ext σ
  simp only [FiniteAction.average_apply, observable, ContinuousMap.coe_mk,
    FiniteAction.onCut_apply, hx, hy, ite_true, ite_false,
    hcancel, mul_zero, ContinuousMap.zero_apply]

end CutSymmetry
end
end RP2
