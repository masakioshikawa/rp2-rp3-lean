module

public import RP3.Model
public import RP3.FourierAll

public section

/-!
# Free-boundary probability measures and their local weak limits

The Gibbs probability measures are constructed from their actual densities.
Their two-spin marginals have the quadrupolar expectation defined in `Model`.
Weak convergence of these marginals therefore preserves the uniform finite-volume
bound with exactly the same constants.
-/
namespace RP3

noncomputable section
open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

section GibbsMeasure
variable {V E : Type*} [Fintype V] [Fintype E]

/-- Normalized free-boundary Gibbs density with respect to the product surface law. -/
@[expose] def freeGibbsDensity (edge : E → V × V) (b : E → ℝ) (σ : Configuration V) : ℝ :=
  weight edge b σ / partition edge b

theorem continuous_freeGibbsDensity (edge : E → V × V) (b : E → ℝ) :
    Continuous (freeGibbsDensity edge b) := by
  unfold freeGibbsDensity
  exact (weight edge b).continuous.div_const _

theorem freeGibbsDensity_nonneg (edge : E → V × V) (b : E → ℝ)
    (σ : Configuration V) : 0 ≤ freeGibbsDensity edge b σ :=
  div_nonneg (Real.exp_pos _).le (partition_pos edge b).le

theorem integral_freeGibbsDensity (edge : E → V × V) (b : E → ℝ) :
    ∫ σ, freeGibbsDensity edge b σ ∂referenceLaw = 1 := by
  unfold freeGibbsDensity
  rw [integral_div]
  change partition edge b / partition edge b = 1
  exact div_self (partition_pos edge b).ne'

/-- The actual free-boundary Gibbs measure. -/
@[expose] def freeGibbsMeasure (edge : E → V × V) (b : E → ℝ) : Measure (Configuration V) :=
  referenceLaw.withDensity (fun σ => ENNReal.ofReal (freeGibbsDensity edge b σ))

@[expose] instance freeGibbsMeasure_isProbability (edge : E → V × V) (b : E → ℝ) :
    IsProbabilityMeasure (freeGibbsMeasure edge b) := by
  constructor
  rw [freeGibbsMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((continuous_freeGibbsDensity edge b).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (Eventually.of_forall (freeGibbsDensity_nonneg edge b)), integral_freeGibbsDensity]
  norm_num

/-- The density construction agrees with the normalized expectations in the proof. -/
theorem integral_freeGibbsMeasure (edge : E → V × V) (b : E → ℝ)
    (f : Configuration V → ℝ) :
    ∫ σ, f σ ∂freeGibbsMeasure edge b =
      (∫ σ, f σ * weight edge b σ ∂referenceLaw) / partition edge b := by
  rw [freeGibbsMeasure, integral_withDensity_eq_integral_toReal_smul
    (f := fun σ => ENNReal.ofReal (freeGibbsDensity edge b σ))
    (ENNReal.measurable_ofReal.comp (continuous_freeGibbsDensity edge b).measurable)
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)), ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun σ => by
    change (ENNReal.ofReal (freeGibbsDensity edge b σ)).toReal * f σ =
      f σ * weight edge b σ / partition edge b
    rw [ENNReal.toReal_ofReal (freeGibbsDensity_nonneg edge b σ)]
    change weight edge b σ / partition edge b * f σ =
      f σ * weight edge b σ / partition edge b
    ring

/-- Bundle the free-boundary law as a probability measure with the weak topology. -/
@[expose] def freeGibbsProbability (edge : E → V × V) (b : E → ℝ) :
    ProbabilityMeasure (Configuration V) := ⟨freeGibbsMeasure edge b, inferInstance⟩

/-- The two-spin marginal is a pushforward of the actual finite-volume Gibbs law. -/
@[expose] def twoSpinMarginal (edge : E → V × V) (b : E → ℝ) (x y : V) :
    ProbabilityMeasure (Spin × Spin) :=
  (freeGibbsProbability edge b).map (fun σ => (σ x, σ y))

/-- Quadrupolar pair test function; compactness makes it bounded. -/
@[expose] def pairTest : (Spin × Spin) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun st => qPair st.1 st.2, by unfold qPair; fun_prop⟩

theorem integral_twoSpinMarginal (edge : E → V × V) (b : E → ℝ) (x y : V) :
    (∫ st, pairTest st ∂(twoSpinMarginal edge b x y : Measure (Spin × Spin))) =
      correlation edge b x y := by
  change (∫ st, pairTest st ∂Measure.map (fun σ : Configuration V => (σ x, σ y))
    (freeGibbsMeasure edge b)) = _
  rw [integral_map_of_stronglyMeasurable (by fun_prop) pairTest.continuous.stronglyMeasurable,
    integral_freeGibbsMeasure]
  rfl

end GibbsMeasure

/-- A probability law on the full infinite square-lattice spin configuration space. -/
abbrev InfiniteConfiguration := Fourier.Site → Spin

@[expose] def infinitePairMarginal (μ : ProbabilityMeasure InfiniteConfiguration) (x y : Fourier.Site) :
    ProbabilityMeasure (Spin × Spin) := μ.map (fun σ => (σ x, σ y))

@[expose] def infiniteCorrelation (μ : ProbabilityMeasure InfiniteConfiguration) (x y : Fourier.Site) : ℝ :=
  ∫ σ, qPair (σ x) (σ y) ∂(μ : Measure InfiniteConfiguration)

theorem integral_infinitePairMarginal (μ : ProbabilityMeasure InfiniteConfiguration)
    (x y : Fourier.Site) :
    (∫ st, pairTest st ∂(infinitePairMarginal μ x y : Measure (Spin × Spin))) =
      infiniteCorrelation μ x y := by
  change (∫ st, pairTest st ∂Measure.map (fun σ : InfiniteConfiguration => (σ x, σ y))
    (μ : Measure InfiniteConfiguration)) = _
  rw [integral_map_of_stronglyMeasurable (by fun_prop) pairTest.continuous.stronglyMeasurable]
  rfl

/-- Convergence of the actual two-spin marginals along one common finite-volume
sequence. A pair-dependent initial segment may be discarded before both sites
belong to the volume. This condition does not refer to an outside filling. -/
@[expose] def HasLocalPairLimit (G : ℕ → Fourier.LatticeGraph)
    (b : ∀ n, (G n).edges → ℝ) (μ : ProbabilityMeasure InfiniteConfiguration) : Prop :=
  ∀ x y : Fourier.Site, ∃ N : ℕ,
    ∃ (xn yn : ∀ n, (G (n + N)).vertices),
    (∀ n, (xn n).val = x) ∧ (∀ n, (yn n).val = y) ∧
    Tendsto (fun n => twoSpinMarginal (fun e : (G (n + N)).edges => e.val)
        (b (n + N)) (xn n) (yn n)) atTop (𝓝 (infinitePairMarginal μ x y))

/-- Local convergence along finite-volume ferromagnetic free-boundary laws.
Any subsequential local weak limit along an exhaustion satisfies this condition,
with the subsequence itself used as `G`. -/
@[expose] def IsFreeBoundaryLocalLimit (β : ℝ) (μ : ProbabilityMeasure InfiniteConfiguration) : Prop :=
  ∃ (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ),
    (∀ n e, 0 ≤ b n e ∧ b n e ≤ β) ∧ HasLocalPairLimit G b μ

/-- Local convergence along free-boundary laws with arbitrary signed couplings
uniformly bounded in absolute value. -/
@[expose] def IsSignedFreeBoundaryLocalLimit (β : ℝ)
    (μ : ProbabilityMeasure InfiniteConfiguration) : Prop :=
  ∃ (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ),
    (∀ n e, |b n e| ≤ β) ∧ HasLocalPairLimit G b μ

/-- The original ferromagnetic class embeds in the signed-coupling class. -/
theorem IsFreeBoundaryLocalLimit.signed {β : ℝ}
    {μ : ProbabilityMeasure InfiniteConfiguration} (hμ : IsFreeBoundaryLocalLimit β μ) :
    IsSignedFreeBoundaryLocalLimit β μ := by
  obtain ⟨G, b, hb, hlocal⟩ := hμ
  exact ⟨G, b, fun n e => by rw [abs_of_nonneg (hb n e).1]; exact (hb n e).2, hlocal⟩

/-- Embed a finite-volume configuration in the infinite product by a fixed
spin outside the volume. This convention is immaterial for local limits along
an exhaustion. -/
@[expose] def extendConfiguration (G : Fourier.LatticeGraph) (s₀ : Spin)
    (σ : Configuration G.vertices) : InfiniteConfiguration :=
  fun z => if hz : z ∈ G.vertices then σ ⟨z, hz⟩ else s₀

theorem continuous_extendConfiguration (G : Fourier.LatticeGraph) (s₀ : Spin) :
    Continuous (extendConfiguration G s₀) := by
  apply continuous_pi
  intro z
  by_cases hz : z ∈ G.vertices
  · simpa only [extendConfiguration, hz, dite_true] using
      (continuous_apply (⟨z, hz⟩ : G.vertices))
  · simpa only [extendConfiguration, hz, dite_false] using
      (continuous_const : Continuous (fun _ : Configuration G.vertices => s₀))

/-- Actual finite-volume Gibbs law, embedded as a probability measure on the
infinite spin space for the usual weak topology. -/
@[expose] def extendedFreeGibbs (G : Fourier.LatticeGraph) (b : G.edges → ℝ) (s₀ : Spin) :
    ProbabilityMeasure InfiniteConfiguration :=
  (freeGibbsProbability (fun e : G.edges => e.val) b).map (extendConfiguration G s₀)

theorem pairMarginal_extendedFreeGibbs (G : Fourier.LatticeGraph) (b : G.edges → ℝ)
    (s₀ : Spin) (x y : Fourier.Site) (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) :
    infinitePairMarginal (extendedFreeGibbs G b s₀) x y =
      twoSpinMarginal (fun e : G.edges => e.val) b ⟨x, hx⟩ ⟨y, hy⟩ := by
  apply Subtype.ext
  change Measure.map (fun σ : InfiniteConfiguration => (σ x, σ y))
      (Measure.map (extendConfiguration G s₀) (freeGibbsMeasure (fun e : G.edges => e.val) b)) =
    Measure.map (fun σ : Configuration G.vertices => (σ ⟨x, hx⟩, σ ⟨y, hy⟩))
      (freeGibbsMeasure (fun e : G.edges => e.val) b)
  rw [Measure.map_map (by fun_prop) (continuous_extendConfiguration G s₀).measurable]
  congr 1
  funext σ
  simp only [Function.comp_def, extendConfiguration, hx, hy, dite_true]

/-- A weak limit of the actual embedded free-boundary laws along an exhaustion
satisfies the two-spin local-limit hypothesis. This also applies to any
subsequence that exhausts the lattice. -/
theorem isFreeBoundaryLocalLimit_of_weak_limit (β : ℝ)
    (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ)
    (hb : ∀ n e, 0 ≤ b n e ∧ b n e ≤ β)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices)
    (s₀ : Spin) (μ : ProbabilityMeasure InfiniteConfiguration)
    (hμ : Tendsto (fun n => extendedFreeGibbs (G n) (b n) s₀) atTop (𝓝 μ)) :
    IsFreeBoundaryLocalLimit β μ := by
  refine ⟨G, b, hb, ?_⟩
  intro x y
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hexhaust x).and (hexhaust y))
  let xn : ∀ n, (G (n + N)).vertices := fun n => ⟨x, (hN (n + N) (by omega)).1⟩
  let yn : ∀ n, (G (n + N)).vertices := fun n => ⟨y, (hN (n + N) (by omega)).2⟩
  refine ⟨N, xn, yn, (fun _ => rfl), (fun _ => rfl), ?_⟩
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => extendedFreeGibbs (G n) (b n) s₀) μ hμ
    (show Continuous (fun σ : InfiniteConfiguration => (σ x, σ y)) by fun_prop)
  have ht := hm.comp (tendsto_add_atTop_nat N)
  convert ht using 1
  · funext n
    exact (pairMarginal_extendedFreeGibbs (G (n + N)) (b (n + N)) s₀ x y
      (hN (n + N) (by omega)).1 (hN (n + N) (by omega)).2).symm
  · rfl

/-- A two-spin weak limit preserves any common bound on quadrupolar expectation. -/
theorem pair_bound_of_weak_limit {ν : ℕ → ProbabilityMeasure (Spin × Spin)}
    {ν₀ : ProbabilityMeasure (Spin × Spin)} (hν : Tendsto ν atTop (𝓝 ν₀))
    {B : ℝ} (hB : ∀ n, |∫ st, pairTest st ∂(ν n : Measure (Spin × Spin))| ≤ B) :
    |∫ st, pairTest st ∂(ν₀ : Measure (Spin × Spin))| ≤ B := by
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν) pairTest
  exact le_of_tendsto' ht.abs hB


/-- Transfer any common spatial envelope to a local limit, including envelopes
that apply only to a specified range of site pairs. This lemma retains the exact
finite-volume bound; no enlargement of its constants is needed. -/
theorem HasLocalPairLimit.correlation_bound
    {G : ℕ → Fourier.LatticeGraph} {b : ∀ n, (G n).edges → ℝ}
    {μ : ProbabilityMeasure InfiniteConfiguration} (hlocal : HasLocalPairLimit G b μ)
    (P : Fourier.Site → Fourier.Site → Prop) (B : Fourier.Site → Fourier.Site → ℝ)
    (hbound : ∀ n (x y : (G n).vertices), P x.val y.val →
      |correlation (fun e : (G n).edges => e.val) (b n) x y| ≤ B x.val y.val)
    (x y : Fourier.Site) (hxy : P x y) : |infiniteCorrelation μ x y| ≤ B x y := by
  obtain ⟨N, xn, yn, hx, hy, hlim⟩ := hlocal x y
  rw [← integral_infinitePairMarginal]
  apply pair_bound_of_weak_limit hlim
  intro n
  rw [integral_twoSpinMarginal]
  have hxy' : P (xn n).val (yn n).val := by simpa only [hx n, hy n] using hxy
  simpa only [hx n, hy n] using hbound (n + N) (xn n) (yn n) hxy'

/-- Extend a finite-volume configuration using an arbitrary, site-dependent
configuration outside the volume. No regularity of the outside values is needed. -/
@[expose] def extendConfigurationWith (G : Fourier.LatticeGraph) (outside : InfiniteConfiguration)
    (σ : Configuration G.vertices) : InfiniteConfiguration :=
  fun z => if hz : z ∈ G.vertices then σ ⟨z, hz⟩ else outside z

theorem continuous_extendConfigurationWith (G : Fourier.LatticeGraph)
    (outside : InfiniteConfiguration) : Continuous (extendConfigurationWith G outside) := by
  apply continuous_pi
  intro z
  by_cases hz : z ∈ G.vertices
  · simpa only [extendConfigurationWith, hz, dite_true] using
      (continuous_apply (⟨z, hz⟩ : G.vertices))
  · simpa only [extendConfigurationWith, hz, dite_false] using
      (continuous_const : Continuous (fun _ : Configuration G.vertices => outside z))

/-- The embedded free-boundary Gibbs measure with an arbitrary outside filling. -/
@[expose] def extendedFreeGibbsWith (G : Fourier.LatticeGraph) (b : G.edges → ℝ)
    (outside : InfiniteConfiguration) : ProbabilityMeasure InfiniteConfiguration :=
  (freeGibbsProbability (fun e : G.edges => e.val) b).map (extendConfigurationWith G outside)

/-- Constant outside fillings recover the original embedding exactly. -/
theorem extendedFreeGibbsWith_const (G : Fourier.LatticeGraph) (b : G.edges → ℝ)
    (s₀ : Spin) : extendedFreeGibbsWith G b (fun _ => s₀) = extendedFreeGibbs G b s₀ := rfl

theorem pairMarginal_extendedFreeGibbsWith (G : Fourier.LatticeGraph)
    (b : G.edges → ℝ) (outside : InfiniteConfiguration) (x y : Fourier.Site)
    (hx : x ∈ G.vertices) (hy : y ∈ G.vertices) :
    infinitePairMarginal (extendedFreeGibbsWith G b outside) x y =
      twoSpinMarginal (fun e : G.edges => e.val) b ⟨x, hx⟩ ⟨y, hy⟩ := by
  apply Subtype.ext
  change Measure.map (fun σ : InfiniteConfiguration => (σ x, σ y))
      (Measure.map (extendConfigurationWith G outside)
        (freeGibbsMeasure (fun e : G.edges => e.val) b)) =
    Measure.map (fun σ : Configuration G.vertices => (σ ⟨x, hx⟩, σ ⟨y, hy⟩))
      (freeGibbsMeasure (fun e : G.edges => e.val) b)
  rw [Measure.map_map (by fun_prop)
    (continuous_extendConfigurationWith G outside).measurable]
  congr 1
  funext σ
  simp only [Function.comp_def, extendConfigurationWith, hx, hy, dite_true]

/-- Any two outside fillings, which may vary independently with volume and site,
have eventually identical two-spin marginals along an exhaustion. -/
theorem eventually_pairMarginal_extendedFreeGibbsWith_eq
    (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices)
    (outside₁ outside₂ : ℕ → InfiniteConfiguration) (x y : Fourier.Site) :
    (fun n => infinitePairMarginal (extendedFreeGibbsWith (G n) (b n) (outside₁ n)) x y)
      =ᶠ[atTop]
    (fun n => infinitePairMarginal (extendedFreeGibbsWith (G n) (b n) (outside₂ n)) x y) := by
  filter_upwards [hexhaust x, hexhaust y] with n hx hy
  rw [pairMarginal_extendedFreeGibbsWith _ _ _ _ _ hx hy,
    pairMarginal_extendedFreeGibbsWith _ _ _ _ _ hx hy]

/-- Convergence of the two-spin marginals is independent of every outside-filling
choice, even if the choices vary with volume and lattice site. -/
theorem tendsto_pairMarginal_extendedFreeGibbsWith_iff
    (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices)
    (outside₁ outside₂ : ℕ → InfiniteConfiguration) (x y : Fourier.Site)
    (ν : ProbabilityMeasure (Spin × Spin)) :
    Tendsto (fun n => infinitePairMarginal
      (extendedFreeGibbsWith (G n) (b n) (outside₁ n)) x y) atTop (𝓝 ν) ↔
    Tendsto (fun n => infinitePairMarginal
      (extendedFreeGibbsWith (G n) (b n) (outside₂ n)) x y) atTop (𝓝 ν) :=
  tendsto_congr' (eventually_pairMarginal_extendedFreeGibbsWith_eq
    G b hexhaust outside₁ outside₂ x y)

/-- A full-configuration weak limit under arbitrary volume- and site-dependent
outside fillings has the intrinsic local pair limits. -/
theorem hasLocalPairLimit_of_weak_limit_with
    (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices)
    (outside : ℕ → InfiniteConfiguration) (μ : ProbabilityMeasure InfiniteConfiguration)
    (hμ : Tendsto (fun n => extendedFreeGibbsWith (G n) (b n) (outside n)) atTop (𝓝 μ)) :
    HasLocalPairLimit G b μ := by
  intro x y
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hexhaust x).and (hexhaust y))
  let xn : ∀ n, (G (n + N)).vertices := fun n => ⟨x, (hN (n + N) (by omega)).1⟩
  let yn : ∀ n, (G (n + N)).vertices := fun n => ⟨y, (hN (n + N) (by omega)).2⟩
  refine ⟨N, xn, yn, (fun _ => rfl), (fun _ => rfl), ?_⟩
  have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => extendedFreeGibbsWith (G n) (b n) (outside n)) μ hμ
    (show Continuous (fun σ : InfiniteConfiguration => (σ x, σ y)) by fun_prop)
  have ht := hm.comp (tendsto_add_atTop_nat N)
  convert ht using 1
  · funext n
    exact (pairMarginal_extendedFreeGibbsWith (G (n + N)) (b (n + N))
      (outside (n + N)) x y (hN (n + N) (by omega)).1
      (hN (n + N) (by omega)).2).symm
  · rfl

/-- General weak-limit bridge for arbitrary bounded signed couplings and
arbitrary outside fillings. -/
theorem isSignedFreeBoundaryLocalLimit_of_weak_limit_with (β : ℝ)
    (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ)
    (hb : ∀ n e, |b n e| ≤ β)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices)
    (outside : ℕ → InfiniteConfiguration) (μ : ProbabilityMeasure InfiniteConfiguration)
    (hμ : Tendsto (fun n => extendedFreeGibbsWith (G n) (b n) (outside n)) atTop (𝓝 μ)) :
    IsSignedFreeBoundaryLocalLimit β μ :=
  ⟨G, b, hb, hasLocalPairLimit_of_weak_limit_with G b hexhaust outside μ hμ⟩

/-- General weak-limit bridge retaining the original ferromagnetic API. -/
theorem isFreeBoundaryLocalLimit_of_weak_limit_with (β : ℝ)
    (G : ℕ → Fourier.LatticeGraph) (b : ∀ n, (G n).edges → ℝ)
    (hb : ∀ n e, 0 ≤ b n e ∧ b n e ≤ β)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices)
    (outside : ℕ → InfiniteConfiguration) (μ : ProbabilityMeasure InfiniteConfiguration)
    (hμ : Tendsto (fun n => extendedFreeGibbsWith (G n) (b n) (outside n)) atTop (𝓝 μ)) :
    IsFreeBoundaryLocalLimit β μ :=
  ⟨G, b, hb, hasLocalPairLimit_of_weak_limit_with G b hexhaust outside μ hμ⟩

end
end RP3
