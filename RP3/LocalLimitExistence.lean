import RP3.LogSquareLimits

/-! Proofs contributed in the Claude Opus review supplied by the user on
11 October 2026, integrated and checked against this pinned development.
See REVIEW-RESPONSE.md for scope and attribution. -/
noncomputable section
open MeasureTheory Filter RP3
open scoped InnerProductSpace BigOperators Matrix Topology

namespace RP3

open Classical in
/-- The full box `[-n,n]²` with every positively oriented nearest-neighbour bond. -/
def exhaustionBox (n : ℕ) : Fourier.LatticeGraph where
  vertices := Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n
  edges := (Finset.univ : Finset (_ × _)).filter
    (fun e => Fourier.PositiveNeighbor e.1.val e.2.val)
  nearest := by
    intro e he
    exact (Finset.mem_filter.mp he).2

theorem box_exhausts (z : Fourier.Site) : ∀ᶠ n in atTop, z ∈ (exhaustionBox n).vertices := by
  refine eventually_atTop.mpr ⟨(max |z.1| |z.2|).toNat, fun n hn => ?_⟩
  have h1 : |z.1| ≤ n := by
    have := Int.self_le_toNat (max |z.1| |z.2|)
    have := le_max_left |z.1| |z.2|
    omega
  have h2 : |z.2| ≤ n := by
    have := Int.self_le_toNat (max |z.1| |z.2|)
    have := le_max_right |z.1| |z.2|
    omega
  simp only [exhaustionBox, Finset.mem_product, Finset.mem_Icc]
  constructor <;> constructor <;> [linarith [neg_abs_le z.1]; linarith [le_abs_self z.1];
    linarith [neg_abs_le z.2]; linarith [le_abs_self z.2]]

/-- Any exhausting sequence with admissible signed couplings has a local limit. -/
theorem exists_signed_local_limit_of_sequence (β : ℝ) (G : ℕ → Fourier.LatticeGraph)
    (b : ∀ n, (G n).edges → ℝ) (hb : ∀ n e, |b n e| ≤ β)
    (hexhaust : ∀ z : Fourier.Site, ∀ᶠ n in atTop, z ∈ (G n).vertices) (s₀ : Spin) :
    ∃ μ : ProbabilityMeasure InfiniteConfiguration, IsSignedFreeBoundaryLocalLimit β μ := by
  obtain ⟨μ, -, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := ProbabilityMeasure InfiniteConfiguration)).tendsto_subseq
      (x := fun n => extendedFreeGibbsWith (G n) (b n) (fun _ => s₀)) (fun _ => Set.mem_univ _)
  exact ⟨μ, isSignedFreeBoundaryLocalLimit_of_weak_limit_with β (fun n => G (φ n))
    (fun n => b (φ n)) (fun n e => hb (φ n) e)
    (fun z => hφ.tendsto_atTop.eventually (hexhaust z)) (fun _ _ => s₀) μ hlim⟩

/-- **Suggested witness.** The local-limit endpoint applies to an actual measure. -/
theorem local_limit_endpoint_nonvacuous_with_spin (β : ℝ) (hβ : 0 ≤ β) (s₀ : Spin) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∃ μ : ProbabilityMeasure InfiniteConfiguration, IsSignedFreeBoundaryLocalLimit β μ ∧
      ∀ x y : Fourier.Site, |infiniteCorrelation μ x y| ≤
        C * Real.exp (-c * (Real.log (2 + (Fourier.siteRadius x y : ℝ))) ^ 2) := by
  obtain ⟨C, hC, c, hc, h⟩ := log_square_quadrupolar_decay_local_limit_signed β hβ
  obtain ⟨μ, hμ⟩ := exists_signed_local_limit_of_sequence β exhaustionBox (fun _ _ => β)
    (fun _ _ => by rw [abs_of_nonneg hβ]) box_exhausts s₀
  exact ⟨C, hC, c, hc, μ, hμ, h μ hμ⟩


/-- A concrete unit director supplies the outside filling without an extra
inhabitedness hypothesis in the public existence theorems. -/
def identitySpin : Spin := by
  let v : E4 := WithLp.toLp 2 ![1, 0, 0, 0]
  have h : ‖v‖ ^ 2 = 1 := by
    norm_num [EuclideanSpace.real_norm_sq_eq, v, Fin.sum_univ_four]
  exact ⟨v, mem_sphere_zero_iff_norm.mpr (by nlinarith [norm_nonneg v])⟩

/-- The signed free-boundary local-limit class is nonempty for every β ≥ 0.
The witnessing finite models are full boxes with every coupling equal to β. -/
theorem exists_signed_free_boundary_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ μ : ProbabilityMeasure InfiniteConfiguration, IsSignedFreeBoundaryLocalLimit β μ :=
  exists_signed_local_limit_of_sequence β exhaustionBox (fun _ _ => β)
    (fun _ _ => by rw [abs_of_nonneg hβ]) box_exhausts identitySpin

/-- The ferromagnetic class also has a witness, obtained from full boxes
with coupling β on every nearest-neighbor bond. -/
theorem exists_free_boundary_local_limit (β : ℝ) (hβ : 0 ≤ β) :
    ∃ μ : ProbabilityMeasure InfiniteConfiguration, IsFreeBoundaryLocalLimit β μ := by
  obtain ⟨μ, -, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := ProbabilityMeasure InfiniteConfiguration)).tendsto_subseq
      (x := fun n => extendedFreeGibbsWith (exhaustionBox n) (fun _ => β)
        (fun _ => identitySpin)) (fun _ => Set.mem_univ _)
  exact ⟨μ, isFreeBoundaryLocalLimit_of_weak_limit_with β
    (fun n => exhaustionBox (φ n)) (fun _ _ => β) (fun _ _ => ⟨hβ, le_rfl⟩)
    (fun z => hφ.tendsto_atTop.eventually (box_exhausts z))
    (fun _ _ => identitySpin) μ hlim⟩

/-- The log-square local-limit endpoint has an actual probability-measure
witness, with no additional choice of a spin required from the caller. -/
theorem local_limit_endpoint_nonvacuous (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
      ∃ μ : ProbabilityMeasure InfiniteConfiguration, IsSignedFreeBoundaryLocalLimit β μ ∧
      ∀ x y : Fourier.Site, |infiniteCorrelation μ x y| ≤
        C * Real.exp (-c * (Real.log (2 + (Fourier.siteRadius x y : ℝ))) ^ 2) :=
  local_limit_endpoint_nonvacuous_with_spin β hβ identitySpin

end RP3

end
