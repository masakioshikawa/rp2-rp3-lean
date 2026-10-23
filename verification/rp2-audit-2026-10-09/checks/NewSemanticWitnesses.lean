import RP2
namespace RP2.NewAudit
noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators

theorem expanded_log_square (β : ℝ) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
    (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |(∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (⟪(σ x).val, (σ y).val⟫_ℝ ^ 2 - 1 / 3) *
          Real.exp (∑ e : G.edges,
            b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere))) /
      (∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Real.exp (∑ e : G.edges,
          b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)))| ≤
        C * Real.exp (-c * (Real.log (2 + ((max |y.val.1-x.val.1| |y.val.2-x.val.2| : ℤ) : ℝ)))^2) := by
  obtain ⟨C, hC, c, hc, h⟩ := RP2.log_square_quadrupolar_decay_signed β hβ
  exact ⟨C, hC, c, hc, fun G b hb x y => h G b hb x y⟩

theorem expanded_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hhigh : β < Real.log ((3 : ℝ)/2)) :
    0 < -Real.log (max (1/2 : ℝ) (3*(1-Real.exp (-β)))) ∧
    ∀ (G : Fourier.LatticeGraph) (b : G.edges → ℝ),
    (∀ e, |b e| ≤ β) → ∀ (x y : G.vertices),
      |(∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        (⟪(σ x).val, (σ y).val⟫_ℝ ^ 2 - 1 / 3) *
          Real.exp (∑ e : G.edges,
            b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere))) /
      (∫ σ : G.vertices → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        Real.exp (∑ e : G.edges,
          b e * ⟪(σ e.val.1).val, (σ e.val.2).val⟫_ℝ ^ 2)
        ∂Measure.pi (fun _ : G.vertices =>
          (((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere Set.univ)⁻¹ •
            (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)))| ≤
        (8 : ℝ)/9 * Real.exp (Real.log (max (1/2 : ℝ) (3*(1-Real.exp (-β)))) *
          ((max |y.val.1-x.val.1| |y.val.2-x.val.2| : ℤ) : ℝ)) := by
  obtain ⟨hm, h⟩ := RP2.elementary_exponential_quadrupolar_decay_signed β hβ hhigh
  refine ⟨hm, ?_⟩
  intro G b hb x y
  have hbound := h G b hb x y
  simp only [HighTemperature.elementaryMass, HighTemperature.elementaryDecayBase, neg_neg] at hbound
  exact hbound

example : (0 : ℝ) < Real.log ((3 : ℝ)/2) := Real.log_pos (by norm_num)

end
end RP2.NewAudit
