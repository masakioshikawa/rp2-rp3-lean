import RP3.Calculus

/-!
# Derivatives of a squared interaction

The recursive product jet differentiates both factors once at each step.
It supplies actual derivatives, including the extra second- and fourth-order
terms absent from a linear spin interaction.
-/
namespace RP3

open scoped BigOperators

noncomputable def productJet {Ω : Type*} (F G : ℕ → ℝ → Ω → ℝ) :
    ℕ → ℕ → ℕ → ℝ → Ω → ℝ
  | 0, a, b, t, ω => F a t ω * G b t ω
  | k+1, a, b, t, ω =>
      productJet F G k (a+1) b t ω + productJet F G k a (b+1) t ω

theorem continuous_productJet {Ω : Type*} [TopologicalSpace Ω]
    (F G : ℕ → ℝ → Ω → ℝ)
    (hF : ∀ k, Continuous (Function.uncurry (F k)))
    (hG : ∀ k, Continuous (Function.uncurry (G k))) (k a b : ℕ) :
    Continuous (Function.uncurry (productJet F G k a b)) := by
  induction k generalizing a b with
  | zero => exact (hF a).mul (hG b)
  | succ k ih => exact (ih (a+1) b).add (ih a (b+1))

theorem hasDerivAt_productJet {Ω : Type*} (F G : ℕ → ℝ → Ω → ℝ)
    (hF : ∀ k t ω, HasDerivAt (fun u => F k u ω) (F (k+1) t ω) t)
    (hG : ∀ k t ω, HasDerivAt (fun u => G k u ω) (G (k+1) t ω) t)
    (k a b : ℕ) (t : ℝ) (ω : Ω) :
    HasDerivAt (fun u => productJet F G k a b u ω)
      (productJet F G (k+1) a b t ω) t := by
  induction k generalizing a b with
  | zero => exact ((hF a t ω).mul (hG b t ω)).congr_deriv (by simp [productJet])
  | succ k ih => exact (ih (a+1) b).add (ih a (b+1))

theorem squareJet_one {Ω : Type*} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    productJet F F 1 0 0 t ω = 2 * F 0 t ω * F 1 t ω := by
  simp only [productJet]; ring

theorem squareJet_two {Ω : Type*} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    productJet F F 2 0 0 t ω = 2 * (F 1 t ω ^ 2 + F 0 t ω * F 2 t ω) := by
  simp only [productJet]; ring

theorem squareJet_three {Ω : Type*} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    productJet F F 3 0 0 t ω =
      2 * (3 * F 1 t ω * F 2 t ω + F 0 t ω * F 3 t ω) := by
  simp only [productJet]; ring

theorem squareJet_four {Ω : Type*} (F : ℕ → ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    productJet F F 4 0 0 t ω =
      2 * (3 * F 2 t ω ^ 2 + 4 * F 1 t ω * F 3 t ω + F 0 t ω * F 4 t ω) := by
  simp only [productJet]; ring

/-- If each factor jet has absolute value at most one, its product jet is
bounded by `2^k`. This includes mixed initial orders `a,b`. -/
theorem abs_productJet_le {Ω : Type*} (F G : ℕ → ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) (hF : ∀ k, |F k t ω| ≤ 1) (hG : ∀ k, |G k t ω| ≤ 1)
    (k a b : ℕ) : |productJet F G k a b t ω| ≤ (2 : ℝ)^k := by
  induction k generalizing a b with
  | zero =>
    simpa [productJet, abs_mul] using
      (mul_le_mul (hF a) (hG b) (abs_nonneg _) zero_le_one)
  | succ k ih =>
    calc
      |productJet F G (k+1) a b t ω| ≤
          |productJet F G k (a+1) b t ω| + |productJet F G k a (b+1) t ω| :=
        abs_add_le _ _
      _ ≤ 2^k + 2^k := add_le_add (ih (a+1) b) (ih a (b+1))
      _ = 2^(k+1) := by ring

end RP3
