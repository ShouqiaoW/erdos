import Erdos390.WholePaper.ValuationError

open scoped BigOperators

namespace Erdos390.WholePaper

example {M a : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    (columnsContaining (Finset.univ : Finset ↥(primePowerColumns M))
      (primePowerInc M) a).card ≤ Nat.log 2 M :=
  primePowerColumns_degree_le_log ha haM

example {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (value : A → ℕ) (M : ℕ) (x : A → ℝ)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ)) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ q : ↥(primePowerColumns M),
        |∑ a, (X a - x a) *
          zeroOneColumn
            (fun q' a' ↦ primePowerInc M q' (value a')) q a| ≤
          (4 * Nat.log 2 M : ℝ) :=
  floating_rounding_primePowerColumns
    row value M x hvaluePos hvalueLe hx hrowInt

example {A : Type*} [Fintype A]
    (value : A → ℕ) (M d : ℕ) (X x : A → ℝ)
    (hM : 0 < M)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hcolumn : ∀ q : ↥(primePowerColumns M),
      |∑ a, (X a - x a) *
        zeroOneColumn
          (fun q' a' ↦ primePowerInc M q' (value a')) q a| ≤
        (4 * d : ℝ))
    {p : ℕ} (hp : p.Prime) :
    |∑ a, (X a - x a) * (value a).factorization p| ≤
      (4 * d * Nat.log p M : ℝ) := by
  simpa only [roundingValuationError] using
    roundingValuationError_le value M d X x hM hvaluePos hvalueLe hcolumn hp

example {A R : Type*} [Fintype A] [Fintype R]
    (row : A → R) (value : A → ℕ) (M : ℕ) (x : A → ℝ)
    (hM : 0 < M)
    (hvaluePos : ∀ a, 0 < value a)
    (hvalueLe : ∀ a, value a ≤ M)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ)) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ p, p.Prime →
        |∑ a, (X a - x a) * (value a).factorization p| ≤
          (4 * Nat.log 2 M * Nat.log p M : ℝ) := by
  simpa only [roundingValuationError] using
    floating_rounding_valuationErrorBox
      row value M x hM hvaluePos hvalueLe hx hrowInt

end Erdos390.WholePaper
