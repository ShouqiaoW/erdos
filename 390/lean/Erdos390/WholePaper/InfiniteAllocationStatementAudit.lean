import Erdos390.WholePaper.InfiniteAllocation

/-! # Expanded statement audit for the infinite cofactor allocation -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example :
    ∃ x : ℕ → ℕ → ℚ,
      (∀ r q : ℕ, 0 ≤ x r q) ∧
      (∀ r : ℕ, 1 ≤ r → ∀ q : ℕ,
        q ∉ Finset.Icc (r + 1) (2 * r + 1) → x r q = 0) ∧
      (∀ r : ℕ, 1 ≤ r →
        (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), x r q) =
          1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))) ∧
      (∀ ℓ : ℕ, ℓ.Prime →
        (∑' r : ℕ,
          ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
            (q.factorization ℓ : ℚ) * x r q) ≤
          (4029639598 / 25970038185 : ℚ) /
            (((ℓ - 1 : ℕ) : ℚ))) := by
  simpa only [alpha, allocationPrimeLoad, allocationPrimeRowLoad,
    C0Rat_eq] using infinite_cofactor_allocation

end

end Erdos390.WholePaper
