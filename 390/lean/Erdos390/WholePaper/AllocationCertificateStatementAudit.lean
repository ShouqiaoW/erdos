import Erdos390.WholePaper.AllocationCertificate

/-! # Literal statement audit for the finite allocation certificate -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example :
    ((finiteAllocationEntries.map AllocationEntry.coordinate).toFinset).card =
        211 ∧
    (∀ r q,
      (r, q) ∈
          (finiteAllocationEntries.map AllocationEntry.coordinate).toFinset →
        0 < finiteAllocation r q ∧
          1 ≤ r ∧ r ≤ 200 ∧ r + 1 ≤ q ∧ q ≤ 2 * r + 1) ∧
    (∀ r q,
      (r, q) ∉
          (finiteAllocationEntries.map AllocationEntry.coordinate).toFinset →
        finiteAllocation r q = 0) ∧
    (∀ r, 1 ≤ r → r ≤ 200 →
      (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          finiteAllocation r q) =
        1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))) ∧
    (∀ ℓ, ℓ.Prime → ℓ ≤ 401 →
      finitePrimeLoad ℓ ≤
        (4029639598 / 25970038185 : ℚ) /
          (((ℓ - 1 : ℕ) : ℚ))) ∧
    (∀ p, p.Prime → 201 < p → p ≤ 401 →
      finitePrimeLoad p +
          (∑ r ∈ Finset.Icc (max 201 (previousPrime p)) (p - 1),
            1 / (((r : ℚ) + 1) * (2 * (r : ℚ) + 1))) ≤
        (4029639598 / 25970038185 : ℚ) /
          (((p - 1 : ℕ) : ℚ))) := by
  simpa only [finiteAllocationSupport, alpha, C0Rat_eq] using
    finite_allocation_certificate

end

end Erdos390.WholePaper
