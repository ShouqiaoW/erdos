import Erdos390.WholePaper.CentralAnchorDivisorSupport

/-! # Expanded statement audit for the central-anchor divisor ledger -/

open scoped BigOperators

namespace Erdos390.WholePaper

example {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hq : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
      IsRoutedCentralCofactor n p (q p)) :
    (2 ^ residualPromotionCost n X *
        (((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P)).prod q)).factorization ℓ =
      (if ℓ = 2 then residualPromotionCost n X else 0) +
        ∑ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P), (q p).factorization ℓ := by
  simpa only [centralAnchorDivisor, largeCentralCofactorProduct,
    largeCentralPrimes, IsLargeCentralCofactorChoice] using
      centralAnchorDivisor_factorization hq

end Erdos390.WholePaper
