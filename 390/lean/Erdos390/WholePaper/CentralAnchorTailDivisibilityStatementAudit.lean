import Erdos390.WholePaper.CentralAnchorTailDivisibility

/-! # Expanded statement audit for central-anchor tail divisibility -/

namespace Erdos390.WholePaper

noncomputable section

example (n h p : ℕ) :
    ((Finset.Ioc (2 * n) (2 * n + h)).prod id).factorization p =
      (2 * n + h).factorial.factorization p -
        (2 * n).factorial.factorization p := by
  simpa only [centralTailProduct, factorInterval] using
    centralTailProduct_factorization n h p

example {n X B h : ℕ} {q : ℕ → ℕ}
    (hqChoice : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        IsRoutedCentralCofactor n p (q p))
    (hqBound : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        q p ≤ B)
    (hvaluation : ∀ ℓ ∈
      (Finset.range (max 2 B + 1)).filter Nat.Prime,
      (2 ^ residualPromotionCost n X *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q).factorization ℓ ≤
        ((Finset.Ioc (2 * n) (2 * n + h)).prod id).factorization ℓ) :
    2 ^ residualPromotionCost n X *
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P)).prod q ∣
      (Finset.Ioc (2 * n) (2 * n + h)).prod id := by
  simpa only [IsLargeCentralCofactorChoice, largeCentralPrimes,
    centralAnchorDivisor, largeCentralCofactorProduct, centralTailProduct,
    factorInterval, primesUpTo] using
      centralAnchorDivisor_dvd_centralTailProduct_of_support_bounds
        hqChoice hqBound hvaluation

example {c : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hqChoice : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        IsRoutedCentralCofactor n p (q p))
    (hqBound : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        q p ≤ B)
    (hvaluation : ∀ ℓ ∈
      (Finset.range (max 2 B + 1)).filter Nat.Prime,
      (2 ^ residualPromotionCost n X *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q).factorization ℓ ≤
        (2 * n + Nat.ceil
            (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization ℓ -
          (2 * n).factorial.factorization ℓ) :
    2 ^ residualPromotionCost n X *
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P)).prod q ∣
      (Finset.Ioc (2 * n)
        (2 * n + Nat.ceil
          (c * ((n : ℝ) / Real.log (n : ℝ))))).prod id := by
  simpa only [IsLargeCentralCofactorChoice, largeCentralPrimes,
    centralAnchorDivisor, largeCentralCofactorProduct, centralTailProduct,
    factorInterval, primesUpTo, upperTailValuation, upperEndpoint,
    upperTailLength, secondOrderScale] using
      centralAnchorDivisor_dvd_upperTail_of_support_bounds
        hqChoice hqBound hvaluation

end

end Erdos390.WholePaper
