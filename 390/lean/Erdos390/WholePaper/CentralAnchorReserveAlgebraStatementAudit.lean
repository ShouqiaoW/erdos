import Erdos390.WholePaper.CentralAnchorReserveAlgebra

/-! # Expanded statement audit for finite central-anchor reserve algebra -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {c epsilon scale : ℝ} {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale) (hℓPrime : ℓ.Prime)
    (hq : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        IsRoutedCentralCofactor n p (q p))
    (hcofactor :
      ((∑ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P), (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail :
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization ℓ -
            (2 * n).factorial.factorization ℓ : ℕ) : ℝ)) :
    (2 ^ residualPromotionCost n X *
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P)).prod q).factorization ℓ ≤
      (2 * n + Nat.ceil
          (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization ℓ -
        (2 * n).factorial.factorization ℓ := by
  simpa only [IsLargeCentralCofactorChoice, largeCentralPrimes,
    centralAnchorDivisor, largeCentralCofactorProduct, upperTailValuation,
    upperEndpoint, upperTailLength, secondOrderScale] using
      centralAnchorDivisor_factorization_le_upperTailValuation_of_slack
        hc hepsilon hscale hℓPrime hq hcofactor hpromotion htail

example {c epsilon scale : ℝ} {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale) (hℓPrime : ℓ.Prime)
    (hq : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        IsRoutedCentralCofactor n p (q p))
    (hcofactor :
      ((∑ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P), (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail :
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization ℓ -
            (2 * n).factorial.factorization ℓ : ℕ) : ℝ)) :
    epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
        ((2 ^ residualPromotionCost n X *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q).factorization ℓ : ℝ) ≤
      (((2 * n + Nat.ceil
            (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization ℓ -
          (2 * n).factorial.factorization ℓ : ℕ) : ℝ) := by
  simpa only [IsLargeCentralCofactorChoice, largeCentralPrimes,
    centralAnchorDivisor, largeCentralCofactorProduct, upperTailValuation,
    upperEndpoint, upperTailLength, secondOrderScale] using
      centralAnchorDivisor_factorization_add_reserve_le_upperTailValuation_of_slack
        hc hepsilon hscale hℓPrime hq hcofactor hpromotion htail

example {c epsilon scale : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale)
    (hqChoice : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        IsRoutedCentralCofactor n p (q p))
    (hqBound : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
        q p ≤ B)
    (hcofactor : ∀ ℓ ∈ (Finset.range (max 2 B + 1)).filter Nat.Prime,
      ((∑ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P), (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail : ∀ ℓ ∈ (Finset.range (max 2 B + 1)).filter Nat.Prime,
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization ℓ -
            (2 * n).factorial.factorization ℓ : ℕ) : ℝ)) :
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
      centralAnchorDivisor_dvd_upperTail_of_slack hc hepsilon hscale
        hqChoice hqBound hcofactor hpromotion htail

end

end Erdos390.WholePaper
