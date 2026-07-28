import Erdos390.WholePaper.CentralAnchorProduct

/-! # Expanded statement audit for the exact full central-anchor product -/

open scoped BigOperators

namespace Erdos390.WholePaper

example {n X : ℕ} (hn : 0 < n) (hXsq : 2 * n < X ^ 2) :
    ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
      (n < p ∧ p ≤ 2 * n ∧ canonicalLargeCentralCofactor n p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
          r + 1 ≤ canonicalLargeCentralCofactor n p ∧
          canonicalLargeCentralCofactor n p ≤ 2 * r + 1 := by
  simpa only [IsLargeCentralCofactorChoice, IsRoutedCentralCofactor,
    largeCentralPrimes] using
      canonicalLargeCentralCofactor_isChoice hn hXsq

example {n X : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
      (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
          r + 1 ≤ q p ∧ q p ≤ 2 * r + 1) :
    ((residualCentralPrimes n X).image (promotedCentralFactor n) ∪
      ((Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P)).image
        (fun p ↦ p * q p)).prod id =
      Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n X *
          (((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q)) := by
  simpa only [fullCentralAnchors, residualPromotedFactors,
    largeCentralAnchors, largeCentralPrimes, largeCentralAnchor,
    centralAnchorDivisor, largeCentralCofactorProduct,
    IsLargeCentralCofactorChoice, IsRoutedCentralCofactor] using
      fullCentralAnchors_prod hn hXTwo hXsq hq

end Erdos390.WholePaper
