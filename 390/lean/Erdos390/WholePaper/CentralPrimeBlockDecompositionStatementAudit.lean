import Erdos390.WholePaper.CentralPrimeBlockDecomposition

/-! # Expanded statement audit for the exact central block split -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (n : ℕ) :
    ((Nat.choose (2 * n) n).primeFactors).prod
        (fun p ↦ p ^ (Nat.choose (2 * n) n).factorization p) =
      Nat.choose (2 * n) n := by
  simpa only [centralPrimeBlock] using centralPrimeBlocks_prod_all n

example (n X : ℕ) :
    (((Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)).image
        (fun p ↦
          2 ^ promotionExponent n
              (p ^ (Nat.choose (2 * n) n).factorization p) *
            p ^ (Nat.choose (2 * n) n).factorization p)).prod id *
      ((Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ X < p)).prod
        (fun p ↦ p ^ (Nat.choose (2 * n) n).factorization p) =
      2 ^ (∑ p ∈
          (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X),
            promotionExponent n
              (p ^ (Nat.choose (2 * n) n).factorization p)) *
        Nat.choose (2 * n) n := by
  simpa only [residualPromotedFactors, promotedCentralFactor,
    promotedBlock, centralPrimeBlock, residualPromotionCost,
    residualCentralPrimes, largeCentralPrimes] using
    residualPromoted_mul_largeCentralPrimeBlocks n X

end

end Erdos390.WholePaper
