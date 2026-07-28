import Erdos390.WholePaper.CentralPromotionCostAsymptotic

/-!
# Expanded literal statement audit for (4.10)--(4.11)

The examples below expose the actual prime support, the exact ceiling
logarithm used for promotion, the Chebyshev majorant, and the final fixed
cutoff selected for an arbitrary positive tolerance.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (n X : ℕ) :
    centralPromotionMajorant n X =
      (Nat.primeCounting X : ℝ) +
        ((Nat.primeCounting X : ℝ) * Real.log (n : ℝ) -
          Chebyshev.theta (X : ℝ)) / Real.log 2 := rfl

example {n X : ℕ} (hX : X ≤ n) :
    ((∑ p ∈
        (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X),
        Nat.clog 2
          (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) : ℕ) : ℝ) ≤
      (Nat.primeCounting X : ℝ) +
        ((Nat.primeCounting X : ℝ) * Real.log (n : ℝ) -
          Chebyshev.theta (X : ℝ)) / Real.log 2 := by
  simpa only [residualPromotionCost, residualCentralPrimes,
    promotionExponent, centralPrimeBlock, centralPromotionMajorant] using
      residualPromotionCost_cast_le_centralPromotionMajorant hX

example :
    ∃ K : ℝ, 0 < K ∧
      ∀ q : ℕ, 2 ≤ q →
        ∀ᶠ n : ℕ in atTop,
          ((∑ p ∈
              (Nat.choose (2 * n) n).primeFactors.filter
                (fun p ↦ p ≤ n / q),
              Nat.clog 2
                (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) : ℕ) : ℝ) ≤
            (K * (1 + Real.log (q : ℝ)) / (q : ℝ)) *
              ((n : ℝ) / Real.log (n : ℝ)) := by
  simpa only [residualPromotionCost, residualCentralPrimes,
    promotionExponent, centralPrimeBlock, secondOrderScale] using
      residualPromotionCost_fixedCutoff_uniform_bound

example {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        ((∑ p ∈
            (Nat.choose (2 * n) n).primeFactors.filter
              (fun p ↦ p ≤ n / (R + 1)),
            Nat.clog 2
              (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) : ℕ) : ℝ) ≤
          epsilon * ((n : ℝ) / Real.log (n : ℝ)) := by
  simpa only [residualPromotionCost, residualCentralPrimes,
    promotionExponent, centralPrimeBlock, secondOrderScale] using
      residualPromotionCost_eventually_cast_le_mul hepsilon

example {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        (∑ p ∈
            (Nat.choose (2 * n) n).primeFactors.filter
              (fun p ↦ p ≤ n / (R + 1)),
            Nat.clog 2
              (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1)) ≤
          Nat.ceil (epsilon * ((n : ℝ) / Real.log (n : ℝ))) := by
  simpa only [residualPromotionCost, residualCentralPrimes,
    promotionExponent, centralPrimeBlock, secondOrderScale] using
      residualPromotionCost_eventually_le_ceil hepsilon

end

end Erdos390.WholePaper
