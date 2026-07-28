import Erdos390.WholePaper.UpperTailValuationAsymptotic

/-!
# Literal statement audit for the fixed-prime upper-tail valuation

The examples expose the actual factorial valuation difference, its finite
two-sided squeeze, paper (4.12), and the simultaneous integral reserve.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

example (c : ℝ) (n p : ℕ) :
    upperTailValuation c n p =
      (2 * n + Nat.ceil
          (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization p -
        (2 * n).factorial.factorization p := rfl

example {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : Nat.ceil
      (c * ((n : ℝ) / Real.log (n : ℝ))) ≤ n) :
    (Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))) : ℝ) /
          ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) ≤
        ((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization p -
            (2 * n).factorial.factorization p : ℕ) ∧
      (((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization p -
            (2 * n).factorial.factorization p : ℕ) : ℝ) ≤
        (Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))) : ℝ) /
          ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) := by
  simpa only [upperTailValuation, upperEndpoint, upperTailLength,
    secondOrderScale] using upperTailValuation_cast_bounds hp htail

example {c : ℝ} (hc : 0 < c) {p : ℕ} (hp : p.Prime) :
    Tendsto
      (fun n : ℕ ↦
        (((2 * n + Nat.ceil
                (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization p -
              (2 * n).factorial.factorization p : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
  simpa only [upperTailValuation, upperEndpoint, upperTailLength,
    secondOrderScale] using
      upperTailValuation_normalized_tendsto hc hp

example {c : ℝ} (hc : 0 < c) (primes : Finset ℕ)
    (reserve : ℕ → ℝ) (hprime : ∀ p ∈ primes, p.Prime)
    (hreserve : ∀ p ∈ primes,
      reserve p < c / ((p - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      Nat.ceil
          (reserve p * ((n : ℝ) / Real.log (n : ℝ))) ≤
        (2 * n + Nat.ceil
            (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization p -
          (2 * n).factorial.factorization p := by
  simpa only [upperTailValuation, upperEndpoint, upperTailLength,
    secondOrderScale] using
      eventually_natCeil_reserve_le_upperTailValuation_on_finset
        hc primes reserve hprime hreserve

example {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε < c)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      0 < Nat.ceil
          (((c - ε) / ((p - 1 : ℕ) : ℝ)) *
            ((n : ℝ) / Real.log (n : ℝ))) ∧
        Nat.ceil
            (((c - ε) / ((p - 1 : ℕ) : ℝ)) *
              ((n : ℝ) / Real.log (n : ℝ))) ≤
          (2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ)))).factorial.factorization p -
            (2 * n).factorial.factorization p := by
  simpa only [upperTailValuation, upperEndpoint, upperTailLength,
    secondOrderScale] using
      eventually_positive_natCeil_sub_slack_reserve_le_on_finset
        hc hε hεc primes hprime

end

end Erdos390.WholePaper
