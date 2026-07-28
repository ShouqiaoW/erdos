import Erdos390.WholePaper.CentralAnchorCutoff

/-! # Expanded literal statement audit for the fixed central-anchor cutoff -/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (R n : ℕ) : centralAnchorCutoff R n = n / (R + 1) := rfl

example (R : ℕ) : centralAnchorCutoffThreshold R = 4 * (R + 1) ^ 2 := rfl

example {R n : ℕ} (hn : 4 * (R + 1) ^ 2 ≤ n) :
    2 * R + 1 < n / (R + 1) ∧
      2 * n < (n / (R + 1)) ^ 2 := by
  simpa only [centralAnchorCutoff, centralAnchorCutoffThreshold] using
    centralAnchorCutoff_scaleSeparation hn

example (R : ℕ) :
    ∀ᶠ n in atTop,
      2 * R + 1 < n / (R + 1) ∧
        2 * n < (n / (R + 1)) ^ 2 := by
  simpa only [centralAnchorCutoff] using
    eventually_centralAnchorCutoff_scaleSeparation R

example {R n p : ℕ} (hp : n / (R + 1) < p) : n / p ≤ R := by
  simpa only [centralAnchorCutoff] using
    div_le_fixedPrefix_of_centralAnchorCutoff_lt hp

example {R n p : ℕ} (hn : 4 * (R + 1) ^ 2 ≤ n)
    (hp : p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P)) :
    (Nat.choose (2 * n) n).factorization p = 1 ∧
      ((n < p ∧ p ≤ 2 * n) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ r = n / p ∧
          p.Prime ∧ n < p * (r + 1) ∧
            p * (2 * r + 1) ≤ 2 * n) := by
  simpa only [centralAnchorCutoff, centralAnchorCutoffThreshold,
    largeCentralPrimes, mem_stationaryPrimeLayer] using
      largeCentralPrime_rowZero_or_fixedPrefix hn hp

example {R n : ℕ} {q : ℕ → ℕ}
    (hq : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P),
      (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
            r + 1 ≤ q p ∧ q p ≤ 2 * r + 1)
    {p : ℕ} (hp : p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P)) :
    q p ≤ 2 * R + 1 := by
  simpa only [centralAnchorCutoff, largeCentralPrimes,
    IsLargeCentralCofactorChoice, IsRoutedCentralCofactor] using
      largeCentralCofactor_le_fixedPrefix hq hp

example {R n : ℕ} {q : ℕ → ℕ}
    (hq : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P),
      (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
            r + 1 ≤ q p ∧ q p ≤ 2 * r + 1)
    {p : ℕ} (hp : p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P)) :
    (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ R ∧ r = n / p ∧
        p ∈ stationaryPrimeLayer n r ∧
          r + 1 ≤ q p ∧ q p ≤ 2 * r + 1 := by
  simpa only [centralAnchorCutoff, largeCentralPrimes,
    IsLargeCentralCofactorChoice, IsRoutedCentralCofactor] using
      largeCentralCofactor_eq_one_or_fixedPrefix hq hp

example {R n p p' q q' : ℕ}
    (hn : 4 * (R + 1) ^ 2 ≤ n)
    (hp : p.Prime) (hp' : p'.Prime)
    (hpLarge : n / (R + 1) < p)
    (hq'Pos : 0 < q') (hq'Upper : q' ≤ 2 * R + 1)
    (heq : p * q = p' * q') : p = p' ∧ q = q' := by
  exact prime_mul_cofactor_eq_of_centralAnchorCutoff
    hn hp hp' hpLarge hq'Pos hq'Upper heq

example {R n : ℕ} {q : ℕ → ℕ}
    (hn : 4 * (R + 1) ^ 2 ≤ n)
    (hq : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P),
      (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
            r + 1 ≤ q p ∧ q p ≤ 2 * r + 1) :
    Set.InjOn (fun p ↦ p * q p)
      ((Nat.choose (2 * n) n).primeFactors.filter
        (fun P ↦ n / (R + 1) < P)) := by
  simpa only [centralAnchorCutoff, centralAnchorCutoffThreshold,
    largeCentralAnchor, largeCentralPrimes,
    IsLargeCentralCofactorChoice, IsRoutedCentralCofactor] using
      largeCentralAnchor_injOn_centralAnchorCutoff hn hq

example {R n : ℕ} {q : ℕ → ℕ}
    (hn : 4 * (R + 1) ^ 2 ≤ n)
    (hq : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ n / (R + 1) < P),
      (n < p ∧ p ≤ 2 * n ∧ q p = 1) ∨
        ∃ r : ℕ, 1 ≤ r ∧ r = n / p ∧
          p ∈ stationaryPrimeLayer n r ∧
            r + 1 ≤ q p ∧ q p ≤ 2 * r + 1) :
    ((residualCentralPrimes n (n / (R + 1))).image
          (promotedCentralFactor n) ∪
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ n / (R + 1) < P)).image
            (fun p ↦ p * q p)).prod id =
      Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (n / (R + 1)) *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ n / (R + 1) < P)).prod q) := by
  simpa only [centralAnchorCutoff, centralAnchorCutoffThreshold,
    fullCentralAnchors, residualPromotedFactors, largeCentralAnchors,
    largeCentralPrimes, largeCentralAnchor, centralAnchorDivisor,
    largeCentralCofactorProduct, IsLargeCentralCofactorChoice,
    IsRoutedCentralCofactor] using
      fullCentralAnchors_prod_centralAnchorCutoff hn hq

example {R n : ℕ} (hn : 4 * (R + 1) ^ 2 ≤ n) :
    ((residualCentralPrimes n (n / (R + 1))).image
          (promotedCentralFactor n) ∪
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ n / (R + 1) < P)).image
            (fun p ↦ p * canonicalLargeCentralCofactor n p)).prod id =
      Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (n / (R + 1)) *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ n / (R + 1) < P)).prod
              (canonicalLargeCentralCofactor n)) := by
  simpa only [centralAnchorCutoff, centralAnchorCutoffThreshold,
    fullCentralAnchors, residualPromotedFactors, largeCentralAnchors,
    largeCentralPrimes, largeCentralAnchor, centralAnchorDivisor,
    largeCentralCofactorProduct] using
      fullCentralAnchors_prod_canonical_centralAnchorCutoff hn

end

end Erdos390.WholePaper
