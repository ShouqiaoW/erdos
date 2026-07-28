import Erdos390.WholePaper.ResidualCentralFactors

/-! # Expanded statement audit for the residual promoted-factor family -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {n X p : ℕ}
    (hp : p ∈ (Nat.choose (2 * n) n).primeFactors.filter (fun q ↦ q ≤ X)) :
    p.Prime ∧ p ≤ X ∧
      0 < (Nat.choose (2 * n) n).factorization p := by
  exact ⟨residualCentralPrimes_prime hp,
    residualCentralPrimes_le hp, residualCentralPrimes_exponent_pos hp⟩

example (n X : ℕ) :
    (((Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)).image
          (fun p ↦
            2 ^ Nat.clog 2
                (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) *
              p ^ (Nat.choose (2 * n) n).factorization p)).card =
      ((Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)).card := by
  exact residualPromotedFactors_card n X

example {n X : ℕ} (hn : 0 < n) :
    ((Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)).image
        (fun p ↦
          2 ^ Nat.clog 2
              (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) *
            p ^ (Nat.choose (2 * n) n).factorization p) ⊆
      Finset.Ioc n (2 * n) := by
  exact residualPromotedFactors_subset_centralInterval hn

example (n X : ℕ) :
    (((Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)).image
        (fun p ↦
          2 ^ Nat.clog 2
              (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) *
            p ^ (Nat.choose (2 * n) n).factorization p)).prod id =
      2 ^ (∑ p ∈ (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X),
          Nat.clog 2
            (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1)) *
        ∏ p ∈ (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X),
          p ^ (Nat.choose (2 * n) n).factorization p := by
  exact residualPromotedFactors_prod n X

end

end Erdos390.WholePaper
