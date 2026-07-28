import Erdos390.WholePaper.CentralAnchorModificationAlgebra

/-! # Expanded statement audit for finite central-cofactor modification -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {n X B ℓ : ℕ} {q q' : ℕ → ℕ} {changed : Finset ℕ}
    (hℓ : ℓ.Prime)
    (hq : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), IsRoutedCentralCofactor n p (q p))
    (hq' : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), IsRoutedCentralCofactor n p (q' p))
    (hchanged : changed ⊆ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P))
    (hsame : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), p ∉ changed → q' p = q p)
    (hq'Bound : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), q' p ≤ B) :
    (2 ^ residualPromotionCost n X *
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P)).prod q').factorization ℓ ≤
      (2 ^ residualPromotionCost n X *
        ((Nat.choose (2 * n) n).primeFactors.filter
          (fun P ↦ X < P)).prod q).factorization ℓ +
        changed.card * Nat.log 2 B := by
  simpa only [IsLargeCentralCofactorChoice, largeCentralPrimes,
    centralAnchorDivisor, largeCentralCofactorProduct] using
      centralAnchorDivisor_factorization_le_add_changed_cost hℓ hq hq'
        hchanged hsame hq'Bound

example {n X B ℓ : ℕ} {q q' : ℕ → ℕ} {changed : Finset ℕ}
    {reserve loss tail : ℝ}
    (hℓ : ℓ.Prime)
    (hq : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), IsRoutedCentralCofactor n p (q p))
    (hq' : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), IsRoutedCentralCofactor n p (q' p))
    (hchanged : changed ⊆ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P))
    (hsame : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), p ∉ changed → q' p = q p)
    (hq'Bound : ∀ p ∈ (Nat.choose (2 * n) n).primeFactors.filter
      (fun P ↦ X < P), q' p ≤ B)
    (hcost : ((changed.card * Nat.log 2 B : ℕ) : ℝ) ≤ loss)
    (hreserve : reserve +
        ((2 ^ residualPromotionCost n X *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q).factorization ℓ : ℝ) ≤ tail) :
    reserve - loss +
        ((2 ^ residualPromotionCost n X *
          ((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q').factorization ℓ : ℝ) ≤ tail := by
  simpa only [IsLargeCentralCofactorChoice, largeCentralPrimes,
    centralAnchorDivisor, largeCentralCofactorProduct] using
      centralAnchorReserve_transfer_after_changed_cost hℓ hq hq'
        hchanged hsame hq'Bound hcost hreserve

end

end Erdos390.WholePaper
