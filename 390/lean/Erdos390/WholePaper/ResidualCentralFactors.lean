import Erdos390.WholePaper.CentralPromotion

/-! # The finite family of promoted residual central factors -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Central-binomial prime divisors at or below the residual cutoff. -/
def residualCentralPrimes (n X : ℕ) : Finset ℕ :=
  (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ p ≤ X)

/-- The set of their promoted factors. -/
def residualPromotedFactors (n X : ℕ) : Finset ℕ :=
  (residualCentralPrimes n X).image (promotedCentralFactor n)

/-- Total extra power of two introduced by residual promotion. -/
def residualPromotionCost (n X : ℕ) : ℕ :=
  ∑ p ∈ residualCentralPrimes n X,
    promotionExponent n (centralPrimeBlock n p)

theorem residualCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem residualCentralPrimes_le {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) : p ≤ X :=
  (Finset.mem_filter.mp hp).2

theorem residualCentralPrimes_exponent_pos {n X p : ℕ}
    (hp : p ∈ residualCentralPrimes n X) :
    0 < (Nat.choose (2 * n) n).factorization p := by
  have hpMem : p ∈ (Nat.choose (2 * n) n).primeFactors :=
    (Finset.mem_filter.mp hp).1
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  exact (Nat.prime_of_mem_primeFactors hpMem).factorization_pos_of_dvd
    hchoosePos.ne' (Nat.dvd_of_mem_primeFactors hpMem)

theorem promotedCentralFactor_injOn_residualCentralPrimes (n X : ℕ) :
    Set.InjOn (promotedCentralFactor n) (residualCentralPrimes n X) := by
  intro p hp q hq hpq
  exact promotedCentralFactor_injective_on_positive_support
    (residualCentralPrimes_prime hp) (residualCentralPrimes_prime hq)
    (residualCentralPrimes_exponent_pos hp)
    (residualCentralPrimes_exponent_pos hq) hpq

theorem residualPromotedFactors_card (n X : ℕ) :
    (residualPromotedFactors n X).card = (residualCentralPrimes n X).card := by
  exact Finset.card_image_of_injOn
    (promotedCentralFactor_injOn_residualCentralPrimes n X)

theorem residualPromotedFactors_subset_centralInterval
    {n X : ℕ} (hn : 0 < n) :
    residualPromotedFactors n X ⊆ Finset.Ioc n (2 * n) := by
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
  exact promotedCentralFactor_mem_centralInterval hn

/-- Exact product identity for the promoted residual family. -/
theorem residualPromotedFactors_prod (n X : ℕ) :
    (residualPromotedFactors n X).prod id =
      2 ^ residualPromotionCost n X *
        (residualCentralPrimes n X).prod (centralPrimeBlock n) := by
  rw [residualPromotedFactors,
    Finset.prod_image
      (promotedCentralFactor_injOn_residualCentralPrimes n X)]
  simp only [id_eq, promotedCentralFactor, promotedBlock]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

end

end Erdos390.WholePaper
