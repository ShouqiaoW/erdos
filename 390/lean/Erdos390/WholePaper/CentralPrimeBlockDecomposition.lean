import Erdos390.WholePaper.ResidualCentralFactors

/-!
# Exact low/high decomposition of the central binomial coefficient

The central binomial coefficient is the product of its complete prime-power
blocks.  Splitting those blocks at the anchor cutoff and promoting every low
block therefore introduces exactly one aggregate power of two and no other
valuation error.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Central-binomial prime divisors strictly above the residual cutoff. -/
def largeCentralPrimes (n X : ℕ) : Finset ℕ :=
  (Nat.choose (2 * n) n).primeFactors.filter (fun p ↦ X < p)

theorem largeCentralPrimes_prime {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : p.Prime := by
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

theorem largeCentralPrimes_gt {n X p : ℕ}
    (hp : p ∈ largeCentralPrimes n X) : X < p :=
  (Finset.mem_filter.mp hp).2

theorem residualCentralPrimes_disjoint_largeCentralPrimes (n X : ℕ) :
    Disjoint (residualCentralPrimes n X) (largeCentralPrimes n X) := by
  rw [Finset.disjoint_left]
  intro p hpLow hpHigh
  exact (not_lt_of_ge (residualCentralPrimes_le hpLow))
    (largeCentralPrimes_gt hpHigh)

theorem residualCentralPrimes_union_largeCentralPrimes (n X : ℕ) :
    residualCentralPrimes n X ∪ largeCentralPrimes n X =
      (Nat.choose (2 * n) n).primeFactors := by
  ext p
  simp only [residualCentralPrimes, largeCentralPrimes,
    Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  · intro hp
    by_cases hle : p ≤ X
    · exact Or.inl ⟨hp, hle⟩
    · exact Or.inr ⟨hp, by omega⟩

/-- The product of all complete central prime-power blocks is exactly the
central binomial coefficient. -/
theorem centralPrimeBlocks_prod_all (n : ℕ) :
    ((Nat.choose (2 * n) n).primeFactors).prod (centralPrimeBlock n) =
      Nat.choose (2 * n) n := by
  have hchoose : Nat.choose (2 * n) n ≠ 0 :=
    (Nat.choose_pos (by omega)).ne'
  simpa only [centralPrimeBlock, Nat.support_factorization] using
    Nat.factorization_prod_pow_eq_self hchoose

/-- Exact multiplicative split at an arbitrary cutoff. -/
theorem residual_mul_largeCentralPrimeBlocks (n X : ℕ) :
    (residualCentralPrimes n X).prod (centralPrimeBlock n) *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      Nat.choose (2 * n) n := by
  rw [← Finset.prod_union
    (residualCentralPrimes_disjoint_largeCentralPrimes n X),
    residualCentralPrimes_union_largeCentralPrimes,
    centralPrimeBlocks_prod_all]

/-- Promoting all low blocks changes the complete central product by exactly
`2^K` and leaves the high blocks untouched. -/
theorem residualPromoted_mul_largeCentralPrimeBlocks (n X : ℕ) :
    (residualPromotedFactors n X).prod id *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      2 ^ residualPromotionCost n X * Nat.choose (2 * n) n := by
  rw [residualPromotedFactors_prod]
  calc
    (2 ^ residualPromotionCost n X *
          (residualCentralPrimes n X).prod (centralPrimeBlock n)) *
        (largeCentralPrimes n X).prod (centralPrimeBlock n) =
      2 ^ residualPromotionCost n X *
        ((residualCentralPrimes n X).prod (centralPrimeBlock n) *
          (largeCentralPrimes n X).prod (centralPrimeBlock n)) := by
        ac_rfl
    _ = 2 ^ residualPromotionCost n X * Nat.choose (2 * n) n := by
      rw [residual_mul_largeCentralPrimeBlocks]

end

end Erdos390.WholePaper
