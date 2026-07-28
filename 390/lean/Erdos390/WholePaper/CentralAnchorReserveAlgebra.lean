import Erdos390.WholePaper.CentralAnchorTailDivisibility
import Erdos390.WholePaper.Constants

/-!
# Finite slack algebra for the central-anchor tail reserve

This file isolates the exact comparison used after the prefix-allocation,
promotion-cost, and factorial-tail estimates have been proved.  The divisor
is the actual `centralAnchorDivisor`; its cofactor valuation is compared at a
fixed prime, and the additional promotion cost is inserted only at `2`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- With one-sixth asymptotic error on the cofactor and tail estimates and a
one-quarter promotion budget, the actual anchor-divisor valuation fits in
the actual upper tail. -/
theorem centralAnchorDivisor_factorization_le_upperTailValuation_of_slack
    {c epsilon scale : ℝ} {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale) (hℓPrime : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hcofactor :
      ((∑ p ∈ largeCentralPrimes n X,
          (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail :
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (upperTailValuation c n ℓ : ℝ)) :
    (centralAnchorDivisor n X q).factorization ℓ ≤
      upperTailValuation c n ℓ := by
  rw [centralAnchorDivisor_factorization hq]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    have hcofactor' :
        ((∑ p ∈ largeCentralPrimes n X,
            (q p).factorization 2 : ℕ) : ℝ) ≤
          (C0 + epsilon / 6) * scale := by
      simpa using hcofactor
    have htail' :
        (c - epsilon / 6) * scale ≤
          (upperTailValuation c n 2 : ℝ) := by
      simpa using htail
    have hcoefficient :
        C0 + epsilon / 6 + epsilon / 4 ≤ c - epsilon / 6 := by
      rw [hc]
      linarith
    have hreal :
        ((residualPromotionCost n X +
            ∑ p ∈ largeCentralPrimes n X,
              (q p).factorization 2 : ℕ) : ℝ) ≤
          (upperTailValuation c n 2 : ℝ) := by
      rw [Nat.cast_add]
      calc
        (residualPromotionCost n X : ℝ) +
              ((∑ p ∈ largeCentralPrimes n X,
                (q p).factorization 2 : ℕ) : ℝ) ≤
            epsilon / 4 * scale + (C0 + epsilon / 6) * scale :=
          add_le_add hpromotion hcofactor'
        _ = (C0 + epsilon / 6 + epsilon / 4) * scale := by ring
        _ ≤ (c - epsilon / 6) * scale :=
          mul_le_mul_of_nonneg_right hcoefficient hscale
        _ ≤ (upperTailValuation c n 2 : ℝ) := htail'
    exact_mod_cast hreal
  · have hpredPosNat : 0 < ℓ - 1 := Nat.sub_pos_of_lt hℓPrime.one_lt
    have hpredPos : 0 < ((ℓ - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredPosNat
    have hcoefficient :
        C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)) ≤
          c / ((ℓ - 1 : ℕ) : ℝ) -
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)) := by
      rw [hc]
      field_simp [hpredPos.ne']
      nlinarith
    have hreal :
        ((∑ p ∈ largeCentralPrimes n X,
            (q p).factorization ℓ : ℕ) : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ) :=
      hcofactor.trans <|
        (mul_le_mul_of_nonneg_right hcoefficient hscale).trans htail
    simp only [if_neg hℓTwo, zero_add]
    exact_mod_cast hreal

/-- The same slack calculation with the quantitative reserve retained.
The conclusion is written additively, so it remains meaningful before
turning the valuation comparison into natural-number divisibility. -/
theorem centralAnchorDivisor_factorization_add_reserve_le_upperTailValuation_of_slack
    {c epsilon scale : ℝ} {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale) (hℓPrime : ℓ.Prime)
    (hq : IsLargeCentralCofactorChoice n X q)
    (hcofactor :
      ((∑ p ∈ largeCentralPrimes n X,
          (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail :
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (upperTailValuation c n ℓ : ℝ)) :
    epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
        ((centralAnchorDivisor n X q).factorization ℓ : ℝ) ≤
      (upperTailValuation c n ℓ : ℝ) := by
  rw [centralAnchorDivisor_factorization hq]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    have hcofactor' :
        ((∑ p ∈ largeCentralPrimes n X,
            (q p).factorization 2 : ℕ) : ℝ) ≤
          (C0 + epsilon / 6) * scale := by
      simpa using hcofactor
    have htail' :
        (c - epsilon / 6) * scale ≤
          (upperTailValuation c n 2 : ℝ) := by
      simpa using htail
    have hcoefficient :
        epsilon / 3 + epsilon / 4 + (C0 + epsilon / 6) ≤
          c - epsilon / 6 := by
      rw [hc]
      linarith
    calc
      epsilon / (3 * (((2 - 1 : ℕ) : ℝ))) * scale +
          (((if (2 : ℕ) = 2 then residualPromotionCost n X else 0) +
            ∑ p ∈ largeCentralPrimes n X,
              (q p).factorization 2 : ℕ) : ℝ) =
        epsilon / 3 * scale +
          (residualPromotionCost n X : ℝ) +
            ((∑ p ∈ largeCentralPrimes n X,
              (q p).factorization 2 : ℕ) : ℝ) := by
          norm_num
          ring
      _ ≤ epsilon / 3 * scale + epsilon / 4 * scale +
          (C0 + epsilon / 6) * scale := by
        gcongr
      _ = (epsilon / 3 + epsilon / 4 +
          (C0 + epsilon / 6)) * scale := by ring
      _ ≤ (c - epsilon / 6) * scale :=
        mul_le_mul_of_nonneg_right hcoefficient hscale
      _ ≤ (upperTailValuation c n 2 : ℝ) := htail'
  · have hpredPosNat : 0 < ℓ - 1 := Nat.sub_pos_of_lt hℓPrime.one_lt
    have hpredPos : 0 < ((ℓ - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredPosNat
    have hcoefficient :
        epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) +
            (C0 / ((ℓ - 1 : ℕ) : ℝ) +
              epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) ≤
          c / ((ℓ - 1 : ℕ) : ℝ) -
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)) := by
      rw [hc]
      field_simp [hpredPos.ne']
      linarith
    have hcofactorActual :
        (((if ℓ = 2 then residualPromotionCost n X else 0) +
          ∑ p ∈ largeCentralPrimes n X,
            (q p).factorization ℓ : ℕ) : ℝ) ≤
          (C0 / ((ℓ - 1 : ℕ) : ℝ) +
              epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale := by
      simpa only [if_neg hℓTwo, zero_add] using hcofactor
    calc
      epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
          (((if ℓ = 2 then residualPromotionCost n X else 0) +
            ∑ p ∈ largeCentralPrimes n X,
              (q p).factorization ℓ : ℕ) : ℝ) ≤
        epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) * scale +
          (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale :=
        add_le_add le_rfl hcofactorActual
      _ = (epsilon / (3 * ((ℓ - 1 : ℕ) : ℝ)) +
          (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ)))) * scale := by ring
      _ ≤ (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale :=
        mul_le_mul_of_nonneg_right hcoefficient hscale
      _ ≤ (upperTailValuation c n ℓ : ℝ) := htail

/-- Simultaneous finite-support form, ending in literal natural-number
divisibility of the central-anchor divisor into the upper tail product. -/
theorem centralAnchorDivisor_dvd_upperTail_of_slack
    {c epsilon scale : ℝ} {n X B : ℕ} {q : ℕ → ℕ}
    (hc : c = C0 + epsilon) (hepsilon : 0 < epsilon)
    (hscale : 0 ≤ scale)
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hcofactor : ∀ ℓ ∈ primesUpTo (max 2 B),
      ((∑ p ∈ largeCentralPrimes n X,
          (q p).factorization ℓ : ℕ) : ℝ) ≤
        (C0 / ((ℓ - 1 : ℕ) : ℝ) +
            epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale)
    (hpromotion :
      (residualPromotionCost n X : ℝ) ≤ epsilon / 4 * scale)
    (htail : ∀ ℓ ∈ primesUpTo (max 2 B),
      (c / ((ℓ - 1 : ℕ) : ℝ) -
          epsilon / (6 * ((ℓ - 1 : ℕ) : ℝ))) * scale ≤
        (upperTailValuation c n ℓ : ℝ)) :
    centralAnchorDivisor n X q ∣
      centralTailProduct n (upperTailLength c n) := by
  apply centralAnchorDivisor_dvd_upperTail_of_support_bounds
    hqChoice hqBound
  intro ℓ hℓ
  exact centralAnchorDivisor_factorization_le_upperTailValuation_of_slack
    hc hepsilon hscale (mem_primesUpTo.mp hℓ).1 hqChoice
      (hcofactor ℓ hℓ) hpromotion (htail ℓ hℓ)

end

end Erdos390.WholePaper
