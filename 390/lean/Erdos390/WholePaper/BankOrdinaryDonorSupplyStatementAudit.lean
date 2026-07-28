import Erdos390.WholePaper.BankOrdinaryDonorSupply

/-! # Expanded statement audit for ordinary-bank analytic supply -/

open Filter

namespace Erdos390.WholePaper

noncomputable section

example :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, 2 ≤ X₀ ∧
      ∀ A B : ℕ, X₀ ≤ A → A ≤ B →
        2 * C * ((B : ℝ) / Real.log (B : ℝ) ^ 3 +
          (A : ℝ) / Real.log (A : ℝ) ^ 3) ≤
            (B : ℝ) - (A : ℝ) →
        ((B : ℝ) - (A : ℝ)) / (2 * Real.log (B : ℝ)) ≤
          (bankPrimeInterval A B).card :=
  exists_primeInterval_card_lower_from_cumulativePNT

example :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (Erdos390.Full.ArithmeticModel.yNat n : ℚ) →
          delta * (Q : ℝ) ≤
            (bankOrdinarySmoothBulkDonors n Q).card :=
  exists_eventually_bankOrdinarySmoothBulkDonors_lower

example {c : ℝ} (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (Erdos390.Full.ArithmeticModel.yNat n : ℚ) →
          eta * secondOrderScale n / Real.log (n : ℝ) ≤
            (bankMarkerOccurrenceTotal
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) : ℝ) :=
  exists_eventually_bankOrdinary_occurrenceTotal_lower hc

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      20 < Q → Q ≤ (Erdos390.Full.ArithmeticModel.yNat n : ℚ) →
        bankMarkerOccurrenceTotal
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q) ⌈/⌉
            bankOrdinaryMultiplicityCap c n Q ≤
          bankEligibleMarkerCount
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n)) Q) :=
  eventually_bankOrdinary_occurrenceCeilDiv_le_markerCount hc

example {c : ℝ} (hc : 0 < c) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
        20 < Q → Q ≤ (Erdos390.Full.ArithmeticModel.yNat n : ℚ) →
          rho * secondOrderScale n /
              max (Q : ℝ) (Real.log (n : ℝ)) ≤
            (bankEligibleMarkerCount
              (bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n)) Q) : ℝ) :=
  exists_eventually_bankOrdinary_markerCount_lower hc

example {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ᶠ n : ℕ in atTop,
        eta * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankMarkerOccurrenceTotal
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n))
              (smallDescentScaleValue scale)) : ℝ) :=
  bankOrdinary_smallScale_occurrenceTotal_lower hc scale

example {c : ℝ} (hc : 0 < c) (scale : SmallDescentScale) :
    ∃ rho : ℝ, 0 < rho ∧
      ∀ᶠ n : ℕ in atTop,
        rho * secondOrderScale n / Real.log (n : ℝ) ≤
          (bankEligibleMarkerCount
            (bankOrdinaryEligibleRelation n
              (upperEndpoint n (upperTailLength c n))
              (smallDescentScaleValue scale)) : ℝ) :=
  bankOrdinary_smallScale_markerCount_lower hc scale

end

end Erdos390.WholePaper
