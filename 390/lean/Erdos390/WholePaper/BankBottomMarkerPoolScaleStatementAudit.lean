import Erdos390.WholePaper.BankBottomMarkerPoolScale

/-! # Expanded statement audit for the available bottom-pool scale facts -/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

example (n : ℕ) :
    bankBottomPrimeScale n =
      ((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ) := rfl

example {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    0 < c / (2 * (bankBottomMarkerDenominator pool.1 : ℝ)) := by
  simpa only [bankBottomOrientedPrimeConstant] using
    bankBottomOrientedPrimeConstant_pos hc pool

example {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        (((bankBottomOrientedMarkerInterval n
          (2 * n + Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))))
          pool).filter Nat.Prime).card : ℝ) /
            (((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ)))
      atTop
        (nhds (c / (2 * (bankBottomMarkerDenominator pool.1 : ℝ)))) := by
  simpa only [bankBottomOrientedMarkerPrimes, bankBottomPrimeScale,
    SafePrimeCounting.shortIntervalPrimeScale, upperEndpoint,
    upperTailLength, secondOrderScale, bankBottomOrientedPrimeConstant] using
      bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
        hc pool

example {c : ℝ} (hc : 0 < c)
    (orientation : BankBottomOrientation) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n))
          (.fiveToFour, orientation)).card : ℝ) /
            bankBottomPrimeScale n)
      atTop (nhds (c / 12)) := by
  simpa [bankBottomOrientedPrimeConstant,
    bankBottomMarkerDenominator] using
      bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
        hc (.fiveToFour, orientation)

example {c : ℝ} (hc : 0 < c)
    (orientation : BankBottomOrientation) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n))
          (.fourToThree, orientation)).card : ℝ) /
            bankBottomPrimeScale n)
      atTop (nhds (c / 10)) := by
  simpa [bankBottomOrientedPrimeConstant,
    bankBottomMarkerDenominator] using
      bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
        hc (.fourToThree, orientation)

example {c : ℝ} (hc : 0 < c)
    (orientation : BankBottomOrientation) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n))
          (.threeToTwo, orientation)).card : ℝ) /
            bankBottomPrimeScale n)
      atTop (nhds (c / 6)) := by
  simpa [bankBottomOrientedPrimeConstant,
    bankBottomMarkerDenominator] using
      bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
        hc (.threeToTwo, orientation)

example {c : ℝ} (hc : 0 < c)
    (orientation : BankBottomOrientation) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n))
          (.twoToOne, orientation)).card : ℝ) /
            bankBottomPrimeScale n)
      atTop (nhds (c / 8)) := by
  simpa [bankBottomOrientedPrimeConstant,
    bankBottomMarkerDenominator] using
      bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
        hc (.twoToOne, orientation)

example {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Ioc (bankBottomMarkerLower n move)
            (bankBottomMarkerUpper
              (2 * n + Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))))
              move)).filter Nat.Prime).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  simpa only [bankBottomMarkerPrimes, bankBottomMarkerInterval,
    upperEndpoint, upperTailLength, secondOrderScale] using
      bankBottomMarkerPrimes_card_div_secondOrderScale_tendsto_zero hc move

example {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (2 * n + Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))))
          pool).card : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
    bankBottomOrientedMarkerPrimes_card_div_secondOrderScale_tendsto_zero
      hc pool

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      5 * (2 * n + Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))) ≤
        12 * n := by
  simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
    eventually_bankBottom_scaledEndpoint_narrow hc

end

end Erdos390.WholePaper
