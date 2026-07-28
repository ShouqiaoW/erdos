import Erdos390.WholePaper.BankBottomConcreteDemand

/-! # Expanded statement audit for the concrete bottom-bank demand chain -/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example (n : ℕ) :
    bankRoundingPrimeSupport n = (yNat n + 1).primesBelow := rfl

example (n p : ℕ) :
    bankRoundingBeta n p =
      4 * Nat.clog 2 (3 * n) * Nat.clog p (3 * n) := rfl

example (n : ℕ) :
    bankRoundingDepth n = ⌈Real.logb 2 (3 * n)⌉₊ :=
  bankRoundingDepth_eq_paperCeil n

example (n p : ℕ) :
    bankRoundingBeta n p =
      4 * ⌈Real.logb 2 (3 * n)⌉₊ * ⌈Real.logb p (3 * n)⌉₊ :=
  bankRoundingBeta_eq_paperCeil n p

example {n M p : ℕ} (hM : M ≤ 3 * n) :
    4 * Nat.log 2 M * Nat.log p M ≤
      4 * Nat.clog 2 (3 * n) * Nat.clog p (3 * n) := by
  simpa only [bankRoundingBeta, bankRoundingDepth] using
    roundingErrorBox_le_bankRoundingBeta (n := n) (p := p) hM

example (n : ℕ) (pool : BankBottomOrientationPool) :
    bankBottomPoolDemand (bankBottomPaperRequests n)
        (bankBottomPaperRequestPool n) pool =
      ∑ p ∈ (yNat n + 1).primesBelow,
        4 * Nat.clog 2 (3 * n) * Nat.clog p (3 * n) := by
  simpa only [bankBottomPaperDemand, bankRoundingPrimeSupport,
    bankRoundingBeta, bankRoundingDepth] using
      bankBottomPaperPoolDemand_eq n pool

example (n : ℕ) :
    bankBottomPaperDemand n ≤
      4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) +
        20 * bankRoundingDepth n * Nat.primeCounting (yNat n) := by
  simpa only [bankBottomPaperDemandMajorant] using
    bankBottomPaperDemand_le_majorant n

example :
    (fun n : ℕ ↦
      ((∑ p ∈ (yNat n + 1).primesBelow,
        4 * Nat.clog 2 (3 * n) * Nat.clog p (3 * n) : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ)) := by
  simpa only [bankBottomPaperDemand, bankRoundingPrimeSupport,
    bankRoundingBeta, bankRoundingDepth] using
      bankBottomPaperDemand_isBigO_yNat

example : Tendsto
    (fun n : ℕ ↦
      ((∑ p ∈ (yNat n + 1).primesBelow,
          4 * Nat.clog 2 (3 * n) * Nat.clog p (3 * n) : ℕ) : ℝ) /
        (((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ)))
    atTop (nhds 0) := by
  simpa only [bankBottomPaperDemand, bankRoundingPrimeSupport,
    bankRoundingBeta, bankRoundingDepth, bankBottomPrimeScale,
    SafePrimeCounting.shortIntervalPrimeScale, secondOrderScale] using
      bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ pool : BankBottomOrientationPool,
      bankBottomPoolDemand (bankBottomPaperRequests n)
          (bankBottomPaperRequestPool n) pool ≤
        (bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) pool).card := by
  simpa only [bankBottomPoolCapacity] using
    eventually_bankBottomPaper_all_poolDemands_le_capacity hc

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankBottomPoolMatching
          (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
          (fun pool ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool),
        Function.Injective matching.matchedSlot ∧
          ∀ request : ↑(bankBottomPaperRequests n),
            matching.matchedSlot request ∈
              bankBottomOrientedMarkerPrimes n
                (upperEndpoint n (upperTailLength c n))
                (bankBottomPaperRequestPool n request.1) :=
  eventually_exists_bankBottomPaper_injective_assignment hc

end

end Erdos390.WholePaper
