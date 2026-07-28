import Erdos390.WholePaper.BankPaperPrechargeUniformCapacityAsymptotic

/-! # Statement audit for uniform precharge capacity -/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ,
      p.Prime → p ≤ yNat n →
        (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) ≤
          delta / (((p - 1 : ℕ) : ℝ)) * secondOrderScale n :=
  eventually_bankPaperPrecharge_perPrimeCapacity hdelta

example (n : ℕ) :
    bankPaperPrechargeCubicLogMajorant n =
      yNat n ^ 3 * Nat.log 2 (3 * n) :=
  rfl

example :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeCubicLogMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) :=
  bankPaperPrechargeCubicLogMajorant_normalized_tendsto_zero

example (n : ℕ) :
    bankPaperPrechargeUniformCapacityMajorant n =
      bankPaperPrechargeSmallPrimeCostMajorant n +
        2 * bankPaperPrechargeCubicLogMajorant n :=
  rfl

example :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeUniformCapacityMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) :=
  bankPaperPrechargeUniformCapacityMajorant_normalized_tendsto_zero

example (c : ℝ) (n : ℕ) :
    bankPaperPrechargeUniformCapacityCost c n =
      yNat n *
        (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
          Nat.log2 (upperTailLength c n) + 1) :=
  rfl

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      bankPaperPrechargeUniformCapacityCost c n ≤
        bankPaperPrechargeUniformCapacityMajorant n :=
  eventually_bankPaperPrechargeUniformCapacityCost_le_majorant hc

example {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeUniformCapacityCost c n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) :=
  bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero hc

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      yNat n *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
            Nat.log2 (upperTailLength c n) + 1) ≤
        upperTailLength c n :=
  eventually_bankPaperPrecharge_uniformMovingPrimeCapacity hc

end

end Erdos390.WholePaper
