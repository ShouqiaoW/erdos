import Erdos390.WholePaper.BankPaperPrechargeAsymptotic

/-! # Expanded statement audit for the precharge asymptotic layer -/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example (n : ℕ) :
    bankPaperPrechargeCubicNormalizedCost n =
      y n ^ 3 * L n / secondOrderScale n :=
  rfl

example {n : ℕ} (hn : 1 < n) :
    bankPaperPrechargeCubicNormalizedCost n =
      L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) :=
  bankPaperPrechargeCubicNormalizedCost_eq hn

example :
    Tendsto bankPaperPrechargeCubicNormalizedCost atTop (nhds 0) :=
  bankPaperPrechargeCubicNormalizedCost_tendsto_zero

example :
    (fun n : ℕ ↦ y n ^ 3 * L n) =o[atTop] secondOrderScale :=
  y_cubed_mul_L_isLittleO_secondOrderScale

example :
    (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop] y :=
  bankPaperPrecharge_yNat_isBigO_y

example :
    (fun n : ℕ ↦ (Nat.log 2 (3 * n) : ℝ)) =O[atTop] L :=
  natLog_two_three_mul_isBigO_L

example :
    (fun n : ℕ ↦
      (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ))
      =o[atTop] secondOrderScale :=
  yNat_cubed_mul_natLog_isLittleO_secondOrderScale

example :
    (fun n : ℕ ↦
      (yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
        (Nat.log 2 (3 * n) : ℝ)) =o[atTop] secondOrderScale :=
  bankPaperPrechargeSmallPrimeCost_isLittleO_secondOrderScale

example :
    Tendsto
      (fun n : ℕ ↦
        ((yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
          (Nat.log 2 (3 * n) : ℝ)) / secondOrderScale n)
      atTop (nhds 0) :=
  bankPaperPrechargeSmallPrimeCost_normalized_tendsto_zero

example :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeSmallPrimeCostMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) :=
  bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero

example (n : ℕ) :
    bankPaperPrechargeSmallPrimeCostMajorant n =
      yNat n * bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) :=
  rfl

example (cost : ℕ → ℕ)
    (hcost : ∀ᶠ n : ℕ in atTop,
      cost n ≤ bankPaperPrechargeSmallPrimeCostMajorant n) :
    Tendsto
      (fun n : ℕ ↦ (cost n : ℝ) / secondOrderScale n)
      atTop (nhds 0) :=
  normalized_tendsto_zero_of_eventually_le_prechargeSmallPrimeCost
    cost hcost

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeSmallPrimeValuationCost ≤
      yNat n *
        (bankPaperAnchorMarkerBudget n * Nat.log 2 M) :=
  R.prechargeSmallPrimeValuationCost_le

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeSmallPrimeValuationCost =
      ∑ p ∈ primesUpTo (yNat n),
        (R.prechargeBaseStateProduct).factorization p :=
  rfl

example {n M : ℕ} (R : BankPaperRealization n M)
    (hM : M ≤ 3 * n) :
    R.prechargeSmallPrimeValuationCost ≤
      bankPaperPrechargeSmallPrimeCostMajorant n :=
  R.prechargeSmallPrimeValuationCost_le_majorant hM

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (hh : h ≤ n) :
    R.prechargeSmallPrimeValuationCost ≤
      bankPaperPrechargeSmallPrimeCostMajorant n :=
  R.prechargeSmallPrimeValuationCost_le_majorant_at_upperEndpoint hh

end

end Erdos390.WholePaper
