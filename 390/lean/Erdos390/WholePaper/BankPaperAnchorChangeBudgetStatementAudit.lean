import Erdos390.WholePaper.BankPaperAnchorChangeBudget

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

example :
    (fun n : ℕ ↦
      (((bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n : ℕ) : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) := by
  simpa only [bankPaperAnchorMarkerBudget] using
    bankPaperAnchorMarkerBudget_isBigO_yNat_sq

example :
    (fun n : ℕ ↦
      (((bankOrdinaryPaperRequests n).card +
        8 * bankBottomPaperDemand n : ℕ) : ℝ)) =o[atTop]
      secondOrderScale := by
  simpa only [bankPaperAnchorMarkerBudget] using
    bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale

example (depth : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        (((bankOrdinaryPaperRequests n).card +
            8 * bankBottomPaperDemand n) *
              Nat.log 2 (2 * depth + 1) : ℕ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  simpa only [bankPaperAnchorMarkerBudget, Nat.cast_mul] using
    bankPaperAnchorChangeCost_normalized_tendsto_zero depth

example (depth : ℕ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (R : BankPaperRealization n M),
      (((R.allMarkers ∩
          largeCentralPrimes n (n / (depth + 1))).card *
            Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
        delta * secondOrderScale n := by
  simpa only [BankPaperRealization.centralChangedMarkers,
    centralAnchorCutoff] using
      eventually_bankPaper_centralChangedMarkers_changeCost_le
        depth hdelta

example {c : ℝ} (hc : C0 < c) {depth : ℕ} (hdepth : 1 ≤ depth) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ) (R : BankPaperRealization n M),
      ∀ ℓ ∈ primesUpTo (2 * depth + 1),
        (((R.allMarkers ∩ largeCentralPrimes n (n / (depth + 1))).card *
            Nat.log 2 (2 * depth + 1) : ℕ) : ℝ) ≤
          (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
  simpa only [BankPaperRealization.centralChangedMarkers,
    centralAnchorCutoff] using
      eventually_bankPaper_changeCost_le_sixth_reserve hc hdepth

end Erdos390.WholePaper
