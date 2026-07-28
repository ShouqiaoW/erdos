import Erdos390.WholePaper.BankPaperSharpCensus

/-! # Expanded statement audit for the sharp actual-bank census -/

open Filter Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example (n : ℕ) :
    bankOrdinaryWeightedPathDemand n =
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * (bankOrdinaryCoreSources p).card := rfl

example (n : ℕ) :
    (bankOrdinaryPaperRequests n).card =
      2 * ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p * (bankOrdinaryCoreSources p).card := by
  simpa only [bankOrdinaryWeightedPathDemand] using
    card_bankOrdinaryPaperRequests_eq_weightedPathDemand n

example {a b : ℕ} (ha : 5 ≤ a) (hab : a ≤ b) :
    bankOrdinaryScaleIndex a ≤ bankOrdinaryScaleIndex b :=
  bankOrdinaryScaleIndex_mono_of_five_le ha hab

example {n p s : ℕ} (hp : p ∈ bankRoundingPrimeSupport n)
    (hs : s ∈ bankOrdinaryCoreSources p) :
    1 ≤ bankOrdinaryComponentScaleIndex s :=
  one_le_bankOrdinaryComponentScaleIndex_of_mem hp hs

example {n p s : ℕ} (hp : p ∈ bankRoundingPrimeSupport n)
    (hs : s ∈ bankOrdinaryCoreSources p)
    (hscale : 6 ≤ bankOrdinaryComponentScaleIndex s) :
    bankOrdinaryComponentScaleIndex s ≤
      bankOrdinaryScaleIndex (yNat n) :=
  bankOrdinaryComponentScaleIndex_le_yNatScaleIndex_of_six_le
    hp hs hscale

example {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) :
    bankOrdinaryCoreSources p ⊆
      (bankOrdinaryCoreSources p).filter
          (fun s ↦ bankOrdinaryComponentScaleIndex s ≤ 5) ∪
        (Finset.Icc 6 (bankOrdinaryScaleIndex (yNat n))).biUnion
          (bankOrdinaryCoreSourcesAtScale p) :=
  bankOrdinaryCoreSources_subset_smallLargePathFibers hp

example (n : ℕ) :
    bankOrdinaryPathComponentBudget n =
      17 + 2 * (bankOrdinaryScaleIndex (yNat n) - 5) := rfl

example {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) :
    (bankOrdinaryCoreSources p).card ≤
      17 + 2 * (bankOrdinaryScaleIndex (yNat n) - 5) :=
  bankOrdinaryCoreSources_card_le_pathComponentBudget hp

example (n : ℕ) :
    bankOrdinaryWeightedPathDemand n ≤
        bankBottomPaperDemand n * bankOrdinaryPathComponentBudget n ∧
      (bankOrdinaryPaperRequests n).card ≤
        2 * bankBottomPaperDemand n *
          bankOrdinaryPathComponentBudget n :=
  ⟨bankOrdinaryWeightedPathDemand_le n,
    card_bankOrdinaryPaperRequests_le_sharp n⟩

example (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) =
      (bankBottomRelevantPaperRequests n).card +
        2 * bankOrdinaryWeightedPathDemand n :=
  card_bankPaperMarkerRequest_eq_weightedPathLedger n

example (n : ℕ) :
    bankPaperSharpMarkerBudget n =
      bankBottomPaperDemand n *
        (42 + 4 * (bankOrdinaryScaleIndex (yNat n) - 5)) := by
  simp only [bankPaperSharpMarkerBudget,
    bankOrdinaryPathComponentBudget]
  ring

example (n : ℕ) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperSharpMarkerBudget n :=
  card_bankPaperMarkerRequest_le_sharpMarkerBudget n

example {n : ℕ} (hy : 6 ≤ yNat n) (hgeometry : 3 * yNat n ≤ n) :
    (bankOrdinaryScaleIndex (yNat n) : ℝ) ≤
      L n / Real.log (4 / 3 : ℝ) :=
  bankOrdinaryScaleIndex_yNat_le_log hy hgeometry

example :
    (fun n : ℕ ↦ (bankOrdinaryPathComponentBudget n : ℝ))
      =O[atTop] L :=
  bankOrdinaryPathComponentBudget_isBigO_L

example
    (hDemand :
      (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ))) :
    (fun n : ℕ ↦ (bankPaperSharpMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) * L n) :=
  bankPaperSharpMarkerBudget_isBigO_yNat_mul_L_of_demand hDemand

example :
    (fun n : ℕ ↦ (bankPaperSharpMarkerBudget n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ) * L n) :=
  bankPaperSharpMarkerBudget_isBigO_yNat_mul_L

example {n M : ℕ} (R : BankPaperRealization n M) :
    Fintype.card (BankPaperMarkerRequest n) ≤
      bankPaperSharpMarkerBudget n :=
  R.prechargeComponentCount_le_sharpMarkerBudget

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows.card ≤ bankPaperSharpMarkerBudget n :=
  R.tangentPaperBankRows_card_le_sharpMarkerBudget

example
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
      (residualCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        (largeCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        fixedExceptional.card + 3 * bankPaperSharpMarkerBudget n :=
  R.tangentPaperNumericalGuardSet_card_le_sharpMarkerBudget
    certificate fixedExceptional hnCutoff

example
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤ 2 + 2 * bankPaperSharpMarkerBudget n :=
  R.tangentPaperPairNumericalGuards_card_le_sharpMarkerBudget
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    ((tangentCommonMultiplierInterval n K h u v).filter
          (fun a ↦ u * a ∈
            R.tangentPaperNumericalGuardSet certificate fixedExceptional) ∪
        (tangentCommonMultiplierInterval n K h u v).filter
          (fun a ↦ v * a ∈
            R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card ≤
      4 + 4 * bankPaperSharpMarkerBudget n := by
  exact
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_sharp
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
        hyCutoff huPrime hvPrime

example
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (Finset.Ioc (n / v) ((2 * n - K * h) / u)).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentExceptionalMultipliers n X0 (yNat n)
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      4 + 4 * bankPaperSharpMarkerBudget n := by
  exact R.tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
    certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime

end

end Erdos390.WholePaper
