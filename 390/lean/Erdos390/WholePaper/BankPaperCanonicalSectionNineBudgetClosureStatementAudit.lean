import Erdos390.WholePaper.BankPaperCanonicalSectionNineBudgetClosure

/-!
# Statement audit for the canonical Section 9 budget closure

The complete public declaration census is followed by exact restatements of
the logarithmic cancellation, the actual-`q` scale reduction, and the
eventual closure theorem.  The package definition itself is intentionally
kept transparent so its three clean-list fields and five quantitative
fields remain visible to downstream audits.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Complete public declaration census -/

#check exists_bankPaperCanonicalSectionNineBudgetCoreSynchronization
#check bankPaperCanonical_bridgeL_mul_secondOrderScale_eq
#check bankPaperCanonical_actualP87Scale_le_secondOrderScale_of_q_upper
#check BankPaperCanonicalSectionNineBudgetClosure
#check eventually_bankPaperCanonicalSectionNineBudgetClosure

example {c : Real} (hc : C0 < c) :
    ∃ depth W : Nat, ∃ r0 : Real,
      2 <= W ∧
      2 * depth + 1 <= W ∧
      1 < r0 ∧
      r0 < 3 / 2 ∧
      ∀ᶠ n : Nat in atTop,
        yNat n < centralAnchorCutoff depth n :=
  exists_bankPaperCanonicalSectionNineBudgetCoreSynchronization hc

/-! ## Exact finite reductions -/

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {n : Nat}
    (hBn : B.sampleData.n = n) :
    B.L * secondOrderScale n = (n : Real) :=
  bankPaperCanonical_bridgeL_mul_secondOrderScale_eq B hBn

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {n : Nat}
    {Cpost Cq tangentConstant : Real}
    (hBn : B.sampleData.n = n)
    (hCpost : 0 <= Cpost)
    (hqUpper : B.q <= Cq * secondOrderScale n)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq <= tangentConstant) :
    Cpost * B.q / B.L <=
      tangentConstant * secondOrderScale n / Real.log (y n) :=
  bankPaperCanonical_actualP87Scale_le_secondOrderScale_of_q_upper
    B hBn hCpost hqUpper hcoefficient

/-! ## Expanded transparent package -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : BridgeData Head (BankPaperCanonicalExponentBand M))
    {c : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma : Real)
    (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W)
    (r0 rho tangentConstant Cpost : Real)
    (endpoint : Nat -> Real) :
    BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M B R certificate deltaStar sigma hdelta hn hW S
        r0 rho tangentConstant Cpost endpoint ↔
      B.sampleData.n = n ∧
      B.sampleData.W = W ∧
      let density := tangentPaperCleanListDensity W r0
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1)
          hdelta hn hW S rho endpoint
      (∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request) ∧
      (∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request <=
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges flow)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            B.L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              flow edge.1 edge.2)
            n (K0 + 1) (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet certificate
              (R.paperFixedExceptionalFactors deltaStar)) request).card) ∧
      (∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
        ∀ side,
          density * n <=
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := density) request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request) ∧
      tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant (delta + M.ratio) sigma <= density ^ 2 / 48 ∧
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorCoefficient
            M n W rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <= density ^ 2 / 96 ∧
      tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)) <= density ^ 2 / 96 ∧
      Cpost * B.q / B.L <=
          tangentConstant * secondOrderScale n / Real.log (y n) ∧
      B.L * secondOrderScale n = (n : Real) :=
  Iff.rfl

/-! ## Exact eventual interface -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : Nat -> BridgeData Head (BankPaperCanonicalExponentBand M))
    (W K0 depth : Nat)
    {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
    (hdelta : 0 < delta)
    (hc : 0 < c)
    (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hcleanMainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0)
    (hWtwo : 2 <= W) (hprefix : 2 * depth + 1 <= W)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hwidth :
      delta + M.ratio <=
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant)
    (hCpost : 0 <= Cpost)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq <= tangentConstant)
    (hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W)
    (hqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q <= Cq * secondOrderScale n) :
    ∀ᶠ n : Nat in atTop,
      ∀ (hn : 1 < n) (hW : W ≠ 0)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (S : ScaleSeparation M n W)
        (endpoint : Nat -> Real),
      BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M (B n) R certificate deltaStar sigma
        hdelta hn hW S r0 rho tangentConstant Cpost endpoint :=
  eventually_bankPaperCanonicalSectionNineBudgetClosure
    M B W K0 depth hdelta hc hr0one hr0three
    hdeltaStar hdeltaUpper hcleanMainSmall hWtwo hprefix
    hrho hratio htangent hsigma hwidth hCpost hcoefficient
    hsync hqUpper

end

end Erdos390.WholePaper
