import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenFinalGeometryConnector
import Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineTerminal
import Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometryTrafficConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineBudgetClosure
import Erdos390.WholePaper.BankPaperCanonicalSectionNineFixedComponentCollision

/-!
# Public Section 9 event step for the frozen-top Post-Hfit source

The older synchronized event step was private and its input hard-coded the
legacy no-top Post-Hfit package.  This connector exposes the same finite
terminal event shape for the verified nearest-integer frozen-top source.

At one index the only source-specific input is
`BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage`.  The event
step combines it with the already existing budget, moment-readiness,
fixed-component collision, and rough-depth hypotheses, then calls
`bankPaperCanonicalSectionNineFinalPayload_of_topFrozenRoundedPostHfit`.

An eventual wrapper reuses the repository's automatic suppliers for those
four source-independent inputs and packages the result directly as
`BankPaperCanonicalDistributedSectionNineTerminalAtDepth`.  No new
family-level Post-Hfit supplier is postulated here.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Frozen-top synchronized input -/

/-- One finite capacity witness augmented by a frozen-top rounded Post-Hfit
package for the same bank, certificate, and canonical mesh partition.

This proposition contains no Section 9 budget closure, collision conclusion,
clean multiplier construction, final geometry, or final payload. -/
def BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∃ R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)),
    ∃ certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
        R.anchorGuardLeftCore R.anchorGuardRightCore
        (R.centralChangedMarkers depth),
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
          centralTailProduct B.sampleData.n
            (upperTailLength c B.sampleData.n) ∧
        (baseBankFactors R.exactificationState).prod id ∣
          certificate.prechargedTailTarget ∧
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
          certificate.prechargedTailTarget ∧
        certificate.prechargedTailTarget *
              centralAnchorDivisor B.sampleData.n
                (centralAnchorCutoff depth B.sampleData.n)
                certificate.q =
            centralTailProduct B.sampleData.n
              (upperTailLength c B.sampleData.n) ∧
        ∃ hW : B.sampleData.W ≠ 0,
          ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
            B.partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hW S ∧
              ∃ Tsource : BarycentricTarget B.sampleData,
                ∃ betaProt alpha beta qTilde : Real,
                  ∃ placementSeed activeSeed :
                      B.sampleData.Sample → Real,
                    ∃ radius : NNReal,
                      ∃ quota : Int,
                        ∃ path : Real → B.ParamSpace,
                          ∃ endpoint : Nat → Real,
                            BankPaperRealization.BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
                              (K := K0 + 1) B R certificate
                              (R.paperFixedExceptionalFactors deltaStar)
                              Tsource deltaStar betaProt alpha beta
                              qTilde sigma placementSeed activeSeed
                              radius Cpost
                              (bankPaperCanonicalRatioCellIndex
                                M hdelta B.n_gt_one hW S rho)
                              quota path endpoint

/-- Eventual form of the synchronized frozen-top input.  The bridge family
is fixed before the asymptotic index. -/
def BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
      M (B n) c depth K0 deltaStar rho sigma Cpost hdelta

/-! ## Public one-index assembly -/

set_option maxHeartbeats 2000000 in
theorem bankPaperCanonicalSectionNineTopFrozenFinalPayload_eventStep
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c r0 deltaStar sigma rho tangentConstant Cpost : Real}
    {depth K0 n W : Nat}
    (hdelta : 0 < delta)
    (hBn : B.sampleData.n = n) (hBW : B.sampleData.W = W)
    (hWtwo : 2 ≤ W)
    (hr0three : r0 < 3 / 2)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho)
    (Hinput :
      BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
        M B c depth K0 deltaStar rho sigma Cpost hdelta)
    (Hbudget :
      ∀ (hn : 1 < n) (hW : W ≠ 0)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (S : ScaleSeparation M n W)
        (endpoint : Nat → Real),
        BankPaperCanonicalSectionNineBudgetClosure
          (K0 := K0) M B R certificate deltaStar sigma
          hdelta hn hW S r0 rho tangentConstant Cpost endpoint)
    (Hmoment :
      ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        (∀ k : Fin M.cellCount,
          (2 : Real) ≤ scalePoint n (M.lower k)) ∧
        ∀ S : ScaleSeparation M n W,
          RegularMeshPrimeCutoffs.Mesh.MomentReady M
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta hn hWne S))
    (Hcollision :
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (deltaStar : Real),
        R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
          deltaStar)
    (hKh : (K0 + 1) * upperTailLength c n ≤ n) :
    ∃ R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n)),
      ∃ certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth),
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
                centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q =
              centralTailProduct n (upperTailLength c n) ∧
          ∃ W' K : Nat,
            ∃ selector : Nat → Real,
              ∃ flow : BankPaperCanonicalTangentPrime n W' →
                  BankPaperCanonicalTangentPrime n W' → Real,
                ∃ L sigma' : Real,
                  R.BankPaperCanonicalSectionNineFinalPayload (K := K)
                    certificate deltaStar selector flow L sigma' := by
  subst n
  subst W
  obtain ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd,
    htargetTail, hWne, S, hpartition, Tsource, betaProt, alpha,
    beta, qTilde, placementSeed, activeSeed, radius, quota, path,
    endpoint, Hpost⟩ := Hinput
  obtain ⟨hWmoment, hn, hTwo, HmomentReady⟩ := Hmoment
  have Hbudget' :
      BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M B R certificate deltaStar sigma
          hdelta hn hWmoment S r0 rho tangentConstant Cpost endpoint :=
    Hbudget hn hWmoment R certificate S endpoint
  unfold BankPaperCanonicalSectionNineBudgetClosure at Hbudget'
  obtain ⟨_hBnBudget, _hBWBudget, hlowerPos, hlower, hlowerScale,
    hmain, herror, hceiling, hscaleDom, hscale⟩ := Hbudget'
  have hdensity :
      0 < tangentPaperCleanListDensity B.sampleData.W r0 :=
    tangentPaperCleanListDensity_pos B.sampleData.W
      (hr0three.trans (by norm_num))
  have hN : 0 < secondOrderScale B.sampleData.n :=
    secondOrderScale_pos (by omega)
  have hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
        deltaStar :=
    Hcollision R deltaStar
  let flow :
      BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W →
        BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W → Real :=
    R.bankPaperCanonicalSectionNineRatioCellFlow
      M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
        hWne S rho endpoint
  have hpayload :
      R.BankPaperCanonicalSectionNineFinalPayload (K := K0 + 1)
        certificate deltaStar endpoint flow B.L sigma := by
    exact
      (BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_topFrozenRoundedPostHfit
        (M := M) (B := B) (c := c) (depth := depth) (K0 := K0)
        (R := R) (certificate := certificate) (Tsource := Tsource)
        (deltaStar := deltaStar) (betaProt := betaProt)
        (alpha := alpha) (beta := beta) (qTilde := qTilde)
        (sigma := sigma) (placementSeed := placementSeed)
        (activeSeed := activeSeed) (radius := radius) (Cpost := Cpost)
        (quota := quota) (path := path) (endpoint := endpoint)
        (hdelta := hdelta) (hWtwo := hWtwo) (S := S)
        (hpartition := hpartition) (r0 := r0) (rho := rho)
        (tangentConstant := tangentConstant)
        (N := secondOrderScale B.sampleData.n)
        (density := tangentPaperCleanListDensity B.sampleData.W r0)
        (hrho := hrho) (hratio := hratio) (htangent := htangent.le)
        (hN := hN) (hscaleDom := hscaleDom)
        (hMertens := hMertens) (hPNT := hPNT) (hprime := hprime)
        (hTwo := hTwo) (Hmoment := HmomentReady S) (Hpost := Hpost)
        (hKh := hKh) (hdensity := hdensity) (hsigma := hsigma)
        (hscale := hscale) (hchargeDvd := hchargeDvd)
        (hfixedComponents := hfixedComponents) (hmain := hmain)
        (herror := herror) (hceiling := hceiling)
        (hlowerPos := hlowerPos) (hlower := hlower)
        (hlowerScale := hlowerScale)).1
  exact ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    B.sampleData.W, K0 + 1, endpoint, flow, B.L, sigma, hpayload⟩

/-! ## Eventual direct terminal packaging -/

/-- Assemble a same-depth distributed Section 9 terminal from an eventual
frozen-top synchronized input.  All source-independent Section 9 estimates
are supplied by the existing automatic eventual theorems. -/
theorem
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (W K0 depth : Nat)
    {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
    (hdelta : 0 < delta) (hc : 0 < c)
    (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdeltaStar :
      IsPaperCombinedTangentDeltaStar c W r0 deltaStar)
    (hWtwo : 2 ≤ W) (hprefix : 2 * depth + 1 ≤ W)
    (hMoment : canonicalActualMomentCutoff ≤ W)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hwidth :
      delta + M.ratio ≤
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant)
    (hCpost : 0 ≤ Cpost)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hprime :
      TangentFixedRatioPrimeIntervalOccupied W rho)
    (hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W)
    (hqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q ≤ Cq * secondOrderScale n)
    (Hinput :
      BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
        M B c depth K0 deltaStar rho sigma Cpost hdelta) :
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth
      c deltaStar depth := by
  have Hbudget :=
    eventually_bankPaperCanonicalSectionNineBudgetClosure
      M B W K0 depth hdelta hc hr0one hr0three
      hdeltaStar.1.1 hdeltaStar.1.2.1 hdeltaStar.2
      hWtwo hprefix hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hsync hqUpper
  have HmomentReady :=
    eventually_bankPaperCanonical_actualMomentReady
      M hdelta W hMoment
  have Hcollision :=
    eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree hc
  have HKh :=
    BankPaperRealization.eventually_mul_upperTailLength_le_self
      (K0 + 1) hc
  simp only
    [BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput]
    at Hinput
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth]
  filter_upwards [Hinput, hsync, Hbudget, HmomentReady, Hcollision, HKh] with
    n HinputN hsyncN HbudgetN HmomentN HcollisionN hKhN
  exact
    bankPaperCanonicalSectionNineTopFrozenFinalPayload_eventStep
      M (B n) hdelta hsyncN.1 hsyncN.2 hWtwo hr0three
      hrho hratio htangent hsigma hMertens hPNT hprime
      HinputN HbudgetN HmomentN HcollisionN hKhN

end

end Erdos390.WholePaper
