import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenEventStepConnector

/-! Statement audit for the public frozen-top Section 9 event step. -/

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

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
        M B c depth K0 deltaStar rho sigma Cpost hdelta ↔
      ∃ R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)),
        ∃ certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
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
                                  quota path endpoint := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
        M B c depth K0 deltaStar rho sigma Cpost hdelta ↔
      ∀ᶠ n : Nat in atTop,
        BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
          M (B n) c depth K0 deltaStar rho sigma Cpost hdelta := by
  rfl

example
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
      c deltaStar depth :=
  bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit
    M B W K0 depth hdelta hc hr0one hr0three hdeltaStar hWtwo
      hprefix hMoment hMertens hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hPNT hprime hsync hqUpper Hinput

#check BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
#check BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
#check bankPaperCanonicalSectionNineTopFrozenFinalPayload_eventStep
#check
  bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit

end

end Erdos390.WholePaper
