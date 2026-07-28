import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalGeometry

/-!
# Section 9 final geometry from the frozen-top source

This connector extracts the only two Post-Hfit fields consumed by the
Section 9 distributed construction--the rounded tangent input and guarded
endpoint slack--from the verified nearest-integer frozen-top package.
No identification with the older no-top global source is used.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-- Feed a frozen-top rounded Post-Hfit package directly into the literal
Section 9 final geometry theorem. -/
theorem
    bankPaperCanonicalSectionNineFinalPayload_of_topFrozenRoundedPostHfit
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde sigma : Real)
    (placementSeed activeSeed : B.sampleData.Sample → Real)
    (radius : NNReal) (Cpost : Real)
    (quota : Int) (path : Real → B.ParamSpace)
    (endpoint : Nat → Real)
    (hdelta : 0 < delta) (hWtwo : 2 ≤ B.sampleData.W)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S)
    (r0 rho tangentConstant N density : Real)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 ≤ tangentConstant) (hN : 0 < N)
    (hscaleDom : Cpost * B.q / B.L ≤
      tangentConstant * N / Real.log (y B.sampleData.n))
    (hMertens : fullReciprocalSumUniformCutoff ≤ B.sampleData.W)
    (hPNT : TangentFixedRatioPrimeCountLower B.sampleData.W rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied
      B.sampleData.W rho)
    (hTwo : ∀ k : Fin M.cellCount,
      2 ≤ scalePoint B.sampleData.n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S))
    (Hpost :
      BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
        (K := K0 + 1) B R certificate
        (R.paperFixedExceptionalFactors deltaStar) Tsource
        deltaStar betaProt alpha beta qTilde sigma
        placementSeed activeSeed radius Cpost
        (bankPaperCanonicalRatioCellIndex
          M hdelta B.n_gt_one (by omega) S rho)
        quota path endpoint)
    (hKh : (K0 + 1) * upperTailLength c B.sampleData.n ≤
      B.sampleData.n)
    (hdensity : 0 < density) (hsigma : 0 < sigma)
    (hscale : B.L * N = (B.sampleData.n : Real))
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar)
    (hmain : tangentDistributedPaperMainBudget
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio) sigma ≤ density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
      (bankPaperCanonicalRatioCellTrafficErrorCoefficient M
        B.sampleData.n B.sampleData.W rho tangentConstant)
      (bankPaperCanonicalRatioCellIncidentErrorCoefficient
        B.sampleData.W B.sampleData.n rho tangentConstant)
      sigma ≤ density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget
      B.sampleData.n (yNat B.sampleData.n)
      (tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W)) ≤ density ^ 2 / 96)
    (hlowerPos :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request)
    (hlower :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request ≤
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges flow)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            B.L sigma
            (fun edge : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W ×
                BankPaperCanonicalTangentPrime
                  B.sampleData.n B.sampleData.W =>
              flow edge.1 edge.2)
            B.sampleData.n (K0 + 1)
            (upperTailLength c B.sampleData.n)
            (roughHeadModulus B.sampleData.W)
            (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
            (yNat B.sampleData.n) R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet certificate
              (R.paperFixedExceptionalFactors deltaStar))
            request).card)
    (hlowerScale :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        ∀ side,
          density * B.sampleData.n ≤
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := density) request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request) :
    R.BankPaperCanonicalSectionNineFinalPayload (K := K0 + 1)
      certificate deltaStar endpoint
      (R.bankPaperCanonicalSectionNineRatioCellFlow
        M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
          (by omega) S rho endpoint)
      B.L sigma ∧
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho) r0 := by
  have Hpost' := Hpost
  unfold BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage at Hpost'
  unfold BankPaperCanonicalPostHfitGuardedSlackPackageOfSource at Hpost'
  have HselectorPartition :
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        B.partition.band
        (bankPaperCanonicalRatioCellIndex
          M hdelta B.n_gt_one (by omega) S rho)
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band
          (bankPaperCanonicalRatioCellIndex
            M hdelta B.n_gt_one (by omega) S rho))
        endpoint := by
    exact Hpost'.2.2.2.2.1
  have Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W (K0 + 1)
        alpha beta B.L sigma endpoint := by
    exact Hpost'.2.2.2.2.2
  exact
    bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack
      (M := M) (B := B) (c := c) (depth := depth) (K0 := K0)
      (R := R) (certificate := certificate)
      (deltaStar := deltaStar) (alpha := alpha) (beta := beta)
      (sigma := sigma) (_radius := radius) (Cpost := Cpost)
      (endpoint := endpoint) (hdelta := hdelta) (hWtwo := hWtwo)
      (S := S) (hpartition := hpartition) (r0 := r0) (rho := rho)
      (tangentConstant := tangentConstant) (N := N) (density := density)
      (hrho := hrho) (hratio := hratio) (htangent := htangent)
      (hN := hN) (hscaleDom := hscaleDom) (hMertens := hMertens)
      (hPNT := hPNT) (hprime := hprime) (hTwo := hTwo)
      (Hmoment := Hmoment) (HselectorPartition := HselectorPartition)
      (Hslack := Hslack) (hKh := hKh) (hdensity := hdensity)
      (hsigma := hsigma) (hscale := hscale) (hchargeDvd := hchargeDvd)
      (hfixedComponents := hfixedComponents) (hmain := hmain)
      (herror := herror) (hceiling := hceiling)
      (hlowerPos := hlowerPos) (hlower := hlower)
      (hlowerScale := hlowerScale)

end BankPaperRealization

end

end Erdos390.WholePaper
