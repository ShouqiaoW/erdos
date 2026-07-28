import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightEventualConnector

/-!
# Statement audit for the frozen-top same-witness handoff
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

namespace BankPaperRealization

/-! The capacity realization and guarded certificate occur inside the
eventual quantifier and after the canonical-partition witness. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar rho sigma Cpost hdelta ↔
      ∀ᶠ n : Nat in atTop,
        ∃ hW : (B n).sampleData.W ≠ 0,
          ∃ Sscale : ScaleSeparation M
              (B n).sampleData.n (B n).sampleData.W,
            (B n).partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta (B n).n_gt_one hW Sscale ∧
              ∀ (R : BankPaperRealization (B n).sampleData.n
                    (upperEndpoint (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n)))
                (certificate : GuardedCentralAnchorCertificate c depth
                  (B n).sampleData.n R.anchorGuardLeftCore
                  R.anchorGuardRightCore
                  (R.centralChangedMarkers depth)),
                centralAnchorDivisor (B n).sampleData.n
                      (centralAnchorCutoff depth (B n).sampleData.n)
                      certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                (baseBankFactors R.exactificationState).prod id ∣
                    certificate.prechargedTailTarget →
                R.selectorTailCharge
                      (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                certificate.prechargedTailTarget *
                      centralAnchorDivisor (B n).sampleData.n
                        (centralAnchorCutoff depth (B n).sampleData.n)
                        certificate.q =
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                ∃ Hsource :
                    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
                      (B n) R certificate K0 deltaStar,
                  ∃ Hdependent :
                      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightDependentInputsAt
                        (B n) R certificate K0 deltaStar sigma Cpost
                          Hsource,
                    Hdependent.cellIndex =
                      bankPaperCanonicalRatioCellIndex
                        M hdelta (B n).n_gt_one hW Sscale rho := by
  rfl

#check
  BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
#check
  bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_symmetricHeightInputs
#check
  bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput_of_combinedChargeTerminal_symmetricHeight

end BankPaperRealization

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
    (Hcapacity :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (Hlocal :
      BankPaperRealization.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar rho sigma Cpost hdelta) :
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth
      c deltaStar depth :=
  bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSymmetricHeightLocalSupplier
    M B W K0 depth hdelta hc hr0one hr0three hdeltaStar hWtwo
      hprefix hMoment hMertens hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hPNT hprime hsync hqUpper Hcapacity Hlocal

#check
  bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSymmetricHeightLocalSupplier

end

end Erdos390.WholePaper
