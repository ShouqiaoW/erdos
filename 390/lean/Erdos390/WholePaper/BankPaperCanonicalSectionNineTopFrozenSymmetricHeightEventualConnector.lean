import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenEventStepConnector

/-!
# Same-witness Section 9 handoff for frozen-top symmetric-height inputs

This file lifts the selector-correct finite input packages to the eventual
same-witness quantifier order used by the capacity terminal.  The local
supplier receives the exact bank and guarded certificate selected by the
combined-charge terminal.  It also uses the same canonical-partition
witness which defines the ratio-cell index in the frozen-top Post-hfit
package.

No equality with the legacy global source selector is used.
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

/-! ## Eventual same-witness local supplier -/

/-- Eventual selector-correct frozen-top finite inputs for the exact
capacity bank and certificate selected at each index.

The final equality is the only mesh-dependent compatibility field: it
identifies the dependent package's tangent cell index with the ratio-cell
index built from the same canonical-partition witness. -/
def BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
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
                    (B n) R certificate K0 deltaStar sigma Cpost Hsource,
                Hdependent.cellIndex =
                  bankPaperCanonicalRatioCellIndex
                    M hdelta (B n).n_gt_one hW Sscale rho

/-! ## One-index and eventual synchronized constructors -/

/-- Package selector-correct finite inputs for one fixed capacity witness as
the public frozen-top synchronized input. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_symmetricHeightInputs
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
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hcombined :
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hbaseDvd :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget)
    (hchargeDvd :
      R.selectorTailCharge
            (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (htargetTail :
      certificate.prechargedTailTarget *
            centralAnchorDivisor B.sampleData.n
              (centralAnchorCutoff depth B.sampleData.n)
              certificate.q =
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hW : B.sampleData.W ≠ 0)
    (Sscale : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition :
      B.partition =
        RegularMeshPrimeCutoffs.Mesh.canonicalPartition
          M hdelta B.n_gt_one hW Sscale)
    (Hsource :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
        B R certificate K0 deltaStar)
    (Hdependent :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightDependentInputsAt
        B R certificate K0 deltaStar sigma Cpost Hsource)
    (hcellIndex :
      Hdependent.cellIndex =
        bankPaperCanonicalRatioCellIndex
          M hdelta B.n_gt_one hW Sscale rho) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
      M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  obtain ⟨quota, path, endpoint, Hpost⟩ :=
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_symmetricHeightInputs
      (K0 := K0) B R certificate deltaStar sigma Cpost
        Hsource Hdependent
  refine
    ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd, htargetTail,
      hW, Sscale, hpartition, Hsource.Tsource, Hsource.core.betaProt,
      Hsource.alpha, Hsource.beta, Hsource.qTilde,
      Hsource.placementSeed, Hsource.activeSeed, Hdependent.radius,
      quota, path, endpoint, ?_⟩
  rw [hcellIndex] at Hpost
  exact Hpost

/-- Apply the frozen-top local supplier to the very capacity witnesses
selected by the combined-charge terminal. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput_of_combinedChargeTerminal_symmetricHeight
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n)
    (Hcapacity :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (Hlocal :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar rho sigma Cpost hdelta) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  simp only [BankPaperCombinedChargeTerminalAtDepth] at Hcapacity
  simp only
    [BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier]
    at Hlocal
  simp only
    [BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput]
  filter_upwards [Hcapacity, hBn, Hlocal] with
    n HcapacityN hBnN HlocalN
  have HcapacityN' :
      ∃ R : BankPaperRealization (B n).sampleData.n
          (upperEndpoint (B n).sampleData.n
            (upperTailLength c (B n).sampleData.n)),
        ∃ certificate : GuardedCentralAnchorCertificate c depth
            (B n).sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth),
          centralAnchorDivisor (B n).sampleData.n
                (centralAnchorCutoff depth (B n).sampleData.n)
                certificate.q * R.prechargeBaseStateProduct ∣
              centralTailProduct (B n).sampleData.n
                (upperTailLength c (B n).sampleData.n) ∧
            (baseBankFactors R.exactificationState).prod id ∣
              certificate.prechargedTailTarget ∧
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
              certificate.prechargedTailTarget ∧
            (∀ p ∈ primesUpTo (2 * depth + 1),
              (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                    secondOrderScale (B n).sampleData.n +
                  (R.selectorTailCharge
                    (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
                certificate.prechargedTailTarget.factorization p) ∧
            certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors deltaStar) *
                R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) =
              certificate.prechargedTailTarget ∧
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) := by
    rw [hBnN]
    exact HcapacityN
  obtain
      ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd,
        _hretained, _hselectorIdentity, htargetTail⟩ := HcapacityN'
  obtain ⟨hW, Sscale, hpartition, Hsupplier⟩ := HlocalN
  obtain ⟨Hsource, Hdependent, hcellIndex⟩ :=
    Hsupplier R certificate hcombined hbaseDvd hchargeDvd htargetTail
  exact
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_symmetricHeightInputs
      (K0 := K0) M (B n) R certificate deltaStar rho sigma Cpost
      hdelta hcombined hbaseDvd hchargeDvd htargetTail hW Sscale
      hpartition Hsource Hdependent hcellIndex

end BankPaperRealization

/-! ## Direct terminal constructor -/

/-- A same-witness frozen-top symmetric-height supplier, together with the
already selected combined-charge capacity terminal, produces the distributed
Section 9 terminal at that same depth. -/
theorem
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSymmetricHeightLocalSupplier
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
      c deltaStar depth := by
  have hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n := by
    filter_upwards [hsync] with n hsyncN
    exact hsyncN.1
  have Hinput :
      BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
        M B c depth K0 deltaStar rho sigma Cpost hdelta :=
    BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput_of_combinedChargeTerminal_symmetricHeight
      M B deltaStar rho sigma Cpost hdelta hBn Hcapacity Hlocal
  exact
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit
      M B W K0 depth hdelta hc hr0one hr0three hdeltaStar hWtwo
      hprefix hMoment hMertens hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hPNT hprime hsync hqUpper Hinput

end

end Erdos390.WholePaper
