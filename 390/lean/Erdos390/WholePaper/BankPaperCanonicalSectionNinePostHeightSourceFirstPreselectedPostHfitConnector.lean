import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshSelectorProvider
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstEventualPostHfitConnector

/-!
# Fixed-mesh Post-Hfit consumption with preselected constants

The global source-first orchestration chooses the placed-selector constant
and the uniform Proposition 8.7 constants before it selects the final mesh.
This file is the fixed-mesh consumption kernel for those choices.

It assumes the mesh-uniform placed-selector callback and the already
specialized one-mesh Proposition 8.7 callback.  It only intersects their
eventual fields with the genuine coherent bridge/source obligation and the
remaining exported numerical events.  In particular, it does not choose a
new selector constant, radius, or post-adjustment constant.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 3600000

/-- Consume constants selected before the final mesh and construct the
eventual synchronized frozen-top Post-Hfit input on that mesh.

`Hselector` is uniform in every later mesh; this theorem specializes it to
the displayed `M`.  `HP87` is already the corresponding single-mesh
callback.  The conclusion uses the supplied public bridge family `B` and
the preselected constant `CP87` literally. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (rho sigma : Real)
    (Cinitial : Real) (radius : NNReal) (CP87 : Real)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (Hsource :
      BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G depth W K0 E Ntail F
          deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
          physicalEtaFloor postMarginFloor Cmass density
          logY Lambda0 mFrozen qTilde M hdelta B)
    (Hselector :
      BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        Patterns I Cprom Cbank G (c := c) depth W K0
          deltaStar betaProt betaAct mu
          logY Lambda0 mFrozen qTilde Cinitial)
    (HP87 :
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
        (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
          betaProt betaAct postMarginFloor Cmass density
          (bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde)
          Cinitial radius CP87 hdelta)
    (hCinitial : 0 ≤ Cinitial)
    (_hradius : 0 < (radius : Real))
    (_hCP87 : 0 ≤ CP87)
    (hc : 0 < c)
    (hTwoW : 2 ≤ W)
    (hdeltaStar : 0 < deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hsigma : 0 < sigma)
    (hsigmaProt : sigma ≤ betaProt)
    (hMoment : canonicalActualMomentCutoff ≤ W) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma CP87 hdelta := by
  have Halpha :=
    eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
      (Head := PaperHeadSimplex.Tag P)
      (Band := BankPaperCanonicalExponentBand M)
      W K0 hc (add_nonneg hbetaProt hbetaAct.le)
        hbetaUpper hKlarge
  have Hmoment :=
    eventually_bankPaperCanonical_actualMomentReady
      M hdelta W hMoment
  have Hnonsmooth :=
    eventually_roughCanonicalBalancedNonsmoothBounds
      W K0 hc hdeltaStar hbetaAct hsigmaProt
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have HbetaRoom :
      ∀ᶠ n : Nat in atTop, betaProt + betaAct ≤ L n :=
    hLTop.eventually (eventually_ge_atTop (betaProt + betaAct))
  have hCactive : 0 ≤ Cmass / density :=
    div_nonneg hCmass hdensity.le
  have HlargeL :=
    BridgeData.eventually_canonical_exponential_slack_le_L
      (Head := PaperHeadSimplex.Tag P)
      (Band := BankPaperCanonicalExponentBand M)
      2 (by norm_num) W radius
        ((betaProt + Cmass / density) + sigma)
        (Cmass / density) hCactive
  simp only
    [BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation]
    at Hsource
  simp only
    [BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback]
    at Hselector
  simp only
    [BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback]
    at HP87
  simp only
    [BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput]
  filter_upwards [
      Hsource, Halpha, Hselector, HP87, Hmoment, Hnonsmooth,
      HbetaRoom, HlargeL,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n hsourceN halphaN hselectorN hP87N hmomentN
        hnonsmoothN hbetaRoomN hlargeLN hnCutoff hyCutoff
  rcases hsourceN with
    ⟨Bsource, hnTail, J, S, Hgap, hsep, hremaining,
      hbridge, hBn, hBW, hbetaProtSync, hbetaActSync,
      hcanonical, hqTilde, hCmassSync, hdensitySync⟩
  subst n
  let R := F.realization Bsource.sampleData.n hnTail
  let certificate := F.certificate Bsource.sampleData.n hnTail
  have halpha : 0 ≤ J.alpha ∧ J.alpha ≤ 1 := by
    apply Set.mem_Icc.mp
    simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
        hbetaProtSync, hbetaActSync] using
      halphaN Bsource rfl hBW
  have hbetaBox :
      0 ≤ J.beta / J.postHeightBridge.L ∧
        J.beta / J.postHeightBridge.L ≤ 1 := by
    have hbetaNonneg : 0 ≤ J.beta := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
        hbetaProtSync, hbetaActSync] using
        add_nonneg hbetaProt hbetaAct.le
    have hbetaLe : J.beta ≤ J.postHeightBridge.L := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
        hbetaProtSync, hbetaActSync,
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
        BridgeData.L] using hbetaRoomN
    exact
      ⟨div_nonneg hbetaNonneg J.postHeightBridge.L_pos.le,
        (div_le_one J.postHeightBridge.L_pos).2 hbetaLe⟩
  have hpool :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar J.postHeightBridge.sampleData.W
          (K0 + 1) 1).Nonempty :=
    bankPaperCanonicalSectionNinePostHeight_guardedBroadCorrectionPool_nonempty_of_sourceInputs
      J S
  have hdFamily :
      (J.d : Real) =
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData] using
      (bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps
        J S Hgap)
  have hqFamily :
      J.postHeightBridge.q =
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    calc
      J.postHeightBridge.q = J.qn := J.postHeightBridge_q
      _ =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n :=
        Hgap.finalActiveMass_family
  have hselector :
      ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs (bankPaperCanonicalSelectorValuationDeficit
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.placedPreSelector p) ≤
          Cinitial * J.postHeightBridge.q /
            ((p : Real) * J.postHeightBridge.L) :=
    hselectorN M hdelta Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical hqTilde
      halpha hbetaBox hpool hdFamily hqFamily
  have hroundedFrozenLedger :
      ∀ m : J.postHeightBridge.sampleData.Sample,
        BridgeData.frozenAmbientWeight
            (bankPaperCanonicalActualFrozenValue
              (candidates :=
                R.roughCanonicalGuardedCandidateSet certificate
                  deltaStar (K0 + 1)))
            (bankPaperCanonicalActualFrozenWeight
              J.postHeightBridge.sampleData
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1))
              J.roundedSourceSelector J.roundedActiveSeed)
            (J.postHeightBridge.sampleData.value m) ≤
          (J.betaProt + S.Cmass / S.density) /
            J.postHeightBridge.L :=
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenLedger_of_sourceInputs
      J S
  have hprimeDeviation :
      J.postHeightBridge.primeDeviationL1 ≤
        7 * J.postHeightBridge.w := by
    rcases hmomentN with ⟨hWne, _hnOne, _hscalePoints, hready⟩
    let Pmesh :=
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta J.postHeightBridge.n_gt_one J.hW J.scaleSeparation
    let Emesh :=
      RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
        M hdelta J.postHeightBridge.n_gt_one J.hW J.scaleSeparation
    have hreadyMesh :
        RegularMeshPrimeCutoffs.Mesh.MomentReady M Pmesh := by
      subst W
      simpa only [Pmesh] using hready J.scaleSeparation
    have hL1 :=
      RegularMeshPrimeCutoffs.Mesh.actual_L1_bound_of_ready
        M Pmesh Emesh (fun _ ↦ rfl) (fun _ ↦ rfl)
          hdelta J.postHeightBridge.n_gt_one hreadyMesh
    calc
      J.postHeightBridge.primeDeviationL1 =
          Pmesh.totalL1 := rfl
      _ ≤ 7 * (delta + M.ratio) := hL1
      _ ≤ 7 * (delta + eta) := by
        nlinarith [M.ratio_le_eta]
      _ = 7 * J.postHeightBridge.w := rfl
  have hlocalP87 :
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
        M Cinitial radius CP87 J S :=
    hP87N Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical
      Hgap.postHeightTarget_margin hCmassSync hdensitySync hqFamily
  have hTwoWJ : 2 ≤ J.postHeightBridge.sampleData.W := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      hBW] using hTwoW
  have hsigmaProtJ : sigma ≤ J.betaProt := by
    simpa only [hbetaProtSync] using hsigmaProt
  have hlargeL :
      (J.betaProt + S.Cmass / S.density) +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  2 J.postHeightBridge.sampleData.W +
              J.postHeightBridge.nuisanceStatisticCoefficient 2) *
                (3 * (radius : Real)))) *
            (S.Cmass / S.density) + sigma ≤
        J.postHeightBridge.L := by
    have hraw :=
      hlargeLN J.postHeightBridge
        (by rfl)
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hBW)
    rw [hbetaProtSync, hCmassSync, hdensitySync]
    linarith only [hraw]
  have hnonsmooth :
      ∀ label,
        RoughCanonicalActiveNonexceptionalLabel
            J.postHeightBridge.sampleData.n deltaStar label →
          sigma / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            J.beta / J.postHeightBridge.L ∧
          J.beta / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            1 - sigma / J.postHeightBridge.L := by
    have hraw :=
      hnonsmoothN depth R certificate
        hnCutoff hyCutoff
    simpa only [
      RoughCanonicalBalancedNonsmoothBounds,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
      bankPaperCanonicalPostHfitBalancedAlpha,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      BridgeData.L, hBW, hbetaProtSync, hbetaActSync] using hraw
  have Hlocal :=
    bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields
      deltaStar rho sigma Cinitial hCinitial radius CP87 M
        Bsource R certificate I hdelta J S Hgap
        halpha hselector hroundedFrozenLedger hprimeDeviation
        hlocalP87 hTwoWJ hsigma hsigmaProtJ hlargeL hnonsmooth
  rcases Hlocal with ⟨_halpha, A, hcellIndex⟩
  have Hpublic :=
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_postHeightInputs
      M Bsource R certificate I deltaStar rho sigma CP87
        hdelta J S A hcellIndex
  rw [hbridge]
  exact Hpublic

end BankPaperRealization

end

end Erdos390.WholePaper
