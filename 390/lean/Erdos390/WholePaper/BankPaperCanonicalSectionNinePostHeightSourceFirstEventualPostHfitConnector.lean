import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteExportedFields
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightLocalInputConnector
import Erdos390.Full.PaperProposition87CanonicalFeasibilitySlackEventually

/-!
# Source-first eventual Post-Hfit connector

This file performs the fixed-mesh eventual intersection which comes after
the source-first coherent bridge/source construction.

The only Proposition 8.7 input is a specialized eventual callback.  It is
stated below at the exact finite field consumed by
`bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields`;
it does not assume a dependent-input package, a Post-Hfit input, or any
eventual conclusion.  Every other field is constructed here from the
source obligation, the Section 8 analytic ledger, and exported numerical
estimates.
-/

open Filter Topology Set Asymptotics
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

/-! ## Exact specialized Proposition 8.7 callback -/

/-- The precise one-index Proposition 8.7 field used by the post-height
finite reduction.

This definition is intentionally only the local P87 callback.  In
particular, it contains neither the selector conclusion nor any local or
eventual Post-Hfit package. -/
def BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    (Cinitial : Real) (radius : NNReal) (Cpost : Real)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) : Prop :=
  ∀ (Delta : BankPaperCanonicalExponentBand M → Real),
    J.postHeightBridge.HasTargetEnvelopes (7 * Cinitial) Delta →
    ∀ (markedTarget : Nat → Real) (N : Real),
      0 ≤ N →
      J.postHeightBridge.q ≤ (1 : Real) * N →
      (∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs (markedTarget p -
          J.postHeightBridge.paperMoment
            (J.postHeightBridge.markedValuation p) 0) ≤
          Cinitial * N /
            ((p : Real) * J.postHeightBridge.L)) →
      (∀ j, Delta j =
        J.postHeightBridge.markedBandResidual markedTarget 0 j) →
      ∀ {Fixed : Type} [Fintype Fixed],
        ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
          (quota : Int),
          (quota : Real) = (∑ f, fixedWeight f) +
            J.postHeightBridge.q →
          J.postHeightBridge.sampleData.HeadPatternsSeparated →
          (∀ x,
            BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
              Icc (0 : Real) 1) →
          (∀ m : J.postHeightBridge.sampleData.Sample,
            BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (J.postHeightBridge.sampleData.value m) ≤
              (J.betaProt + S.Cmass / S.density) /
                J.postHeightBridge.L) →
          (∀ m : J.postHeightBridge.sampleData.Sample,
            J.postHeightBridge.baseline.baseWeight m ≤
              (S.Cmass / S.density) / J.postHeightBridge.L) →
          J.postHeightBridge.HasPaperProposition87Conclusion
            Delta radius markedTarget N Cpost
              fixedValue fixedWeight quota

/-- An upstream-only eventual callback for the exact local P87 field.

The premises are the literal source-family synchronizations available from
`BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation`.
The post-height margin premise is a primitive-gap field.  No conclusion
contract is among the premises. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct postMarginFloor Cmass density : Real)
    (qMass : Nat → Real)
    (Cinitial : Real) (radius : NNReal) (Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∀ (Bsource : BridgeData (PaperHeadSimplex.Tag P)
        (BankPaperCanonicalExponentBand M)),
      Bsource.sampleData.n = n →
      Bsource.sampleData.W = W →
      ∀
        (R : BankPaperRealization Bsource.sampleData.n
          (upperEndpoint Bsource.sampleData.n
            (upperTailLength c Bsource.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth
          Bsource.sampleData.n R.anchorGuardLeftCore
          R.anchorGuardRightCore (R.centralChangedMarkers depth))
        (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
          (K0 := K0) M Bsource R certificate I deltaStar hdelta)
        (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
          M Bsource R certificate I deltaStar hdelta J),
      J.betaProt = betaProt →
      J.betaAct = betaAct →
      ∀
        (hsep :
          physicalBound (I.upper .minus)
              J.postHeightBridge.sampleData.n <
            physicalBound (I.lower .plus)
              J.postHeightBridge.sampleData.n)
        (hremaining :
          ∀ cell : Cell (PaperHeadSimplex.Tag P),
            (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
              (G J.postHeightBridge.sampleData.n).guards).Nonempty),
      J.postHeightBridge.sampleData =
          canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            Patterns I (G J.postHeightBridge.sampleData.n)
              hsep hremaining →
      postMarginFloor ≤ J.postHeightTarget.cellMassMargin →
      S.Cmass = Cmass →
      S.density = density →
      J.postHeightBridge.q = qMass n →
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
        M Cinitial radius Cpost J S

/-- Choice form of the specialized P87 callback.  Its quantifier order is
the required one: the selector theorem first fixes `Cinitial`; only then
does P87 choose `radius` and `Cpost`. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Factory
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct postMarginFloor Cmass density : Real)
    (qMass : Nat → Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ Cinitial : Real, 0 ≤ Cinitial →
    ∃ radius : NNReal, ∃ Cpost : Real,
      0 < (radius : Real) ∧ 0 ≤ Cpost ∧
        BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
          (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
            betaProt betaAct postMarginFloor Cmass density
            qMass Cinitial radius Cpost hdelta

/-! ## Fixed-mesh eventual compositor -/

/-- Intersect the source-first bridge obligation with all exported
fixed-mesh estimates and produce the public eventual synchronized
Post-Hfit input.

The conclusion exposes the selector and P87 choices only to record their
honest dependency order.  The public bridge family is the supplied `B`;
inside the proof it is rewritten pointwise using the equality
`B n = J.postHeightBridge` supplied by the source obligation. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstEventualPostHfitInput
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
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (Hsource :
      BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G depth W K0 E Ntail F
          deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
          physicalEtaFloor postMarginFloor Cmass density
          logY Lambda0 mFrozen qTilde M hdelta B)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde))
    (HP87 :
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Factory
        (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar betaProt betaAct
          postMarginFloor Cmass density
          (bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde)
          hdelta)
    (hc : 0 < c)
    (hTwoW : 2 ≤ W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1 / 18)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 ≤ W)
    (hmu : 0 < mu)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hsigma : 0 < sigma)
    (hsigmaProt : sigma ≤ betaProt)
    (hMoment : canonicalActualMomentCutoff ≤ W) :
    ∃ Cinitial : Real, ∃ radius : NNReal, ∃ Cpost : Real,
      0 ≤ Cinitial ∧ 0 < (radius : Real) ∧ 0 ≤ Cpost ∧
        BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
          M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  have hWone : 1 < W := by omega
  obtain ⟨Azero, hAzero, Nzero, Hzero⟩ :=
    exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate
      Patterns I Cprom Cbank G W hWone hHeadLe
  have HdBigO :=
    bankPaperCanonicalSectionEight_d_isBigO
      W (K0 + 1) c betaAct hmu
        logY Lambda0 mFrozen qTilde Hledger
  obtain ⟨Cd, hCd, Hd⟩ := (isBigO_iff').mp HdBigO
  rcases
      bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
        W (K0 + 1) hc hbetaAct hmu
          logY Lambda0 mFrozen qTilde Hledger with
    ⟨cFinal, hcFinal, HfinalMass⟩
  obtain ⟨Cinitial, hCinitial, Hselector⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate
      (betaProt := betaProt) (betaAct := betaAct)
      P Patterns I Cprom Cbank G W K0 depth hTwoW hHeadLe
        hc hdeltaStar hdeltaStarUpper (by norm_num : (0 : Real) < 1)
        hcFinal hAzero.le hCd.le hprefix
  obtain ⟨radius, Cpost, hradius, hCpost, HP87event⟩ :=
    HP87 Cinitial hCinitial
  refine ⟨Cinitial, radius, Cpost, hCinitial, hradius, hCpost, ?_⟩
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
    [BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput]
  filter_upwards [
      Hsource, Halpha, Hselector, HP87event, Hd, HfinalMass,
      Hmoment, Hnonsmooth, HbetaRoom, HlargeL,
      eventually_ge_atTop Nzero,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n hsourceN halphaN hselectorN hP87N hdN hfinalMassN
        hmomentN hnonsmoothN hbetaRoomN hlargeLN hNzero
        hnCutoff hyCutoff
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
  have hscaleDiv :
      0 < secondOrderScale Bsource.sampleData.n /
        L Bsource.sampleData.n := by
    have hnOne : 1 < Bsource.sampleData.n := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using J.postHeightBridge.n_gt_one
    exact div_pos (secondOrderScale_pos hnOne) (L_pos hnOne)
  have hdFamily :
      (J.d : Real) =
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData] using
      (bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps
        J S Hgap)
  have hdBound :
      |(J.d : Real)| ≤
        Cd *
          (secondOrderScale J.postHeightBridge.sampleData.n /
            J.postHeightBridge.L) := by
    have hdBoundN :
        |bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n| ≤
          Cd * (secondOrderScale Bsource.sampleData.n /
            L Bsource.sampleData.n) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hscaleDiv] using hdN
    simpa only [
      hdFamily,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      BridgeData.L] using hdBoundN
  have hmass :
      cFinal *
          secondOrderScale J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.q := by
    simpa only [
      J.postHeightBridge_q,
      Hgap.finalActiveMass_family,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hfinalMassN
  have hzero :
      ∀ p : BandPrime J.postHeightBridge.sampleData.n
            J.postHeightBridge.sampleData.W,
        ∀ sign : PhysicalSign,
          (J.postHeightBridge.guardedCellProbability
              (none, sign)).expect
              (fun m ↦ valuation p.1 (m : Nat)) ≤
            Azero / (p.1 : Real) := by
    intro p sign
    exact
      Hzero J.postHeightBridge
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hNzero)
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hBW)
        hsep hremaining hcanonical p sign
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
      halpha hbetaBox hpool hdBound hmass hzero
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
    rcases hmomentN with ⟨hWne, hnOne, _hscalePoints, hready⟩
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
        M Cinitial radius Cpost J S :=
    hP87N Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical
      Hgap.postHeightTarget_margin hCmassSync hdensitySync
      (by
        calc
          J.postHeightBridge.q = J.qn := J.postHeightBridge_q
          _ =
              bankPaperCanonicalSmoothFinalActiveMassFamily
                mu logY Lambda0 mFrozen qTilde
                  Bsource.sampleData.n :=
            Hgap.finalActiveMass_family)
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
      deltaStar rho sigma Cinitial hCinitial radius Cpost M
        Bsource R certificate I hdelta J S Hgap
        halpha hselector hroundedFrozenLedger hprimeDeviation
        hlocalP87 hTwoWJ hsigma hsigmaProtJ hlargeL hnonsmooth
  rcases Hlocal with ⟨_halpha, A, hcellIndex⟩
  have Hpublic :=
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_postHeightInputs
      M Bsource R certificate I deltaStar rho sigma Cpost
        hdelta J S A hcellIndex
  rw [hbridge]
  exact Hpublic

end BankPaperRealization

end

end Erdos390.WholePaper
