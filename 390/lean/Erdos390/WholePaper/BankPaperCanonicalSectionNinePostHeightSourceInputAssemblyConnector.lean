import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineActiveLedgerConnector

/-!
# Mechanical source-input assembly for the fresh post-height bridge

This file is downstream from the honest reduction boundary in
`BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector`.  It does
not alter that boundary and does not assert a final supplier.

There are two results.

* A finite constructor takes one already-chosen fresh bridge `J`, its
  genuinely target-dependent synchronization facts, and one already-produced
  rounded source state.  Canonical sample geometry and the two literal
  capacity divisibilities then construct
  `BankPaperCanonicalSectionNinePostHeightSourceInputsAt` and the existing
  `BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt`.
* A mesh-uniform eventual wrapper supplies all of the mechanical hypotheses
  of that finite constructor from the existing Section 8 ledger, canonical
  guarded-cell estimates, bridge-guard agreement, and the rounded-source
  theorem.  The realization and certificate are the literal fiber of the
  same `BankPaperCanonicalGuardedTailFamily`.

The wrapper still quantifies over `J` and assumes the four target-margin
bounds, the exact frozen/final-mass synchronization, and
`BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt`.  Thus it is an
assembly theorem, not a renamed solution of the target/source producer gap.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.FiniteProbability
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Finite assembly -/

/-- Construct the literal post-height source package and the existing
primitive-gap record from one coherent finite bridge.

The hypotheses named `hsourceState`, `hmFrozen`, `hfinalActiveMass`, and
`hsourceResidual` are exact outputs or inputs of existing narrow
connectors.  Everything else stored in the resulting source package is
derived here from canonical sample geometry or from the two displayed
capacity divisibilities. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sign, 1 ≤ I.lower sign)
    (hupperTwo : ∀ sign, I.upper sign ≤ 2)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (deltaStar mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (hsourceMarginFloor : 0 < sourceMarginFloor)
    (hheadMarginFloor : 0 < headMarginFloor)
    (hphysicalEtaFloor : 0 < physicalEtaFloor)
    (hpostMarginFloor : 0 < postMarginFloor)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (hexponentSync : J.exponent = E)
    (hhead : primesUpTo J.postHeightBridge.sampleData.W ⊆ P)
    (hsep :
      physicalBound (I.upper .minus) J.postHeightBridge.sampleData.n <
        physicalBound (I.lower .plus) J.postHeightBridge.sampleData.n)
    (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      (rawCell (PaperHeadSimplex.pattern P hprime E) I
          J.postHeightBridge.sampleData.n cell \
        (G J.postHeightBridge.sampleData.n).guards).Nonempty)
    (hcanonical :
      J.postHeightBridge.sampleData =
        canonicalSampleData
          (W := J.postHeightBridge.sampleData.W)
          (PaperHeadSimplex.pattern P hprime E) I
          (G J.postHeightBridge.sampleData.n) hsep hremaining)
    (hguardAgreement :
      BankPaperCanonicalBridgeGuardAgreement
        (G J.postHeightBridge.sampleData.n) R certificate deltaStar)
    (hupperBroad : ∀ sign,
      physicalBound (I.upper sign) J.postHeightBridge.sampleData.n ≤
        2 * J.postHeightBridge.sampleData.n -
          (K0 + 1) *
            upperTailLength c J.postHeightBridge.sampleData.n)
    (hroughDepth :
      (K0 + 1) * upperTailLength c J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.sampleData.n)
    (hqnOne : 1 ≤ J.qn)
    (hbetaProt : 0 ≤ J.betaProt)
    (hsourceState :
      BankPaperCanonicalSelectorSourceState
        (W := J.postHeightBridge.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.roundedSourceSelector)
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass) (hdensity : 0 < density)
    (hmassUpper :
      J.qn ≤
        Cmass * (J.postHeightBridge.sampleData.n : Real) /
          J.postHeightBridge.L)
    (hcellDensity : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (J.postHeightBridge.sampleData.n : Real) ≤
        (Fintype.card
          (J.postHeightBridge.sampleData.SampleAt cell) : Real))
    (hcombined :
      centralAnchorDivisor J.postHeightBridge.sampleData.n
            (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct J.postHeightBridge.sampleData.n
          (upperTailLength c J.postHeightBridge.sampleData.n))
    (hcharge :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hsourceMargin :
      sourceMarginFloor ≤ J.Tsource.cellMassMargin)
    (hheadMargin :
      headMarginFloor ≤ J.targetInputs.headMargin)
    (hphysicalEta :
      physicalEtaFloor ≤ J.targetInputs.physicalEta)
    (hpostMargin :
      postMarginFloor ≤ J.postHeightTarget.cellMassMargin)
    (hqTildeFamily :
      J.qTilde = qTilde Bsource.sampleData.n)
    (hmFrozen :
      mFrozen Bsource.sampleData.n =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
          J.postHeightBridge R certificate deltaStar J.betaProt J.alpha)
    (hfinalActiveMass :
      J.qn =
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n)
    (hsourceResidual :
      BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
        (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          J.Tsource deltaStar J.betaProt J.alpha J.beta J.qTilde) :
    ∃ S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
        M Bsource R certificate I deltaStar hdelta J,
      ∃ _Hgap :
          BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
            M Bsource R certificate I E deltaStar mu
              sourceMarginFloor headMarginFloor physicalEtaFloor
              postMarginFloor logY Lambda0 mFrozen qTilde hdelta J S,
        S.Cmass = Cmass ∧ S.density = density := by
  have hpatternE :
      J.postHeightBridge.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime E := by
    calc
      J.postHeightBridge.sampleData.pattern =
          (canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (G J.postHeightBridge.sampleData.n)
            hsep hremaining).pattern :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.pattern)
          hcanonical
      _ = PaperHeadSimplex.pattern P hprime E :=
        canonicalSampleData_pattern
          (PaperHeadSimplex.pattern P hprime E) I
          (G J.postHeightBridge.sampleData.n) hsep hremaining
  have hpattern :
      J.postHeightBridge.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime J.exponent := by
    simpa only [hexponentSync] using hpatternE
  have hsampleGuards :
      J.postHeightBridge.sampleData.guards =
        (G J.postHeightBridge.sampleData.n).guards := by
    calc
      J.postHeightBridge.sampleData.guards =
          (canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (G J.postHeightBridge.sampleData.n)
            hsep hremaining).guards :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.guards)
          hcanonical
      _ = (G J.postHeightBridge.sampleData.n).guards :=
        canonicalSampleData_guards
          (PaperHeadSimplex.pattern P hprime E) I
          (G J.postHeightBridge.sampleData.n) hsep hremaining
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      J.postHeightBridge I hlowerOne hupperTwo
        J.postHeightHlo J.postHeightHhi
  have houtsideGuard :
      ∀ m : J.postHeightBridge.sampleData.Sample,
        J.postHeightBridge.sampleData.value m ∉
          R.roughCanonicalGuardSet certificate deltaStar := by
    intro m
    exact
      structuredSample_value_not_fullGuard_of_agreement
        J.postHeightBridge.sampleData
        (G J.postHeightBridge.sampleData.n)
        R certificate deltaStar hguardAgreement
        hbounds.2 hsampleGuards m
  have hheadSeparated :
      J.postHeightBridge.sampleData.HeadPatternsSeparated :=
    Erdos390.Full.PaperBridgeFit.StructuredSampleData.headPatternsSeparated_of_paperHeadSimplex
      P hprime E hE J.postHeightBridge.sampleData hpatternE
  have hbase :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget :=
    certificate.baseExactificationBank_prod_dvd_prechargedTailTarget
      R hcombined
  have htarget :
      certificate.prechargedTailTarget *
            centralAnchorDivisor J.postHeightBridge.sampleData.n
              (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
              certificate.q =
        centralTailProduct J.postHeightBridge.sampleData.n
          (upperTailLength c J.postHeightBridge.sampleData.n) :=
    certificate.prechargedTailTarget_mul_centralAnchorDivisor
  let S :
      BankPaperCanonicalSectionNinePostHeightSourceInputsAt
        M Bsource R certificate I deltaStar hdelta J := {
    lowerOne := hlowerOne
    upperTwo := hupperTwo
    upperBroad := hupperBroad
    qn_one_le := hqnOne
    hprime := hprime
    hpattern := hpattern
    headPrimes := hhead
    headSeparated := hheadSeparated
    roughDepth := hroughDepth
    outsideGuard := houtsideGuard
    betaProt_nonneg := hbetaProt
    sourceState := hsourceState
    Cmass := Cmass
    density := density
    Cmass_nonneg := hCmass
    density_pos := hdensity
    massUpper := hmassUpper
    cellDensity := hcellDensity
    combined_dvd := hcombined
    base_dvd := hbase
    charge_dvd := hcharge
    target_tail := htarget
  }
  let Hgap :
      BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
        M Bsource R certificate I E deltaStar mu
          sourceMarginFloor headMarginFloor physicalEtaFloor postMarginFloor
          logY Lambda0 mFrozen qTilde hdelta J S := {
    exponent_pos := hE
    exponent_sync := hexponentSync
    sourceMarginFloor_pos := hsourceMarginFloor
    headMarginFloor_pos := hheadMarginFloor
    physicalEtaFloor_pos := hphysicalEtaFloor
    postMarginFloor_pos := hpostMarginFloor
    sourceTarget_margin := hsourceMargin
    headMargin_uniform := hheadMargin
    physicalEta_uniform := hphysicalEta
    postHeightTarget_margin := hpostMargin
    qTilde_family := hqTildeFamily
    mFrozen_family := hmFrozen
    finalActiveMass_family := hfinalActiveMass
    sourceResidual := hsourceResidual
  }
  exact ⟨S, Hgap, rfl, rfl⟩

/-! ## Eventual mechanical wrapper -/

/-- Uniformly assemble the source package after a coherent fresh bridge has
been chosen on the literal fiber of `F`.

The returned constants `Cmass` and `density` are fixed before the mesh and
before the bridge at an eventual index.  The capacity premise is a plain
conjunction, matching the output shape of the combined-charge tail chooser:
the base-bank divisibility and target-tail identity are derived internally.

This theorem deliberately remains universally quantified over `J` and over
its target/residual facts. -/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual
    (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sign, 1 ≤ I.lower sign)
    (hupperStrict : ∀ sign, I.upper sign < 2)
    {c : Real} (depth W K0 Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    {deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real}
    (hc : 0 < c) (hbetaAct : 0 < betaAct) (hmu : 0 < mu)
    (hbetaProt : 0 ≤ betaProt)
    (hsourceMarginFloor : 0 < sourceMarginFloor)
    (hheadMarginFloor : 0 < headMarginFloor)
    (hphysicalEtaFloor : 0 < physicalEtaFloor)
    (hpostMarginFloor : 0 < postMarginFloor)
    (hhead : primesUpTo W ⊆ P)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar))) :
    ∃ Cmass density : Real,
      0 < Cmass ∧
      0 < density ∧
      ∀ {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta),
        ∀ᶠ n : Nat in atTop,
          ∀ (hdelta : 0 < delta)
          (Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M)),
          Bsource.sampleData.n = n →
          Bsource.sampleData.W = W →
          ∀ (hnTail : Ntail ≤ Bsource.sampleData.n),
            let R := F.realization Bsource.sampleData.n hnTail
            let certificate := F.certificate Bsource.sampleData.n hnTail
            ∀ (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                (K0 := K0) M Bsource R certificate I deltaStar hdelta),
              J.exponent = E →
              J.betaProt = betaProt →
              J.betaAct = betaAct →
              (∀
                (hsep :
                  physicalBound (I.upper .minus)
                      J.postHeightBridge.sampleData.n <
                    physicalBound (I.lower .plus)
                      J.postHeightBridge.sampleData.n)
                (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
                  (rawCell (PaperHeadSimplex.pattern P hprime E) I
                      J.postHeightBridge.sampleData.n cell \
                    (roughCanonicalBridgeRelevantLedgerFamily depth
                      J.postHeightBridge.sampleData.n).guards).Nonempty),
                J.postHeightBridge.sampleData =
                    canonicalSampleData
                      (W := J.postHeightBridge.sampleData.W)
                      (PaperHeadSimplex.pattern P hprime E) I
                      (roughCanonicalBridgeRelevantLedgerFamily depth
                        J.postHeightBridge.sampleData.n)
                      hsep hremaining →
                J.qTilde =
                    bankPaperCanonicalGuardedSmoothBaseMass
                      R certificate deltaStar
                        J.postHeightBridge.sampleData.W
                        (K0 + 1) J.betaAct →
                sourceMarginFloor ≤ J.Tsource.cellMassMargin →
                headMarginFloor ≤ J.targetInputs.headMargin →
                physicalEtaFloor ≤ J.targetInputs.physicalEta →
                postMarginFloor ≤ J.postHeightTarget.cellMassMargin →
                mFrozen Bsource.sampleData.n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass
                      (K := K0 + 1) J.postHeightBridge R certificate
                      deltaStar J.betaProt J.alpha →
                J.qn =
                    bankPaperCanonicalSmoothFinalActiveMassFamily
                      mu logY Lambda0 mFrozen
                        (F.extendedGuardedSmoothBaseMass
                          W (K0 + 1) betaAct deltaStar)
                        Bsource.sampleData.n →
                BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
                    (K := K0 + 1) J.postHeightBridge R certificate
                      (R.paperFixedExceptionalFactors deltaStar)
                      J.Tsource deltaStar J.betaProt J.alpha J.beta
                        J.qTilde →
                (centralAnchorDivisor J.postHeightBridge.sampleData.n
                        (centralAnchorCutoff depth
                          J.postHeightBridge.sampleData.n)
                        certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct J.postHeightBridge.sampleData.n
                      (upperTailLength c
                        J.postHeightBridge.sampleData.n)) ∧
                  R.selectorTailCharge
                        (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                ∃ S :
                    BankPaperCanonicalSectionNinePostHeightSourceInputsAt
                      M Bsource R certificate I deltaStar hdelta J,
                  ∃ _Hgap :
                      BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                        M Bsource R certificate I E deltaStar mu
                          sourceMarginFloor headMarginFloor physicalEtaFloor
                          postMarginFloor logY Lambda0 mFrozen
                          (F.extendedGuardedSmoothBaseMass
                            W (K0 + 1) betaAct deltaStar)
                          hdelta J S,
                    S.Cmass = Cmass ∧ S.density = density) := by
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass W (K0 + 1) betaAct deltaStar
  have Hledger' :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde] using Hledger
  have Hraw :
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct) =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalRawSmoothBaseMass_isBigO
      W (K0 + 1) c betaAct
  have HqTilde : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) (K0 + 1) betaAct)
      qTilde Hraw Hledger'.1
  have Hq0 :
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde HqTilde
  have Hd :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        (fun n => secondOrderScale n / L n) :=
    bankPaperCanonicalSectionEight_d_isBigO
      W (K0 + 1) c betaAct hmu logY Lambda0 mFrozen qTilde Hledger'
  have HdScale :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        secondOrderScale :=
    Hd.trans secondOrderScale_div_L_isLittleO_secondOrderScale.isBigO
  have Hfinal :
      bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        secondOrderScale :=
    (Hq0.sub HdScale).congr_left fun n => by
      rfl
  obtain ⟨Cmass, hCmass, hmassBound⟩ :=
    (isBigO_iff').mp Hfinal
  let density : Real :=
    bankPaperCanonicalGuardedCellDensityFloor
      (PaperHeadSimplex.pattern P hprime E) I
  have hdensity : 0 < density := by
    simpa only [density] using
      bankPaperCanonicalGuardedCellDensityFloor_pos
        (PaperHeadSimplex.pattern P hprime E) I
  have hupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I (K0 + 1) hc hupperStrict
  have hroughDepth :=
    eventually_mul_upperTailLength_le_self (K0 + 1) hc
  have hqnOne :=
    eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
      W (K0 + 1) hc hbetaAct hmu
        logY Lambda0 mFrozen qTilde Hledger'
  have hguardAgreement :=
    eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
      (c := c) depth deltaStar
  have hrawDensity :=
    eventually_guarded_rawCell_density
      (PaperHeadSimplex.pattern P hprime E) I
      2 0 (roughCanonicalBridgeRelevantLedgerFamily depth)
  refine ⟨Cmass, density, hCmass, hdensity, ?_⟩
  intro delta eta M
  have hsource :=
    eventually_bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_residualInputs
      (Band := BankPaperCanonicalExponentBand M)
      (deltaStar := deltaStar)
      hprime E hE I hlowerOne hupperStrict
      2 0 (roughCanonicalBridgeRelevantLedgerFamily depth)
      depth W (K0 + 1) hc hbetaAct hsourceMarginFloor hbetaProt
      hhead mFrozen qTilde
      (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde)
      Hledger'
  filter_upwards [
      hsource, hupperBroad, hroughDepth, hqnOne,
      hguardAgreement, hrawDensity, hmassBound,
      eventually_secondOrderScale_pos]
      with n hsourceN hupperBroadN hroughDepthN hqnOneN
        hguardAgreementN hrawDensityN hmassBoundN hscaleN
  intro hdelta Bsource hBn hBW hnTail
  subst n
  let R := F.realization Bsource.sampleData.n hnTail
  let certificate := F.certificate Bsource.sampleData.n hnTail
  dsimp only
  intro J hexponentSync hbetaProtSync hbetaActSync
    hsep hremaining hcanonical hqTildeActual
    hsourceMargin hheadMargin hphysicalEta hpostMargin
    hmFrozen hfinalActiveMass hsourceResidual hcapacity
  have hBWpost :
      J.postHeightBridge.sampleData.W = W := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hBW
  have hqTildeFiber :
      qTilde Bsource.sampleData.n =
        bankPaperCanonicalGuardedSmoothBaseMass
          R certificate deltaStar W (K0 + 1) betaAct := by
    simp only [
      qTilde,
      BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
      dif_pos hnTail, R, certificate]
  have hqTildeFamily :
      J.qTilde = qTilde Bsource.sampleData.n := by
    calc
      J.qTilde =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar
              J.postHeightBridge.sampleData.W (K0 + 1) J.betaAct :=
        hqTildeActual
      _ =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar W (K0 + 1) betaAct := by
        rw [hBWpost, hbetaActSync]
      _ = qTilde Bsource.sampleData.n :=
        hqTildeFiber.symm
  have hupperTwo : ∀ sign, I.upper sign ≤ 2 :=
    fun sign => (hupperStrict sign).le
  have hupperBroadPost : ∀ sign,
      physicalBound (I.upper sign) J.postHeightBridge.sampleData.n ≤
        2 * J.postHeightBridge.sampleData.n -
          (K0 + 1) *
            upperTailLength c J.postHeightBridge.sampleData.n := by
    intro sign
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hupperBroadN sign
  have hroughDepthPost :
      (K0 + 1) *
          upperTailLength c J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hroughDepthN
  have hqnOnePost : 1 ≤ J.qn := by
    rw [hfinalActiveMass]
    exact hqnOneN
  have hmassFamily :
      bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n ≤
        Cmass * secondOrderScale Bsource.sampleData.n := by
    have habs :
        |bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n| ≤
          Cmass * secondOrderScale Bsource.sampleData.n := by
      simpa only [Real.norm_eq_abs, abs_of_pos hscaleN] using
        hmassBoundN
    exact
      (le_abs_self
        (bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n)).trans habs
  have hmassUpper :
      J.qn ≤
        Cmass * (J.postHeightBridge.sampleData.n : Real) /
          J.postHeightBridge.L := by
    calc
      J.qn =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n :=
        hfinalActiveMass
      _ ≤ Cmass * secondOrderScale Bsource.sampleData.n :=
        hmassFamily
      _ =
          Cmass * (J.postHeightBridge.sampleData.n : Real) /
            J.postHeightBridge.L := by
        simp only [
          secondOrderScale, BridgeData.L,
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        ring
  have hcellDensity : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (J.postHeightBridge.sampleData.n : Real) ≤
        (Fintype.card
          (J.postHeightBridge.sampleData.SampleAt cell) : Real) := by
    intro cell
    have hcellFinset :
        J.postHeightBridge.sampleData.cellFinset cell =
          rawCell (PaperHeadSimplex.pattern P hprime E) I
              Bsource.sampleData.n cell \
            (roughCanonicalBridgeRelevantLedgerFamily
              depth Bsource.sampleData.n).guards := by
      calc
        J.postHeightBridge.sampleData.cellFinset cell =
            (canonicalSampleData
              (W := J.postHeightBridge.sampleData.W)
              (PaperHeadSimplex.pattern P hprime E) I
              (roughCanonicalBridgeRelevantLedgerFamily
                depth J.postHeightBridge.sampleData.n)
              hsep hremaining).cellFinset cell :=
          congrArg
            (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
              D.cellFinset cell)
            hcanonical
        _ =
            rawCell (PaperHeadSimplex.pattern P hprime E) I
                J.postHeightBridge.sampleData.n cell \
              (roughCanonicalBridgeRelevantLedgerFamily
                depth J.postHeightBridge.sampleData.n).guards :=
          canonicalSampleData_cellFinset
            (PaperHeadSimplex.pattern P hprime E) I
            (roughCanonicalBridgeRelevantLedgerFamily
              depth J.postHeightBridge.sampleData.n)
            hsep hremaining cell
        _ =
            rawCell (PaperHeadSimplex.pattern P hprime E) I
                Bsource.sampleData.n cell \
              (roughCanonicalBridgeRelevantLedgerFamily
                depth Bsource.sampleData.n).guards := by
          rfl
    have hcardEq :
        (Fintype.card
            (J.postHeightBridge.sampleData.SampleAt cell) : Real) =
          ((rawCell (PaperHeadSimplex.pattern P hprime E) I
              Bsource.sampleData.n cell \
            (roughCanonicalBridgeRelevantLedgerFamily
              depth Bsource.sampleData.n).guards).card : Real) := by
      rw [Fintype.card_coe, hcellFinset]
    have hdensityLe :
        density ≤
          paperCellDensity
              ((PaperHeadSimplex.pattern P hprime E) cell.1)
              (I.lower cell.2) (I.upper cell.2) / 4 := by
      simpa only [density] using
        bankPaperCanonicalGuardedCellDensityFloor_le
          (PaperHeadSimplex.pattern P hprime E) I cell
    calc
      density * (J.postHeightBridge.sampleData.n : Real) =
          density * (Bsource.sampleData.n : Real) := by
        rfl
      _ ≤
          (paperCellDensity
              ((PaperHeadSimplex.pattern P hprime E) cell.1)
              (I.lower cell.2) (I.upper cell.2) / 4) *
            (Bsource.sampleData.n : Real) :=
        mul_le_mul_of_nonneg_right hdensityLe (Nat.cast_nonneg _)
      _ =
          paperCellDensity
              ((PaperHeadSimplex.pattern P hprime E) cell.1)
              (I.lower cell.2) (I.upper cell.2) *
            (Bsource.sampleData.n : Real) / 4 := by
        ring
      _ ≤
          ((rawCell (PaperHeadSimplex.pattern P hprime E) I
              Bsource.sampleData.n cell \
            (roughCanonicalBridgeRelevantLedgerFamily
              depth Bsource.sampleData.n).guards).card : Real) :=
        hrawDensityN cell
      _ =
          (Fintype.card
            (J.postHeightBridge.sampleData.SampleAt cell) : Real) :=
        hcardEq.symm
  have hguardAgreementPost :
      BankPaperCanonicalBridgeGuardAgreement
        (roughCanonicalBridgeRelevantLedgerFamily
          depth J.postHeightBridge.sampleData.n)
        R certificate deltaStar := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hguardAgreementN R certificate
  have hmFrozenForSource :
      mFrozen Bsource.sampleData.n =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
          J.postHeightBridge R certificate deltaStar betaProt J.alpha := by
    simpa only [hbetaProtSync] using hmFrozen
  have hresidualForSource :
      BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
        (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          J.Tsource deltaStar betaProt J.alpha J.beta
            (qTilde Bsource.sampleData.n) := by
    simpa only [hbetaProtSync, hqTildeFamily] using hsourceResidual
  have hsourceStateRaw :=
    hsourceN J.postHeightBridge rfl hBWpost
      hsep hremaining hcanonical R certificate hguardAgreementPost
      J.Tsource hsourceMargin
      (R.paperFixedExceptionalFactors deltaStar)
      J.alpha J.beta hmFrozenForSource hresidualForSource
  have hsourceState :
      BankPaperCanonicalSelectorSourceState
        (W := J.postHeightBridge.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.roundedSourceSelector := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector,
      hbetaProtSync, hqTildeFamily] using hsourceStateRaw
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_canonical
      (M := M) (hprime := hprime) (E := E) (hE := hE)
      (Bsource := Bsource) (R := R) (certificate := certificate)
      (I := I) (hlowerOne := hlowerOne) (hupperTwo := hupperTwo)
      (Cprom := 2) (Cbank := 0)
      (G := roughCanonicalBridgeRelevantLedgerFamily depth)
      (deltaStar := deltaStar) (mu := mu)
      (sourceMarginFloor := sourceMarginFloor)
      (headMarginFloor := headMarginFloor)
      (physicalEtaFloor := physicalEtaFloor)
      (postMarginFloor := postMarginFloor)
      (logY := logY) (Lambda0 := Lambda0)
      (mFrozen := mFrozen) (qTilde := qTilde)
      (hsourceMarginFloor := hsourceMarginFloor)
      (hheadMarginFloor := hheadMarginFloor)
      (hphysicalEtaFloor := hphysicalEtaFloor)
      (hpostMarginFloor := hpostMarginFloor)
      (hdelta := hdelta) (J := J)
      (hexponentSync := hexponentSync) (hhead := by
        simpa only [hBWpost] using hhead)
      (hsep := hsep) (hremaining := hremaining)
      (hcanonical := hcanonical)
      (hguardAgreement := hguardAgreementPost)
      (hupperBroad := hupperBroadPost)
      (hroughDepth := hroughDepthPost)
      (hqnOne := hqnOnePost)
      (hbetaProt := by
        simpa only [hbetaProtSync] using hbetaProt)
      (hsourceState := hsourceState)
      (Cmass := Cmass) (density := density)
      (hCmass := hCmass.le) (hdensity := hdensity)
      (hmassUpper := hmassUpper) (hcellDensity := hcellDensity)
      (hcombined := hcapacity.1) (hcharge := hcapacity.2)
      (hsourceMargin := hsourceMargin)
      (hheadMargin := hheadMargin)
      (hphysicalEta := hphysicalEta)
      (hpostMargin := hpostMargin)
      (hqTildeFamily := hqTildeFamily)
      (hmFrozen := hmFrozen)
      (hfinalActiveMass := by
        simpa only [qTilde] using hfinalActiveMass)
      (hsourceResidual := hsourceResidual)

end BankPaperRealization

end

end Erdos390.WholePaper
