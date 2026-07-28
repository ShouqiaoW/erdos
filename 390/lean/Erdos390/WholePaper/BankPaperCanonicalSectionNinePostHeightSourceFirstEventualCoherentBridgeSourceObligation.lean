import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstRichSourceProducer
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerPostBridgeAssembly
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceInputAssemblyConnector

/-!
# Source-first construction of the eventual coherent post-height bridge

This module combines the genuine rich source family, the exact Section 8
ledger, and the post-ledger fresh bridge.  It discharges the existing honest
family-level coherent-bridge/source obligation without assuming a bridge,
source package, primitive-gap record, or conclusion-bearing contract.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 3600000 in
/-- The source-first construction produces one total fresh bridge family and
the exact eventual coherent-bridge/source obligation used by the downstream
Section 9 reductions. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstEventualCoherentBridgeSourceObligation
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    (hW : 0 < W)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 ≤ W)
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hterminal :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n)) :
    let P := primesUpTo W
    let hprime :=
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W
    let I :=
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
    let G : ∀ n, Ledger n 2 0 :=
      roughCanonicalBridgeRelevantLedgerFamily depth
    ∃ E : Nat,
    ∃ sourceCellMargin postMargin Cmass density : Real,
    ∃ logY Lambda0 mFrozen : Nat → Real,
      let Patterns := PaperHeadSimplex.pattern P hprime E
      let qTilde :=
        F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar
      let physicalEtaFloor :=
        bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2
      let postCellMargin :=
        postMargin *
          (physicalEtaFloor /
            PhysicalInterpolationTarget.physicalSpan I)
      ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
          (BankPaperCanonicalExponentBand M),
        0 < E ∧
        0 < sourceCellMargin ∧
        0 < postMargin ∧
        0 < physicalEtaFloor ∧
        0 < postCellMargin ∧
        0 < Cmass ∧
        0 < density ∧
        logY = F.extendedPrechargedTailLogTarget ∧
        BankPaperCanonicalSectionEightAnalyticLedger
          (fun n =>
            bankPaperCanonicalRawSmoothBaseMass W n
              (upperTailLength c n) (K0 + 1) betaAct)
          qTilde
          (bankPaperCanonicalSmoothA0Family
            logY Lambda0 mFrozen qTilde) ∧
        BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
          P Patterns I 2 0 G (c := c) depth W K0 E N F
          deltaStar betaProt betaAct
          bankPaperCanonicalSectionNinePostHeightPhysicalMu
          sourceCellMargin postMargin physicalEtaFloor postCellMargin
          Cmass density logY Lambda0 mFrozen qTilde M hdelta B := by
  let P := primesUpTo W
  have hprime : ∀ p ∈ P, p.Prime := by
    simpa only [P] using
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  let G : ∀ n, Ledger n 2 0 :=
    roughCanonicalBridgeRelevantLedgerFamily depth
  have hcPos : 0 < c :=
    (show (0 : Real) < C0 by norm_num [C0]).trans hc
  have hdeltaStarUpper : deltaStar < 1 :=
    hdeltaStar.2.1.trans (by norm_num)
  have hw : 0 < delta + eta :=
    add_pos hdelta (M.ratio_pos.trans_le M.ratio_le_eta)
  obtain
      ⟨cSource, cUpper, E, sourceCellMargin,
        hcSource, hcUpper, hE, hsourceCellMarginPos,
        hElarge, Hmass, sourceGeom, source,
        Hprojection, Hsource, Hready, Hgeom⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceFamilies
      M hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge
        hprefix hdelta F hterminal
  have HsourceLower :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n :=
    Hmass.mono fun _ hn => hn.1
  obtain
      ⟨logY, Lambda0, mFrozen, hlogY, Hledger, Hsync,
        Cpost, postMargin, hCpost, hpostMargin,
        hpostMarginPos, HJ⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerPostBridgeAssembly
      M hc hdeltaStar.1 hdeltaStarUpper hW hbetaAct hdelta F
        source Hsource cSource E sourceCellMargin hcSource hE
        hElarge HsourceLower Hready
  let Patterns := PaperHeadSimplex.pattern P hprime E
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let physicalEtaFloor : Real :=
    bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2
  let postCellMargin : Real :=
    postMargin *
      (physicalEtaFloor /
        PhysicalInterpolationTarget.physicalSpan I)
  have hphysicalEtaFloorPos : 0 < physicalEtaFloor := by
    exact div_pos
      bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
      (by norm_num)
  have hpostCellMarginPos : 0 < postCellMargin := by
    exact mul_pos hpostMarginPos
      (div_pos hphysicalEtaFloorPos
        (PhysicalInterpolationTarget.physicalSpan_pos (I := I)))
  have hlowerOne : ∀ sign, 1 ≤ I.lower sign := by
    intro sign
    simpa only [I] using
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one sign
  have hupperStrict : ∀ sign, I.upper sign < 2 := by
    intro sign
    cases sign <;>
      norm_num [I,
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals]
  have hupperTwo : ∀ sign, I.upper sign ≤ 2 :=
    fun sign => (hupperStrict sign).le
  have hhead : primesUpTo W ⊆ P := by
    intro p hp
    simpa only [P] using hp
  obtain ⟨Cmass, density, hCmass, hdensity, Hassemble⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual
      P hprime E hE I hlowerOne hupperStrict depth W K0 N F
      hcPos hbetaAct
      bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      hbetaProt hsourceCellMarginPos hpostMarginPos
      hphysicalEtaFloorPos hpostCellMarginPos hhead
      logY Lambda0 mFrozen Hledger
  have Hresidual :=
    eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
      (Band := BankPaperCanonicalExponentBand M)
      Patterns I 2 0 G depth W K0
      hcPos hdeltaStar.1 hbetaProt hbetaAct
      (by norm_num : (0 : Real) ≤ 0) hbetaProt
      hbetaUpper hKlarge hprefix
  have HupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I (K0 + 1) hcPos hupperStrict
  have HroughDepth :=
    eventually_mul_upperTailLength_le_self (K0 + 1) hcPos
  have Hpost :
      ∀ᶠ n : Nat in atTop,
        ∃ Bpost : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
        ∃ Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
        ∃ hnTail : N ≤ Bsource.sampleData.n,
          let R := F.realization Bsource.sampleData.n hnTail
          let certificate := F.certificate Bsource.sampleData.n hnTail
          ∃ J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
              (K0 := K0) M Bsource R certificate I deltaStar hdelta,
          ∃ S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
              M Bsource R certificate I deltaStar hdelta J,
          ∃ Hgap : BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
              M Bsource R certificate I E deltaStar
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                sourceCellMargin postMargin physicalEtaFloor postCellMargin
                logY Lambda0 mFrozen qTilde hdelta J S,
          ∃ hsep :
              physicalBound (I.upper .minus)
                  J.postHeightBridge.sampleData.n <
                physicalBound (I.lower .plus)
                  J.postHeightBridge.sampleData.n,
          ∃ hremaining :
              ∀ cell : Cell (PaperHeadSimplex.Tag P),
                (rawCell Patterns I
                    J.postHeightBridge.sampleData.n cell \
                  (G J.postHeightBridge.sampleData.n).guards).Nonempty,
            Bpost = J.postHeightBridge ∧
            Bsource.sampleData.n = n ∧
            Bsource.sampleData.W = W ∧
            J.betaProt = betaProt ∧
            J.betaAct = betaAct ∧
            J.postHeightBridge.sampleData =
              canonicalSampleData
                (W := J.postHeightBridge.sampleData.W)
                Patterns I (G J.postHeightBridge.sampleData.n)
                hsep hremaining ∧
            J.qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass
                R certificate deltaStar
                J.postHeightBridge.sampleData.W
                (K0 + 1) J.betaAct ∧
            S.Cmass = Cmass ∧
            S.density = density := by
    filter_upwards [
        eventually_ge_atTop N, Hsource, Hsync, Hgeom, HJ,
        Hassemble M, Hresidual, HupperBroad, HroughDepth]
      with n hn hsourceN hsyncN hgeomN hJN
        hassembleN hresidualN hupperBroadN hroughDepthN
    generalize hZ : sourceGeom n hn = Z
    change
      (Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
        Σ' _hnTail : N ≤ D.n,
        Σ' _hnD : 1 < D.n,
        Σ' _hWD : D.W ≠ 0,
        Σ' _S : ScaleSeparation M D.n D.W,
        Σ' _hlo : (∀ sigma, D.lo sigma =
            physicalBound (I.lower sigma) D.n),
        Σ' _hhi : (∀ sigma, D.hi sigma =
            physicalBound (I.upper sigma) D.n),
          HeadSimplexReserve P) at Z
    rcases Z with
      ⟨D, hnTail, hnD, hWD, Sgeom, hlo, hhi, RheadSource⟩
    let KphysicalSource :=
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D I hlo hhi RheadSource KphysicalSource
        hdelta hnD hWD Sgeom hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D I hlo hhi RheadSource KphysicalSource
        hdelta hnD hWD Sgeom hw
    let R := F.realization D.n hnTail
    let certificate := F.certificate D.n hnTail
    have hsrc :
        source n hn =
          ⟨Bsource, ⟨⟨R, certificate⟩, Tsource⟩⟩ := by
      rw [Hprojection n hn, hZ]
      rfl
    have hs := hsourceN hn
    have hsync := hsyncN hn
    have hg := hgeomN hn
    have hj := hJN hn
    rw [hsrc] at hs hsync hg hj
    dsimp only at hs hsync hg hj
    rcases hs with
      ⟨hBn, hBW, hqSourceActual, hqOne,
        hheadSeparatedSource, hactiveSmooth, halpha, hbetaBox,
        hsourceResidualSource, hprecharged⟩
    rcases hsync with
      ⟨hmFrozenSync, hlogYSync, hLambda0Sync⟩
    rcases hg with
      ⟨hsep, hremaining, hcanonical, hguardAgreement⟩
    rcases hj with
      ⟨Rhead, Kphysical, J, hJTsource, hJsourceMargin,
        hRheadExponent, hRheadTarget, hJTpaper, hJqRhead,
        hJqFamily, hJexponent, hJd, hJbetaProt, hJbetaAct,
        hJq0, hJA0, hJqn, hJheadMargin, hJphysicalEta⟩
    have hBpostN : J.postHeightBridge.sampleData.n = n := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using hBn
    have hBpostW : J.postHeightBridge.sampleData.W = W := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using hBW
    have hsepJ :
        physicalBound (I.upper .minus)
            J.postHeightBridge.sampleData.n <
          physicalBound (I.lower .plus)
            J.postHeightBridge.sampleData.n := by
      simpa only [hBpostN] using hsep
    have hremainingJ :
        ∀ cell : Cell (PaperHeadSimplex.Tag P),
          (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
            (G J.postHeightBridge.sampleData.n).guards).Nonempty := by
      intro cell
      rw [hBpostN]
      simpa only [Patterns, I, G, P] using hremaining cell
    have hcanonicalJ :
        J.postHeightBridge.sampleData =
          canonicalSampleData
            (W := J.postHeightBridge.sampleData.W)
            Patterns I (G J.postHeightBridge.sampleData.n)
            hsepJ hremainingJ := by
      calc
        J.postHeightBridge.sampleData = Bsource.sampleData :=
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData
            J
        _ =
            canonicalSampleData
              (W := W) Patterns I (G n) hsep hremaining := by
          simpa only [Patterns, I, G, P] using hcanonical
        _ =
            canonicalSampleData
              (W := J.postHeightBridge.sampleData.W)
              Patterns I (G J.postHeightBridge.sampleData.n)
              hsepJ hremainingJ := by
          cases hBpostN
          rw [hBpostW]
    have hqActualJ :
        J.qTilde =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar
            J.postHeightBridge.sampleData.W
            (K0 + 1) J.betaAct := by
      calc
        J.qTilde =
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n :=
          hJqFamily
        _ =
            bankPaperCanonicalGuardedSmoothBaseMass
              R certificate deltaStar Bsource.sampleData.W
              (K0 + 1) betaAct :=
          hqSourceActual
        _ =
            bankPaperCanonicalGuardedSmoothBaseMass
              R certificate deltaStar
              J.postHeightBridge.sampleData.W
              (K0 + 1) J.betaAct := by
          rw [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
            hJbetaAct]
    have hpatternJ :
        J.postHeightBridge.sampleData.pattern =
          PaperHeadSimplex.pattern P hprime Rhead.exponent := by
      calc
        J.postHeightBridge.sampleData.pattern =
            (canonicalSampleData
              (W := J.postHeightBridge.sampleData.W)
              Patterns I (G J.postHeightBridge.sampleData.n)
              hsepJ hremainingJ).pattern :=
          congrArg
            (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
              D.pattern)
            hcanonicalJ
        _ = Patterns :=
          canonicalSampleData_pattern Patterns I
            (G J.postHeightBridge.sampleData.n) hsepJ hremainingJ
        _ = PaperHeadSimplex.pattern P hprime Rhead.exponent := by
          rw [hRheadExponent]
    have hheadSubset :
        primesUpTo J.postHeightBridge.sampleData.W ⊆ P := by
      intro p hp
      simpa only [hBpostW, P] using hp
    have hheadSeparatedJ :
        J.postHeightBridge.sampleData.HeadPatternsSeparated := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using hheadSeparatedSource
    have hbounds :=
      bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
        J.postHeightBridge I hlowerOne hupperTwo
        J.postHeightHlo J.postHeightHhi
    have hguardAgreementJ :
        BankPaperCanonicalBridgeGuardAgreement
          (G J.postHeightBridge.sampleData.n) R certificate deltaStar := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using hguardAgreement
    have hsampleGuardsJ :
        J.postHeightBridge.sampleData.guards =
          (G J.postHeightBridge.sampleData.n).guards := by
      calc
        J.postHeightBridge.sampleData.guards =
            (canonicalSampleData
              (W := J.postHeightBridge.sampleData.W)
              Patterns I (G J.postHeightBridge.sampleData.n)
              hsepJ hremainingJ).guards :=
          congrArg
            (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
              D.guards)
            hcanonicalJ
        _ = (G J.postHeightBridge.sampleData.n).guards :=
          canonicalSampleData_guards Patterns I
            (G J.postHeightBridge.sampleData.n) hsepJ hremainingJ
    have hnotGuard :
        ∀ m : J.postHeightBridge.sampleData.Sample,
          J.postHeightBridge.sampleData.value m ∉
            R.roughCanonicalGuardSet certificate deltaStar := by
      intro m
      exact
        structuredSample_value_not_fullGuard_of_agreement
          J.postHeightBridge.sampleData
          (G J.postHeightBridge.sampleData.n)
          R certificate deltaStar hguardAgreementJ
          hbounds.2 hsampleGuardsJ m
    have htargetCompatibility :
        ∀ p : {p : Nat // p ∈ P},
          p.1 ≤ J.postHeightBridge.sampleData.W →
            Rhead.target p =
              ((certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar)).factorization
                  p.1 : Real) := by
      intro p _hp
      exact hRheadTarget p
    have hchargeDvd :
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget := by
      have ht := hterminal D.n hnTail
      simpa only [R, certificate] using ht.2.2.1
    have hupperBroadJ :
        ∀ sign,
          physicalBound (I.upper sign)
              J.postHeightBridge.sampleData.n ≤
            2 * J.postHeightBridge.sampleData.n -
              (K0 + 1) *
                upperTailLength c J.postHeightBridge.sampleData.n := by
      intro sign
      simpa only [hBpostN] using hupperBroadN sign
    have hroughDepthJ :
        (K0 + 1) *
            upperTailLength c J.postHeightBridge.sampleData.n ≤
          J.postHeightBridge.sampleData.n := by
      simpa only [hBpostN] using hroughDepthN
    have hqActualResidual :
        J.qTilde =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar J.postHeightBridge.sampleData.W
            (K0 + 1) betaAct := by
      simpa only [hJbetaAct] using hqActualJ
    have hsourceResidualRaw :=
      hresidualN J.postHeightBridge hBpostN hBpostW
        hsepJ hremainingJ hcanonicalJ
        R certificate J.Tsource J.qTilde hqActualResidual
        hprime Rhead Kphysical J.postHeightHlo J.postHeightHhi
        hJTpaper hJqRhead hpatternJ hheadSubset hheadSeparatedJ
        hlowerOne hupperTwo hupperBroadJ hroughDepthJ
        hnotGuard htargetCompatibility hchargeDvd
    have hsourceResidualJ :
        BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
          (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          J.Tsource deltaStar J.betaProt J.alpha J.beta J.qTilde := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
        bankPaperCanonicalPostHfitBalancedAlpha,
        BridgeData.L,
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
        hJbetaProt, hJbetaAct] using hsourceResidualRaw
    have hheadMarginLe :
        postMargin ≤ J.targetInputs.headMargin := by
      rw [hJheadMargin]
    have hphysicalEtaLe :
        physicalEtaFloor ≤ J.targetInputs.physicalEta := by
      rw [hJphysicalEta]
    have hpostTargetMargin :
        postCellMargin ≤ J.postHeightTarget.cellMassMargin := by
      change
        postCellMargin ≤
          (bankPaperCanonicalSectionNinePostHeightTarget
            J.postHeightBridge I J.postHeightHlo J.postHeightHhi
            J.postHeightTargetInputs).cellMassMargin
      rw [
        bankPaperCanonicalSectionNinePostHeightTarget_cellMassMargin,
        show J.postHeightTargetInputs.headMargin =
            J.targetInputs.headMargin by rfl,
        show J.postHeightTargetInputs.physicalEta =
            J.targetInputs.physicalEta by rfl,
        hJheadMargin, hJphysicalEta]
    have hmFrozenJ :
        mFrozen Bsource.sampleData.n =
          bankPaperCanonicalTopFrozenSmoothFrozenMass
            (K := K0 + 1) J.postHeightBridge R certificate
            deltaStar J.betaProt J.alpha := by
      simpa only [
        hBn, hJbetaProt, hJbetaAct,
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
        bankPaperCanonicalPostHfitBalancedAlpha,
        bankPaperCanonicalTopFrozenSmoothFrozenMass,
        BridgeData.L,
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using hmFrozenSync
    have hJqnFamily :
        J.qn =
          bankPaperCanonicalSmoothFinalActiveMassFamily
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
      simpa only [qTilde, hBn] using hJqn
    have hcapacity :
        (centralAnchorDivisor J.postHeightBridge.sampleData.n
                (centralAnchorCutoff depth
                  J.postHeightBridge.sampleData.n)
                certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct J.postHeightBridge.sampleData.n
              (upperTailLength c J.postHeightBridge.sampleData.n)) ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget := by
      have ht := hterminal D.n hnTail
      dsimp only at ht
      constructor
      · simpa only [
          R, certificate,
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
          Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData]
          using ht.1
      · simpa only [R, certificate] using ht.2.2.1
    obtain ⟨Ssource, Hgap, hSCmass, hSdensity⟩ :=
      hassembleN hdelta Bsource hBn hBW hnTail
        J hJexponent hJbetaProt hJbetaAct
        hsepJ hremainingJ hcanonicalJ hqActualJ
        hJsourceMargin hheadMarginLe hphysicalEtaLe hpostTargetMargin
        hmFrozenJ hJqnFamily hsourceResidualJ hcapacity
    exact
      ⟨J.postHeightBridge, Bsource, hnTail, J, Ssource, Hgap,
        hsepJ, hremainingJ, rfl, hBn, hBW,
        hJbetaProt, hJbetaAct, hcanonicalJ, hqActualJ,
        hSCmass, hSdensity⟩
  obtain ⟨Npost, hNpost⟩ := Filter.eventually_atTop.mp Hpost
  choose Bpost hBpost using hNpost
  let fallback : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) :=
    Bpost Npost le_rfl
  let B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) := fun n =>
    if h : Npost ≤ n then Bpost n h else fallback
  refine
    ⟨E, sourceCellMargin, postMargin, Cmass, density,
      logY, Lambda0, mFrozen, ?_⟩
  dsimp only
  refine
    ⟨B, hE, hsourceCellMarginPos, hpostMarginPos,
      hphysicalEtaFloorPos, hpostCellMarginPos,
      hCmass, hdensity, hlogY, ?_, ?_⟩
  · simpa only [qTilde] using Hledger
  · filter_upwards [eventually_ge_atTop Npost] with n hnLarge
    rcases hBpost n hnLarge with
      ⟨Bsource, hnTail, J, Ssource, Hgap, hsep, hremaining,
        hBpostEq, hBn, hBW, hJbetaProt, hJbetaAct,
        hcanonical, hqActual, hSCmass, hSdensity⟩
    refine
      ⟨Bsource, hnTail, J, Ssource, Hgap, hsep, hremaining,
        ?_, hBn, hBW, hJbetaProt, hJbetaAct,
        hcanonical, hqActual, hSCmass, hSdensity⟩
    calc
      B n = Bpost n hnLarge := by
        simp only [B, dif_pos hnLarge]
      _ = J.postHeightBridge := hBpostEq

end BankPaperRealization

end

end Erdos390.WholePaper
