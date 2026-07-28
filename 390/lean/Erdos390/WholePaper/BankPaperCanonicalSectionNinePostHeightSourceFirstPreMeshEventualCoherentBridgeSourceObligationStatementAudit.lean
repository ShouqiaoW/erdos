import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshEventualCoherentBridgeSourceObligation

/-!
# Expanded statement audit: pre-mesh coherent bridge/source obligation

This audit repeats the complete public theorem assignment literally.  The
exponent, both cell margins, the source constants, and the three scalar
families, together with their positivity and analytic-ledger facts, are all
chosen before the universally quantified final regular relative mesh.

For each final mesh, the concluding
`BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation`
is unfolded completely: the total bridge family and its eventual source
bridge, tail proof, post-height inputs, source inputs, primitive gaps,
canonical sample identity, guarded smooth mass identity, and fixed source
constants are all displayed.
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
example
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
        ∀ {delta eta : Real}
            (M : RegularRelativeMesh.Mesh delta eta)
            (hdelta : 0 < delta),
          ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
              (BankPaperCanonicalExponentBand M),
            ∀ᶠ n : Nat in atTop,
              ∃ Bsource : BridgeData (PaperHeadSimplex.Tag P)
                  (BankPaperCanonicalExponentBand M),
                ∃ hnTail : N ≤ Bsource.sampleData.n,
                  let R := F.realization Bsource.sampleData.n hnTail
                  let certificate :=
                    F.certificate Bsource.sampleData.n hnTail
                  ∃ J :
                      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                        (K0 := K0) M Bsource R certificate I
                          deltaStar hdelta,
                    ∃ S :
                        BankPaperCanonicalSectionNinePostHeightSourceInputsAt
                          M Bsource R certificate I deltaStar hdelta J,
                      ∃ _Hgap :
                          BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                            M Bsource R certificate I E deltaStar
                              bankPaperCanonicalSectionNinePostHeightPhysicalMu
                              sourceCellMargin postMargin physicalEtaFloor
                              postCellMargin logY Lambda0 mFrozen qTilde
                              hdelta J S,
                        ∃ hsep :
                            physicalBound (I.upper .minus)
                                J.postHeightBridge.sampleData.n <
                              physicalBound (I.lower .plus)
                                J.postHeightBridge.sampleData.n,
                          ∃ hremaining :
                              ∀ cell :
                                  Cell (PaperHeadSimplex.Tag P),
                                (rawCell Patterns I
                                    J.postHeightBridge.sampleData.n cell \
                                  (G J.postHeightBridge.sampleData.n).guards).Nonempty,
                            B n = J.postHeightBridge ∧
                              Bsource.sampleData.n = n ∧
                              Bsource.sampleData.W = W ∧
                              J.betaProt = betaProt ∧
                              J.betaAct = betaAct ∧
                              J.postHeightBridge.sampleData =
                                canonicalSampleData
                                  (W :=
                                    J.postHeightBridge.sampleData.W)
                                  Patterns I
                                    (G
                                      J.postHeightBridge.sampleData.n)
                                    hsep hremaining ∧
                              J.qTilde =
                                bankPaperCanonicalGuardedSmoothBaseMass
                                  R certificate deltaStar
                                    J.postHeightBridge.sampleData.W
                                    (K0 + 1) J.betaAct ∧
                              S.Cmass = Cmass ∧
                              S.density = density := by
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation
      hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge hprefix
        F hterminal

/-! ## Public declaration census -/

#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation

end BankPaperRealization

end

end Erdos390.WholePaper
