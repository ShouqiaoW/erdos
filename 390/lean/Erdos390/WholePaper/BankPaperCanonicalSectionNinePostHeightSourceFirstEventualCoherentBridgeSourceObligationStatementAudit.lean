import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstEventualCoherentBridgeSourceObligation

/-!
# Statement audit for the source-first eventual coherent bridge obligation

This audit freezes the complete expanded public interface: the literal
combined-charge tail hypotheses and the fixed constants, analytic ledger,
total post-height bridge family, and eventual coherent source obligation
produced from them.
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
open BankPaperRealization

noncomputable section

set_option maxHeartbeats 3600000 in
example
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
  exact
    BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstEventualCoherentBridgeSourceObligation
      M hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge
        hprefix hdelta F hterminal

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstEventualCoherentBridgeSourceObligation

end

end Erdos390.WholePaper
