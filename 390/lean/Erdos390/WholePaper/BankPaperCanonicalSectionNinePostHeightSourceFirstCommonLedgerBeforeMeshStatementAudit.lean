import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCommonLedgerBeforeMesh

/-!
# Statement audit for the common source-first ledger before the final mesh

This audit reproduces the complete parameter order of the common-ledger
theorem.  In particular, all guarded-tail, fixed numerical, source-margin,
and two-sided mass inputs occur before the scalar families.  The exact
Section 8 analytic ledger follows the three scalar witnesses, while the
final regular relative mesh is universally quantified only afterwards.

For each such final mesh the conclusion displays the dependent fixed-rich
source witness and the literal eventual synchronization of its frozen mass,
precharged logarithm, and rounded logarithmic mass with the three common
families.  The audit does not replace either the ledger or synchronization
conclusion by a named conclusion package.
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

set_option maxHeartbeats 2400000 in
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
            centralTailProduct n (upperTailLength c n))
    (cSource cUpper : Real) (E : Nat) (sourceCellMargin : Real)
    (hcSource : 0 < cSource)
    (hcUpper : 0 < cUpper)
    (hE : 0 < E)
    (hsourceCellMarginEq :
      sourceCellMargin =
        bankPaperCanonicalSectionNinePostHeightHeadMargin E
            (fun _ : {p : Nat // p ∈ primesUpTo W} =>
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
            cUpper *
          bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau)
    (hElarge :
      2 *
            (∑ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                c p.1) ≤
          (E : Real) * (cSource / 4))
    (Hmass :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n ∧
          F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n ≤
            cUpper * secondOrderScale n) :
    ∃ logY Lambda0 mFrozen : Nat → Real,
      logY = F.extendedPrechargedTailLogTarget ∧
        BankPaperCanonicalSectionEightAnalyticLedger
          (fun n =>
            bankPaperCanonicalRawSmoothBaseMass W n
              (upperTailLength c n) (K0 + 1) betaAct)
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)
          (bankPaperCanonicalSmoothA0Family
            logY Lambda0 mFrozen
            (F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar)) ∧
        ∀ {delta eta : Real}
            (M : RegularRelativeMesh.Mesh delta eta)
            (hdelta : 0 < delta),
          ∃ X :
              BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
                M (c := c) (deltaStar := deltaStar)
                  (betaProt := betaProt) (betaAct := betaAct)
                  (sourceCellMargin := sourceCellMargin)
                  (depth := depth) (N := N) (W := W)
                  (K0 := K0) (E := E) hdelta F,
            ∀ᶠ n : Nat in atTop,
              ∀ hn : N ≤ n,
                let Y := X.source n hn
                let B := Y.1
                let R := Y.2.1.1
                let certificate := Y.2.1.2
                let T := Y.2.2
                let alpha :=
                  bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct
                let qTilde :=
                  F.extendedGuardedSmoothBaseMass
                    W (K0 + 1) betaAct deltaStar n
                mFrozen n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass
                      (K := K0 + 1) B R certificate
                        deltaStar betaProt alpha ∧
                  logY n =
                    bankPaperCanonicalSectionNinePostHeightLogY
                      B R certificate ∧
                  Lambda0 n =
                    bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                      (K0 + 1) B R certificate T
                        deltaStar betaProt alpha
                          (betaProt + betaAct) qTilde := by
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCommonLedgerBeforeMesh
      hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge hprefix
        F hterminal cSource cUpper E sourceCellMargin
        hcSource hcUpper hE hsourceCellMarginEq hElarge Hmass

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCommonLedgerBeforeMesh

end BankPaperRealization

end

end Erdos390.WholePaper
