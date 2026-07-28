import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshLedgerPostMarginAssembly

/-!
# Expanded statement audit: source-first pre-mesh ledger/post-margin assembly

This audit repeats the complete public statement of the pre-mesh assembly.
In particular, it displays the source numerical witnesses and their exact
margin and two-sided mass facts, the three common scalar families and their
analytic ledger, the positive post-height margin and all four eventual
mass/height inequalities, and only then the universal final-mesh quantifier.
For every final mesh it exposes the dependent fixed-rich source witness and
the literal eventual synchronization of all three common scalar families.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
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
            centralTailProduct n (upperTailLength c n)) :
    ∃ cSource cUpper : Real, ∃ E : Nat, ∃ sourceCellMargin : Real,
      0 < cSource ∧
        0 < cUpper ∧
        0 < E ∧
        sourceCellMargin =
          bankPaperCanonicalSectionNinePostHeightHeadMargin E
              (fun _ : {p : Nat // p ∈ primesUpTo W} =>
                bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
              cUpper *
            bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau ∧
        0 < sourceCellMargin ∧
        2 *
              (∑ p : {p : Nat // p ∈ primesUpTo W},
                bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                  c p.1) ≤
            (E : Real) * (cSource / 4) ∧
        (∀ᶠ n : Nat in atTop,
          cSource * secondOrderScale n ≤
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ∧
            F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ≤
              cUpper * secondOrderScale n) ∧
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
            ∃ CfinalUpper postMargin : Real,
              0 < CfinalUpper ∧
                postMargin =
                  bankPaperCanonicalSectionNinePostHeightHeadMargin
                    E
                    (fun _ : {p : Nat // p ∈ primesUpTo W} =>
                      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
                        c W)
                    CfinalUpper ∧
                0 < postMargin ∧
                (∀ᶠ n : Nat in atTop,
                  (cSource / 4) * secondOrderScale n ≤
                      bankPaperCanonicalSmoothFinalActiveMassFamily
                        bankPaperCanonicalSectionNinePostHeightPhysicalMu
                        logY Lambda0 mFrozen
                        (F.extendedGuardedSmoothBaseMass
                          W (K0 + 1) betaAct deltaStar) n ∧
                    ‖bankPaperCanonicalSmoothFinalActiveMassFamily
                        bankPaperCanonicalSectionNinePostHeightPhysicalMu
                        logY Lambda0 mFrozen
                        (F.extendedGuardedSmoothBaseMass
                          W (K0 + 1) betaAct deltaStar) n‖ ≤
                      CfinalUpper * ‖secondOrderScale n‖ ∧
                    Real.log
                          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                            .minus) ≤
                        bankPaperCanonicalSmoothFinalActiveHeightFamily
                              bankPaperCanonicalSectionNinePostHeightPhysicalMu
                              logY Lambda0 mFrozen
                              (F.extendedGuardedSmoothBaseMass
                                W (K0 + 1) betaAct deltaStar) n /
                            bankPaperCanonicalSmoothFinalActiveMassFamily
                              bankPaperCanonicalSectionNinePostHeightPhysicalMu
                              logY Lambda0 mFrozen
                              (F.extendedGuardedSmoothBaseMass
                                W (K0 + 1) betaAct deltaStar) n -
                          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
                      bankPaperCanonicalSmoothFinalActiveHeightFamily
                              bankPaperCanonicalSectionNinePostHeightPhysicalMu
                              logY Lambda0 mFrozen
                              (F.extendedGuardedSmoothBaseMass
                                W (K0 + 1) betaAct deltaStar) n /
                            bankPaperCanonicalSmoothFinalActiveMassFamily
                              bankPaperCanonicalSectionNinePostHeightPhysicalMu
                              logY Lambda0 mFrozen
                              (F.extendedGuardedSmoothBaseMass
                                W (K0 + 1) betaAct deltaStar) n +
                          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
                        Real.log
                          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                            .plus)) ∧
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
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshLedgerPostMarginAssembly
      hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge hprefix
        F hterminal

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshLedgerPostMarginAssembly

end BankPaperRealization

end

end Erdos390.WholePaper
