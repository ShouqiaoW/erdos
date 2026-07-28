import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshNumericalData
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCommonLedgerBeforeMesh
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPostMarginData

/-!
# Source-first ledger and post-margin data before the final mesh

This module composes the three source-first choices which must precede the
final regular mesh:

* the source-mass coefficients, head exponent, and source-cell margin;
* the common Section 8 scalar ledger obtained from a reference mesh; and
* the final-active-mass upper coefficient and positive post-height margin.

The conclusion exposes every numerical fact and analytic estimate directly.
Only after all these witnesses have been chosen does it quantify over the
final mesh and return a genuine rich source synchronized with the common
ledger.
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

/-- Choose the source numerics, common scalar ledger, and post-height margin
before the final mesh. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshLedgerPostMarginAssembly
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
  obtain
      ⟨cSource, cUpper, E, sourceCellMargin,
        hcSource, hcUpper, hE, hsourceCellMarginEq,
        hsourceCellMarginPos, hElarge, Hmass⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshNumericalData
      depth W K0 hc hW hbetaAct deltaStar F
  obtain ⟨logY, Lambda0, mFrozen, hlogY, Hledger, Hmesh⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCommonLedgerBeforeMesh
      hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge hprefix
        F hterminal cSource cUpper E sourceCellMargin
        hcSource hcUpper hE hsourceCellMarginEq hElarge Hmass
  have HsourceLower :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n :=
    Hmass.mono fun _ hn => hn.1
  obtain
      ⟨CfinalUpper, postMargin, hCfinalUpper, hpostMargin,
        hpostMarginPos, Hpost⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPostMarginData
      hc hW hbetaAct F cSource E hcSource hE HsourceLower
        logY Lambda0 mFrozen Hledger
  exact
    ⟨cSource, cUpper, E, sourceCellMargin,
      hcSource, hcUpper, hE, hsourceCellMarginEq,
      hsourceCellMarginPos, hElarge, Hmass,
      logY, Lambda0, mFrozen, hlogY, Hledger,
      CfinalUpper, postMargin, hCfinalUpper, hpostMargin,
      hpostMarginPos, Hpost, Hmesh⟩

end BankPaperRealization

end

end Erdos390.WholePaper
