import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreselectedPostLedgerConnector

/-!
# Expanded statement audit: preselected source-first post-ledger bridge

This audit freezes the fixed-mesh consumption interface after all analytic
constants have already been selected.  In particular, `CfinalUpper`,
`postMargin`, their defining and positivity hypotheses, and the full
mesh-free event `Hpost` are explicit inputs.  The conclusion is directly the
eventual sixteen-field bridge tuple: it contains no existentially chosen
analytic constant.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hW : 0 < W)
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (cSource : Real)
    (hcSource : 0 < cSource)
    (E : Nat)
    (sourceCellMargin : Real)
    (hE : 0 < E)
    (hElarge :
      2 *
            (∑ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                c p.1) ≤
          (E : Real) * (cSource / 4))
    (logY Lambda0 mFrozen : Nat → Real)
    (CfinalUpper postMargin : Real)
    (hCfinalUpper : 0 < CfinalUpper)
    (hpostMargin :
      postMargin =
        bankPaperCanonicalSectionNinePostHeightHeadMargin
          E
          (fun _ : {p : Nat // p ∈ primesUpTo W} =>
            bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
          CfinalUpper)
    (hpostMarginPos : 0 < postMargin)
    (X :
      BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
        M (c := c) (deltaStar := deltaStar)
          (betaProt := betaProt) (betaAct := betaAct)
          (sourceCellMargin := sourceCellMargin)
          (depth := depth) (N := N) (W := W)
          (K0 := K0) (E := E) hdelta F)
    (Hsync :
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
                      (betaProt + betaAct) qTilde)
    (Hpost :
      ∀ᶠ n : Nat in atTop,
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
                  .plus)) :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let Y := X.source n hn
        let B := Y.1
        let R := Y.2.1.1
        let certificate := Y.2.1.2
        let T := Y.2.2
        let target :
            {p : Nat // p ∈ primesUpTo W} → Real :=
          fun p =>
            ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors
                deltaStar)).factorization p.1 : Real)
        ∃ Rhead : HeadSimplexReserve (primesUpTo W),
        ∃ Kphysical : PhysicalInterpolationTarget
            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals,
        ∃ J :
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
              (K0 := K0) M B R certificate
                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                deltaStar hdelta,
          J.Tsource = T ∧
            sourceCellMargin ≤ J.Tsource.cellMassMargin ∧
            Rhead.exponent = E ∧
            (∀ p, Rhead.target p = target p) ∧
            J.Tsource =
                J.postHeightBridge.barycentricTargetOfPaperData
                  bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                  J.postHeightHlo J.postHeightHhi Rhead Kphysical ∧
            J.qTilde = Rhead.activeMass ∧
            J.qTilde =
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ∧
            J.exponent = E ∧
            J.d =
              bankPaperCanonicalSmoothDIntFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen
                (F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar) n ∧
            J.betaProt = betaProt ∧
            J.betaAct = betaAct ∧
            J.q0 =
              bankPaperCanonicalSmoothQ0Family
                mFrozen
                (F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar) n ∧
            J.A0 =
              bankPaperCanonicalSmoothA0Family
                logY Lambda0 mFrozen
                (F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar) n ∧
            J.qn =
              bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen
                (F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar) n ∧
            J.targetInputs.headMargin = postMargin ∧
            J.targetInputs.physicalEta =
              bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 := by
  exact
    eventually_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostLedgerBridgeInputs
      M hc hW hdelta F cSource hcSource E sourceCellMargin hE hElarge
        logY Lambda0 mFrozen CfinalUpper postMargin hCfinalUpper
        hpostMargin hpostMarginPos X Hsync Hpost

#check
  eventually_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostLedgerBridgeInputs

end BankPaperRealization

end

end Erdos390.WholePaper
