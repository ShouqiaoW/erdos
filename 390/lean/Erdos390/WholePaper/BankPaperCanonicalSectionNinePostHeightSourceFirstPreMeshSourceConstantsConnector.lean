import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceInputAssemblyConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor

/-!
# Source-input constants chosen before the final mesh

The mechanical Section 9 source-input assembler already chooses its mass
upper coefficient and guarded-cell density before a regular relative mesh.
This module specializes that theorem to the literal paper prime set,
patterns, physical intervals, physical mean, and rough canonical guard
ledger.

The result deliberately retains the full target/residual continuation of the
mechanical assembler.  In particular, no final mesh, bridge, target, source
record, or primitive-gap record is assumed when `Cmass` and `density` are
chosen.
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

noncomputable section

namespace BankPaperRealization

/-- Choose the source-input mass coefficient and cell-density constant before
the final mesh, after the common scalar ledger and the two source/post-height
head margins have been fixed.

The conclusion is the exact continuation of
`exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual`,
specialized to the paper data. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshSourceConstants
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 E : Nat}
    (hc : C0 < c)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hE : 0 < E)
    (sourceCellMargin postMargin : Real)
    (hsourceCellMargin : 0 < sourceCellMargin)
    (hpostMargin : 0 < postMargin)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
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
          (Bsource : BridgeData
            (PaperHeadSimplex.Tag (primesUpTo W))
            (BankPaperCanonicalExponentBand M)),
          Bsource.sampleData.n = n →
          Bsource.sampleData.W = W →
          ∀ (hnTail : N ≤ Bsource.sampleData.n),
            let R := F.realization Bsource.sampleData.n hnTail
            let certificate := F.certificate Bsource.sampleData.n hnTail
            ∀ (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                (K0 := K0) M Bsource R certificate
                  bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                  deltaStar hdelta),
              J.exponent = E →
              J.betaProt = betaProt →
              J.betaAct = betaAct →
              (∀
                (hsep :
                  physicalBound
                      (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                        .minus)
                      J.postHeightBridge.sampleData.n <
                    physicalBound
                      (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                        .plus)
                      J.postHeightBridge.sampleData.n)
                (hremaining :
                  ∀ cell :
                      Cell (PaperHeadSimplex.Tag (primesUpTo W)),
                  (rawCell
                      (PaperHeadSimplex.pattern
                        (primesUpTo W)
                        (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                          W) E)
                      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                      J.postHeightBridge.sampleData.n cell \
                    (roughCanonicalBridgeRelevantLedgerFamily depth
                      J.postHeightBridge.sampleData.n).guards).Nonempty),
                J.postHeightBridge.sampleData =
                    canonicalSampleData
                      (W := J.postHeightBridge.sampleData.W)
                      (PaperHeadSimplex.pattern
                        (primesUpTo W)
                        (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                          W) E)
                      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                      (roughCanonicalBridgeRelevantLedgerFamily depth
                        J.postHeightBridge.sampleData.n)
                      hsep hremaining →
                J.qTilde =
                    bankPaperCanonicalGuardedSmoothBaseMass
                      R certificate deltaStar
                        J.postHeightBridge.sampleData.W
                        (K0 + 1) J.betaAct →
                sourceCellMargin ≤ J.Tsource.cellMassMargin →
                postMargin ≤ J.targetInputs.headMargin →
                bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
                    J.targetInputs.physicalEta →
                postMargin *
                      ((bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2) /
                        PhysicalInterpolationTarget.physicalSpan
                          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals) ≤
                    J.postHeightTarget.cellMassMargin →
                mFrozen Bsource.sampleData.n =
                    bankPaperCanonicalTopFrozenSmoothFrozenMass
                      (K := K0 + 1) J.postHeightBridge R certificate
                      deltaStar J.betaProt J.alpha →
                J.qn =
                    bankPaperCanonicalSmoothFinalActiveMassFamily
                      bankPaperCanonicalSectionNinePostHeightPhysicalMu
                      logY Lambda0 mFrozen
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
                      M Bsource R certificate
                        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                        deltaStar hdelta J,
                  ∃ _Hgap :
                      BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                        M Bsource R certificate
                          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                          E deltaStar
                          bankPaperCanonicalSectionNinePostHeightPhysicalMu
                          sourceCellMargin postMargin
                          (bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2)
                          (postMargin *
                            ((bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2) /
                              PhysicalInterpolationTarget.physicalSpan
                                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals))
                          logY Lambda0 mFrozen
                          (F.extendedGuardedSmoothBaseMass
                            W (K0 + 1) betaAct deltaStar)
                          hdelta J S,
                    S.Cmass = Cmass ∧ S.density = density) := by
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  have hcPos : 0 < c := by
    exact
      (show (0 : Real) < C0 by norm_num [C0]).trans hc
  have hlowerOne : ∀ sign, 1 ≤ I.lower sign := by
    intro sign
    simpa only [I] using
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one sign
  have hupperStrict : ∀ sign, I.upper sign < 2 := by
    intro sign
    cases sign <;>
      norm_num [I,
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals]
  have hphysicalEtaFloor :
      0 < bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 := by
    exact div_pos
      bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
      (by norm_num)
  have hpostCellMargin :
      0 <
        postMargin *
          ((bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2) /
            PhysicalInterpolationTarget.physicalSpan I) := by
    exact mul_pos hpostMargin
      (div_pos hphysicalEtaFloor
        (PhysicalInterpolationTarget.physicalSpan_pos (I := I)))
  have hhead :
      primesUpTo W ⊆ primesUpTo W := by
    intro p hp
    exact hp
  simpa only [I] using
    (exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceInputsAndPrimitiveGapsAt_of_targetResidual
      (primesUpTo W)
      (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W)
      E hE I hlowerOne hupperStrict depth W K0 N F
      hcPos hbetaAct
      bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      hbetaProt hsourceCellMargin hpostMargin
      hphysicalEtaFloor hpostCellMargin hhead
      logY Lambda0 mFrozen Hledger)

end BankPaperRealization

end

end Erdos390.WholePaper
