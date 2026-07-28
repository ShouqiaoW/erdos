import Erdos390.WholePaper.BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightFinalPayloadConnector

/-!
# Statement audit for the ledger-backed frozen-top completion

The first example unfolds the completion proposition, so that the order of
the mesh, ledger, bridge family, `Cq`, numerical constants, and local
supplier is checked independently of the declaration.  The remaining
examples restate the two public theorem signatures.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

example (c : Real) (depth W : Nat) (r0 deltaStar : Real) :
    BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar ↔
      ∃ delta eta : Real,
        ∃ M : RegularRelativeMesh.Mesh delta eta,
          ∃ P : Finset Nat,
            ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
                (BankPaperCanonicalExponentBand M),
              ∃ K0 smoothK : Nat,
                ∃ betaAct : Real,
                  ∃ logY Lambda0 mFrozen qTilde : Nat → Real,
                    ∃ hdelta : 0 < delta,
                      BankPaperCanonicalSectionEightAnalyticLedger
                        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
                          (upperTailLength c n) smoothK betaAct)
                        qTilde
                        (bankPaperCanonicalSmoothA0Family
                          logY Lambda0 mFrozen qTilde) ∧
                      (∀ᶠ n : Nat in atTop,
                        ∃ T : BarycentricTarget (B n).sampleData,
                          ∀ m : (B n).sampleData.Sample,
                            (B n).baseline.baseWeight m =
                              bankPaperCanonicalScaledActiveSeed T
                                (bankPaperCanonicalSmoothQ0Family
                                  mFrozen qTilde n) m) ∧
                      (∀ᶠ n : Nat in atTop,
                        (B n).sampleData.n = n ∧
                          (B n).sampleData.W = W) ∧
                      ∀ Cq : Real, 0 < Cq →
                        ∃ tangentConstant sigma Cpost : Real,
                          0 < tangentConstant ∧
                          0 < sigma ∧
                          delta + M.ratio ≤
                            bankPaperCanonicalRatioCellPaperWidthChoice
                              (tangentPaperCleanListDensity W r0)
                              sigma (21 / 20 : Real) tangentConstant ∧
                          0 ≤ Cpost ∧
                          (2 / 9 : Real) * Cpost * Cq ≤
                            tangentConstant ∧
                          BankPaperRealization.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
                            M B c depth K0 deltaStar (21 / 20 : Real)
                              sigma Cpost hdelta := by
  rfl

example
    {c : Real} (hc : C0 < c)
    (Hcompletion :
      ∀ (depth W : Nat) (r0 deltaStar : Real),
        201 ≤ depth →
        2 ≤ W →
        2 * depth + 1 ≤ W →
        fullReciprocalSumUniformCutoff ≤ W →
        canonicalActualMomentCutoff ≤ W →
        1 < r0 →
        r0 < 3 / 2 →
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
          BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
            c depth W r0 deltaStar) :
    ∃ depth W : Nat, ∃ r0 deltaStar : Real,
      201 ≤ depth ∧
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        1 < r0 ∧
        r0 < 3 / 2 ∧
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar ∧
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
        BankPaperCanonicalDistributedSectionNineTerminalAtDepth
          c deltaStar depth :=
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
    hc Hcompletion

example
    (Hcompletion :
      ∀ (c : Real), C0 < c →
        ∀ (depth W : Nat) (r0 deltaStar : Real),
          201 ≤ depth →
          2 ≤ W →
          2 * depth + 1 ≤ W →
          fullReciprocalSumUniformCutoff ≤ W →
          canonicalActualMomentCutoff ≤ W →
          1 < r0 →
          r0 < 3 / 2 →
          IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
            BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
              c depth W r0 deltaStar) :
    MainAsymptotic :=
  mainAsymptotic_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
    Hcompletion

#check
  BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
#check
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
#check
  mainAsymptotic_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion

end

end Erdos390.WholePaper
