import Erdos390.WholePaper.BankPaperCanonicalSectionNineLedgerBackedWitnesswiseFinalPayloadConnector

/-!
# Statement audit for ledger-backed witnesswise completion

The expanded packages below show that the direct eventual upper bound for
`(B n).q` has disappeared.  In its place are the Section 8 analytic ledger,
eventual canonical scaled-seed alignment, and a numerical continuation
which is invoked after the positive big-O constant is known.  Both the
legacy rounded-source supplier and the primary weak source-state supplier
are audited.
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

/-! ## Expanded ledger-backed package -/

example (c : Real) (depth W : Nat) (r0 deltaStar : Real) :
    BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
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
                          (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                          BankPaperRealization.BankPaperCanonicalSectionNinePostHfitLocalSupplier
                            M B c depth K0 deltaStar sigma Cpost
                              hdelta := by
  rfl

example (c : Real) (depth W : Nat) (r0 deltaStar : Real) :
    BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
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
                          (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                          BankPaperRealization.BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
                            M B c depth K0 deltaStar sigma Cpost
                              hdelta := by
  rfl

/-! ## Exact reduction -/

example
    {c : Real} {depth W : Nat} {r0 deltaStar : Real}
    (Hcompletion :
      BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar) :
    BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
      c depth W r0 deltaStar :=
  bankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion_of_ledgerBacked
    Hcompletion

/-! ## Exact source-state parameter callback order -/

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
          BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
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
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
    hc Hcompletion

/-! ## Exact parameter callback order -/

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
          BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
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
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedWitnesswiseAnalyticCompletion
    hc Hcompletion

/-! ## Exact source-state main-asymptotic wrapper -/

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
            BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
              c depth W r0 deltaStar) :
    MainAsymptotic :=
  mainAsymptotic_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
    Hcompletion

/-! ## Complete public declaration census -/

#check
  BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
#check
  BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
#check
  bankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion_of_ledgerBacked
#check
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedWitnesswiseAnalyticCompletion
#check
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
#check
  mainAsymptotic_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion

end

end Erdos390.WholePaper
