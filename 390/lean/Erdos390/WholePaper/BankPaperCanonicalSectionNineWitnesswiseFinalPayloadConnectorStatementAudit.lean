import Erdos390.WholePaper.BankPaperCanonicalSectionNineWitnesswiseFinalPayloadConnector

/-!
# Statement audit for the witnesswise Section 9 final-payload connector

The transparent completion package is expanded literally, and the production
theorem is restated with its exact callback quantifier order.  In particular,
the callback has no combined-charge terminal argument.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Expanded witnesswise completion -/

example (c : Real) (depth W : Nat) (r0 deltaStar : Real) :
    BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar ↔
      ∃ delta eta : Real,
        ∃ M : RegularRelativeMesh.Mesh delta eta,
          ∃ P : Finset Nat,
            ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
                (BankPaperCanonicalExponentBand M),
              ∃ K0 : Nat,
                ∃ tangentConstant sigma Cpost Cq : Real,
                  ∃ hdelta : 0 < delta,
                    0 < tangentConstant ∧
                    0 < sigma ∧
                    delta + M.ratio ≤
                      bankPaperCanonicalRatioCellPaperWidthChoice
                        (tangentPaperCleanListDensity W r0)
                        sigma (21 / 20 : Real) tangentConstant ∧
                    0 ≤ Cpost ∧
                    (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                    (∀ᶠ n : Nat in atTop,
                      (B n).sampleData.n = n ∧
                        (B n).sampleData.W = W) ∧
                    (∀ᶠ n : Nat in atTop,
                      (B n).q ≤ Cq * secondOrderScale n) ∧
                    BankPaperRealization.BankPaperCanonicalSectionNinePostHfitLocalSupplier
                      M B c depth K0 deltaStar sigma Cpost hdelta := by
  rfl

/-! ## Exact callback order -/

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
          BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
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
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_witnesswiseAnalyticCompletion
    hc Hcompletion

/-! ## Complete public declaration census -/

#check BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
#check
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_witnesswiseAnalyticCompletion

end

end Erdos390.WholePaper
