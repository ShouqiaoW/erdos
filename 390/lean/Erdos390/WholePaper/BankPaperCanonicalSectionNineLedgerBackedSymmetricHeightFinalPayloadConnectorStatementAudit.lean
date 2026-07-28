import Erdos390.WholePaper.BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightFinalPayloadConnector

/-!
# Statement audit for ledger-backed symmetric-height completion

The checks expose both exact finite-to-eventual lifts: the legacy
three-package rounded-source supplier and the primary weak source-state
supplier with one dependent analytic tail.  They also audit the unchanged
Section 8 and parameter-synchronization interfaces.
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

namespace BankPaperRealization

/-! ## Exact eventual lift -/

/-- The supplier is tail-only.  At each sufficiently large index the
canonical partition is chosen before the capacity realization and
certificate, and the three symmetric-height packages are returned for
those exact witnesses after all four capacity facts have been received. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta ↔
      ∀ᶠ n : Nat in atTop,
        ∃ hW : (B n).sampleData.W ≠ 0,
          ∃ Sscale : ScaleSeparation M
              (B n).sampleData.n (B n).sampleData.W,
            (B n).partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta (B n).n_gt_one hW Sscale ∧
              ∀ (R : BankPaperRealization (B n).sampleData.n
                    (upperEndpoint (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n)))
                (certificate : GuardedCentralAnchorCertificate c depth
                  (B n).sampleData.n R.anchorGuardLeftCore
                  R.anchorGuardRightCore
                  (R.centralChangedMarkers depth)),
                centralAnchorDivisor (B n).sampleData.n
                      (centralAnchorCutoff depth (B n).sampleData.n)
                      certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                (baseBankFactors R.exactificationState).prod id ∣
                    certificate.prechargedTailTarget →
                R.selectorTailCharge
                      (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                certificate.prechargedTailTarget *
                      centralAnchorDivisor (B n).sampleData.n
                        (centralAnchorCutoff depth (B n).sampleData.n)
                        certificate.q =
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                ∃ Hsource :
                    BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
                      (B n) R certificate K0 deltaStar,
                  ∃ Hanalytic :
                      BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
                        (B n) R certificate K0 deltaStar Cpost Hsource,
                    Nonempty
                      (BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
                        (B n) R certificate K0 deltaStar sigma Cpost
                          Hsource Hanalytic) := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (Hsymmetric :
      BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNinePostHfitLocalSupplier
      M B c depth K0 deltaStar sigma Cpost hdelta :=
  bankPaperCanonicalSectionNinePostHfitLocalSupplier_of_symmetricHeight
    M B c depth K0 deltaStar sigma Cpost hdelta Hsymmetric

/-! ## Exact eventual source-state lift -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta ↔
      ∀ᶠ n : Nat in atTop,
        ∃ hW : (B n).sampleData.W ≠ 0,
          ∃ Sscale : ScaleSeparation M
              (B n).sampleData.n (B n).sampleData.W,
            (B n).partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta (B n).n_gt_one hW Sscale ∧
              ∀ (R : BankPaperRealization (B n).sampleData.n
                    (upperEndpoint (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n)))
                (certificate : GuardedCentralAnchorCertificate c depth
                  (B n).sampleData.n R.anchorGuardLeftCore
                  R.anchorGuardRightCore
                  (R.centralChangedMarkers depth)),
                centralAnchorDivisor (B n).sampleData.n
                      (centralAnchorCutoff depth (B n).sampleData.n)
                      certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                (baseBankFactors R.exactificationState).prod id ∣
                    certificate.prechargedTailTarget →
                R.selectorTailCharge
                      (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                certificate.prechargedTailTarget *
                      centralAnchorDivisor (B n).sampleData.n
                        (centralAnchorCutoff depth (B n).sampleData.n)
                        certificate.q =
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                ∃ Hsource :
                    BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
                      (B n) R certificate K0 deltaStar,
                  Nonempty
                    (BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
                      (B n) R certificate K0 deltaStar sigma Cpost
                        Hsource) := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (Hsymmetric :
      BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
      M B c depth K0 deltaStar sigma Cpost hdelta :=
  bankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier_of_symmetricHeight
    M B c depth K0 deltaStar sigma Cpost hdelta Hsymmetric

end BankPaperRealization

/-! ## Expanded completion package -/

example (c : Real) (depth W : Nat) (r0 deltaStar : Real) :
    BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
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
                          BankPaperRealization.BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
                            M B c depth K0 deltaStar sigma Cpost
                              hdelta := by
  rfl

example (c : Real) (depth W : Nat) (r0 deltaStar : Real) :
    BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
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
                          BankPaperRealization.BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
                            M B c depth K0 deltaStar sigma Cpost
                              hdelta := by
  rfl

/-! ## Exact completion conversion -/

example
    {c : Real} {depth W : Nat} {r0 deltaStar : Real}
    (Hcompletion :
      BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar) :
    BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
      c depth W r0 deltaStar :=
  bankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion_of_symmetricHeight
    Hcompletion

example
    {c : Real} {depth W : Nat} {r0 deltaStar : Real}
    (Hcompletion :
      BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar) :
    BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
      c depth W r0 deltaStar :=
  bankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion_of_symmetricHeight
    Hcompletion

/-! ## Exact public terminal -/

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
          BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
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
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
    hc Hcompletion

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
          BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
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
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
    hc Hcompletion

/-! ## Exact global main theorem wrapper -/

/-- The global callback does not receive an externally fixed capacity depth.
For each `c > C0`, the synchronized terminal chooses the depth used by the
eventual endpoint reduction. -/
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
            BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
              c depth W r0 deltaStar) :
    MainAsymptotic :=
  mainAsymptotic_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
    Hcompletion

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
            BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
              c depth W r0 deltaStar) :
    MainAsymptotic :=
  mainAsymptotic_of_ledgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
    Hcompletion

/-! ## Complete public declaration census -/

#check
  BankPaperRealization.BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHfitLocalSupplier_of_symmetricHeight
#check
  BankPaperRealization.BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
#check
  BankPaperRealization.bankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier_of_symmetricHeight
#check
  BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
#check
  BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
#check
  bankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion_of_symmetricHeight
#check
  bankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion_of_symmetricHeight
#check
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
#check
  exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
#check
  mainAsymptotic_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
#check
  mainAsymptotic_of_ledgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion

end

end Erdos390.WholePaper
