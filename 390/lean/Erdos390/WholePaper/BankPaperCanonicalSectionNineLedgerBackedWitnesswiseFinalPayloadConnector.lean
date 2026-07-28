import Erdos390.WholePaper.BankPaperCanonicalActualBridgeMassUpperConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineWitnesswiseFinalPayloadConnector

/-!
# Ledger-backed witnesswise Section 9 completion

The witnesswise Section 9 connector previously exposed an eventual upper
bound

`(B n).q <= Cq * secondOrderScale n`

as a direct analytic premise.  For the literal Section 8 bridge this bound
is already a consequence of two more primitive facts: the Section 8
analytic ledger and eventual identification of the bridge baseline with the
canonical scaled seed.

There is one genuine dependency-order issue.  The constant `Cq` is obtained
existentially from the Section 8 big-O estimate.  The Section 9 tangent
constant must be at least `(2 / 9) * Cpost * Cq`, while increasing that
tangent constant decreases the admissible mesh width.  Moreover `sigma`
and `Cpost` occur in the local Post-Hfit supplier.  Consequently these
three numerical choices cannot honestly be fixed before the big-O witness
is known.

The completion package below records the exact non-circular interface: the
mesh, bridge family, ledger, scaled-seed alignment, and index/width
synchronization are fixed first; a continuation then supplies the tangent
and Post-Hfit parameters for every positive big-O constant.  Applying that
continuation to the constant produced by Section 8 removes the direct
`q`-upper-bound premise entirely.

An additive source-state variant changes only the final local-supplier
socket.  Its terminal invokes the existing weak same-witness producer
directly, without reconstructing a rounded selector source.
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

/-! ## The ledger-backed completion package -/

/-- A witnesswise Section 9 completion whose actual bridge-mass estimate is
derived from the literal Section 8 ledger.

The final continuation is intentionally quantified over the positive
constant `Cq`.  This is the precise dependency order forced by the
coefficient condition and the inverse dependence of
`bankPaperCanonicalRatioCellPaperWidthChoice` on `tangentConstant`.
No eventual upper bound for `(B n).q` is a field of this definition. -/
def BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
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
                        M B c depth K0 deltaStar sigma Cpost hdelta

/-! ## Source-state ledger-backed completion package -/

/-- The ledger-backed completion whose final callback supplies only the
minimal selector source state consumed before Proposition 8.7.

All Section 8 ledger, scaled-seed, synchronization, and numerical fields are
identical to the legacy completion above.  Only the eventual local supplier
is weakened. -/
def
    BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
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
                        M B c depth K0 deltaStar sigma Cpost hdelta

/-! ## Eliminate the Section 8 asymptotic witness -/

/-- Convert the ledger-backed package into the exact witnesswise analytic
completion expected by the synchronized final-payload connector.

The only use of the Section 8 data is to produce one positive `Cq` and its
eventual actual-mass bound.  The numerical continuation is invoked only
after that `Cq` has been selected, so neither the tangent constant nor the
mesh-width condition is chosen circularly. -/
theorem
    bankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion_of_ledgerBacked
    {c : Real} {depth W : Nat} {r0 deltaStar : Real}
    (Hcompletion :
      BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar) :
    BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
      c depth W r0 deltaStar := by
  unfold
    BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
    at Hcompletion
  obtain
      ⟨delta, eta, M, P, B, K0, smoothK, betaAct, logY, Lambda0,
        mFrozen, qTilde, hdelta, Hledger, hseed, hsync, Hnumerical⟩ :=
    Hcompletion
  obtain ⟨Cq, hCq, hqUpper⟩ :=
    exists_bankPaperCanonical_actualBridge_q_upper_of_sectionEightLedger_scaledSeed
      B W smoothK c betaAct logY Lambda0 mFrozen qTilde Hledger hseed
  obtain
      ⟨tangentConstant, sigma, Cpost, htangent, hsigma, hwidth,
        hCpost, hcoefficient, Hlocal⟩ :=
    Hnumerical Cq hCq
  unfold BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
  exact
    ⟨delta, eta, M, P, B, K0, tangentConstant, sigma, Cpost, Cq,
      hdelta, htangent, hsigma, hwidth, hCpost, hcoefficient,
      hsync, hqUpper, Hlocal⟩

/-! ## Parameter-synchronized final payload -/

/-- The parameter-synchronized distributed Section 9 terminal follows from
ledger-backed witnesswise completions.

Thus the callback now exposes the literal Section 8 ledger and canonical
scaled-seed alignment, rather than an assumed eventual upper bound for the
actual bridge mass. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedWitnesswiseAnalyticCompletion
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
          c deltaStar depth := by
  apply
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_witnesswiseAnalyticCompletion
      hc
  intro depth W r0 deltaStar hdepth hWtwo hprefix hMertens hMoment
    hr0one hr0three hdeltaStar
  exact
    bankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion_of_ledgerBacked
      (Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix hMertens
        hMoment hr0one hr0three hdeltaStar)

/-! ## Source-state parameter-synchronized final payload -/

/-- The ledger-backed source-state completion feeds the existing weak
same-witness producer directly.

The Section 8 ledger first supplies the positive actual-mass constant.  Only
then is the numerical continuation invoked; its source-state local supplier
is passed to the combined-charge producer for the exact capacity witnesses. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
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
          c deltaStar depth := by
  apply exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload
    hc
  intro depth W r0 deltaStar hdepth hWtwo hprefix hMertens hMoment
    hr0one hr0three hdeltaStar Hcharge
  have Hanalytic :=
    Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix hMertens
      hMoment hr0one hr0three hdeltaStar
  unfold
    BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
    at Hanalytic
  obtain
      ⟨delta, eta, M, P, B, K0, smoothK, betaAct, logY, Lambda0,
        mFrozen, qTilde, hdelta, Hledger, hseed, hsync, Hnumerical⟩ :=
    Hanalytic
  obtain ⟨Cq, hCq, hqUpper⟩ :=
    exists_bankPaperCanonical_actualBridge_q_upper_of_sectionEightLedger_scaledSeed
      B W smoothK c betaAct logY Lambda0 mFrozen qTilde Hledger hseed
  obtain
      ⟨tangentConstant, sigma, Cpost, htangent, hsigma, hwidth,
        hCpost, hcoefficient, Hlocal⟩ :=
    Hnumerical Cq hCq
  have hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n := by
    filter_upwards [hsync] with n hsyncN
    exact hsyncN.1
  have Hinput :
      BankPaperCanonicalSectionNineSynchronizedPostHfitInput
        M B c depth K0 deltaStar (21 / 20 : Real)
          sigma Cpost hdelta :=
    BankPaperRealization.bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal_sourceStateLocalSupplier
      M B deltaStar (21 / 20 : Real) sigma Cpost hdelta
        hBn Hcharge Hlocal
  unfold BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion
  exact
    ⟨delta, eta, M, P, B, K0, tangentConstant, sigma, Cpost, Cq,
      hdelta, htangent, hsigma, hwidth, hCpost, hcoefficient,
      hsync, hqUpper, Hinput⟩

/-! ## Source-state global main-asymptotic wrapper -/

/-- Ledger-backed source-state completions at every paper scale imply the
literal small-`o` main theorem. -/
theorem
    mainAsymptotic_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
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
    MainAsymptotic := by
  apply mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  obtain
      ⟨depth, W, r0, deltaStar, hdepth, _hWtwo, _hprefix,
        _hMertens, _hMoment, _hr0one, _hr0three, _hdeltaStar,
        _hcharge, hterminal⟩ :=
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
      hc (Hcompletion c hc)
  exact
    eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
      hc hdepth hterminal

end

end Erdos390.WholePaper
