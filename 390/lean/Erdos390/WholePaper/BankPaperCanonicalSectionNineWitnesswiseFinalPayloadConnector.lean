import Erdos390.WholePaper.BankPaperCanonicalSectionNineSynchronizedPostHfitProducer

/-!
# Witnesswise synchronized Section 9 final-payload connector

The earlier parameter-synchronized connector packages a synchronized
Post-Hfit input which already contains existential capacity witnesses.  As a
conditional interface, that still permits its completion hypothesis to
construct a second bank and guarded anchor certificate unrelated to the
witnesses selected by the combined-charge terminal.

This file exposes the exact remaining interface.  Its local Post-Hfit
supplier is applied only after the combined-charge existential has been
destructured, and hence augments that very `BankPaperRealization` and guarded
anchor certificate.  The active-mass bound and the bridge index/width
equalities are eventual: no bridge at the exceptional small indices is
required to have sample index `0` or `1`.
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

/-! ## Exact witnesswise analytic completion -/

/-- The analytic data left after the capacity depth, Section 9 width, and
tangent exponent have been synchronized.

Unlike `BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion`, the
last field is not an already existentially packaged Post-Hfit input.  It is
a local supplier which receives the exact capacity bank and certificate
selected at each sufficiently large index, together with the four
combined-charge facts used downstream.

The bridge sample index and width are synchronized only eventually.  This is
the strongest inhabitable form because every `BridgeData` carries
`1 < sampleData.n`. -/
def BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
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
                  M B c depth K0 deltaStar sigma Cpost hdelta

/-! ## Parameter-synchronized exact-witness connector -/

/-- Choose the capacity depth first and then the common Section 9 width,
tangent exponent, and complete finite payload.

The completion callback does not receive
`BankPaperCombinedChargeTerminalAtDepth`.  The already proved terminal is
destructured internally by
`bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal`;
its exact bank and certificate are passed to the witnesswise local supplier.
Thus the returned distributed terminal cannot be assembled from an
independent second pair of capacity witnesses. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_witnesswiseAnalyticCompletion
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
          c deltaStar depth := by
  apply exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload
    hc
  intro depth W r0 deltaStar hdepth hWtwo hprefix hMertens hMoment
    hr0one hr0three hdeltaStar Hcharge
  have Hanalytic :=
    Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix hMertens
      hMoment hr0one hr0three hdeltaStar
  unfold BankPaperCanonicalSectionNineWitnesswiseAnalyticCompletion
    at Hanalytic
  obtain ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
    Cpost, Cq, hdelta, htangent, hsigma, hwidth, hCpost,
    hcoefficient, hsync, hqUpper, Hlocal⟩ :=
    Hanalytic
  have hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n := by
    filter_upwards [hsync] with n hsyncN
    exact hsyncN.1
  have Hinput :
      BankPaperCanonicalSectionNineSynchronizedPostHfitInput
        M B c depth K0 deltaStar (21 / 20 : Real)
          sigma Cpost hdelta :=
    BankPaperRealization.bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal
      M B deltaStar (21 / 20 : Real) sigma Cpost hdelta
        hBn Hcharge Hlocal
  unfold BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion
  exact
    ⟨delta, eta, M, P, B, K0, tangentConstant, sigma, Cpost, Cq,
      hdelta, htangent, hsigma, hwidth, hCpost, hcoefficient,
      hsync, hqUpper, Hinput⟩

end

end Erdos390.WholePaper
