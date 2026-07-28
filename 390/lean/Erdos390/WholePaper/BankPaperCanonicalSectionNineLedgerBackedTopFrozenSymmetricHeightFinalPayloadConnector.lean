import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightEventualConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineLedgerBackedWitnesswiseFinalPayloadConnector

/-!
# Ledger-backed frozen-top symmetric-height Section 9 completion

This is the family-level wrapper for the selector-correct frozen-top local
supplier.  Its Section 8 ledger, scaled-seed alignment, synchronization,
and numerical dependency order are the same as in the existing
ledger-backed symmetric-height completion.  The final callback is instead
the same-witness frozen-top supplier, and the distributed terminal is
constructed through the public frozen-top event step.

No equality with the legacy global source selector occurs in this file.
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

/-! ## Ledger-backed completion type -/

/-- The ledger-backed completion whose final continuation supplies the
selector-correct frozen-top symmetric-height packages for the exact
capacity witnesses.

The continuation is invoked only after the positive bridge-mass constant
`Cq` has been selected. -/
def
    BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
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
                      BankPaperRealization.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
                        M B c depth K0 deltaStar (21 / 20 : Real)
                          sigma Cpost hdelta

/-! ## Parameter-synchronized terminal -/

/-- Ledger-backed frozen-top completions at every synchronized paper
parameter choice produce the combined-charge and distributed Section 9
terminals at one common depth. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
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
          c deltaStar depth := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice hc
  let r0 : Real := 5 / 4
  let rho : Real := 21 / 20
  have hr0one : 1 < r0 := by norm_num [r0]
  have hr0three : r0 < 3 / 2 := by norm_num [r0]
  have hr0two : r0 < 2 := by norm_num [r0]
  have hrho : 1 < rho := by norm_num [rho]
  have hratio : rho ^ 3 < r0 := by norm_num [rho, r0]
  obtain ⟨WPNT, _hWPNTtwo, _hWPNTMertens, hWPNT⟩ :=
    exists_fixedRatioPrimeCountLower_and_Mertens_cutoff hrho
  obtain ⟨Woccupancy, _hWoccupancyTwo, hWoccupancy⟩ :=
    exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho
  let W : Nat :=
    max (2 * depth + 1)
      (max tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy)))
  have hprefix : 2 * depth + 1 ≤ W := by
    dsimp only [W]
    exact le_max_left _ _
  have hMertensBase : tangentSelbergMertensBase ≤ W := by
    dsimp only [W]
    exact
      (le_max_left tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy))).trans
          (le_max_right _ _)
  have hWtwo : 2 ≤ W :=
    tangentSelbergMertensBase_ge_two.trans hMertensBase
  have hMertens : fullReciprocalSumUniformCutoff ≤ W :=
    tangentSelbergMertensBase_ge_cutoff.trans hMertensBase
  have hMoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W]
    exact
      ((le_max_left canonicalActualMomentCutoff
        (max WPNT Woccupancy)).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWPNTW : WPNT ≤ W := by
    dsimp only [W]
    exact
      (((le_max_left WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWoccupancyW : Woccupancy ≤ W := by
    dsimp only [W]
    exact
      (((le_max_right WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hPNT : TangentFixedRatioPrimeCountLower W rho :=
    tangentFixedRatioPrimeCountLower_mono_cutoff hWPNTW hWPNT
  have hprime : TangentFixedRatioPrimeIntervalOccupied W rho :=
    tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
      hWoccupancyW hWoccupancy
  let deltaStar := paperCombinedTangentDeltaStar c W r0
  obtain ⟨hdeltaStar, Hcharge⟩ :=
    huniform W r0 hr0two
  have Hanalytic :=
    Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix hMertens
      hMoment hr0one hr0three hdeltaStar
  unfold
    BankPaperCanonicalSectionNineLedgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
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
  have Hlocal' :
      BankPaperRealization.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar rho sigma Cpost hdelta := by
    simpa only [rho] using Hlocal
  have hcPos : 0 < c := by
    have hC0Pos : (0 : Real) < C0 := by norm_num [C0]
    exact hC0Pos.trans hc
  have Hterminal :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth :=
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSymmetricHeightLocalSupplier
      M B W K0 depth hdelta hcPos hr0one hr0three hdeltaStar
      hWtwo hprefix hMoment hMertens hrho hratio htangent hsigma
      hwidth hCpost hcoefficient hPNT hprime hsync hqUpper
      Hcharge Hlocal'
  exact
    ⟨depth, W, r0, deltaStar, hdepth, hWtwo, hprefix, hMertens,
      hMoment, hr0one, hr0three, hdeltaStar, Hcharge, Hterminal⟩

/-! ## Global main asymptotic -/

/-- Selector-correct ledger-backed frozen-top completions at every paper
scale imply the literal small-`o` main theorem. -/
theorem
    mainAsymptotic_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
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
    MainAsymptotic := by
  apply mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  obtain
      ⟨depth, W, r0, deltaStar, hdepth, _hWtwo, _hprefix,
        _hMertens, _hMoment, _hr0one, _hr0three, _hdeltaStar,
        _hcharge, hterminal⟩ :=
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedTopFrozenSymmetricHeightWitnesswiseAnalyticCompletion
      hc (Hcompletion c hc)
  exact
    eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
      hc hdepth hterminal

end

end Erdos390.WholePaper
