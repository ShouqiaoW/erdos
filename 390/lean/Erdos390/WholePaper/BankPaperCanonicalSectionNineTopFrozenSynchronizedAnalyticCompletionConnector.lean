import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenEventStepConnector

/-!
# Synchronized analytic completion for the frozen-top Section 9 source

The public frozen-top event step already turns an eventual synchronized
Post-Hfit input into the distributed Section 9 terminal.  This file supplies
the parameter-synchronization layer parallel to
`BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion`.

The completion callback receives the actual combined-charge terminal selected
at the common capacity depth.  It then supplies the mesh, bridge family,
numerical data, actual bridge-mass bound, and frozen-top synchronized input.
No local source package, analytic ledger, or post-height construction is
postulated by this connector.
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

/-! ## Frozen-top residual analytic completion -/

/-- The analytic data which augment one already selected combined-charge
terminal and feed the public frozen-top Section 9 event step.

The depth, width, tangent exponent, and combined tangent parameter are fixed
before this package is requested.  The eventual Post-Hfit input retains the
same bridge family and uses the fixed ratio `21 / 20` required by the
parameter-synchronization theorem below. -/
def BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
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
                  BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
                    M B c depth K0 deltaStar (21 / 20 : Real)
                      sigma Cpost hdelta

/-! ## Parameter-synchronized distributed terminal -/

/-- Choose the capacity depth first, then the common width and tangent
parameters, and finally invoke a frozen-top analytic completion which receives
the exact combined-charge terminal selected at those parameters.

The conclusion retains both the combined-charge terminal and the distributed
finite-payload terminal at the same depth and `deltaStar`. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_topFrozenSynchronizedAnalyticCompletion
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
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth →
          BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
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
      hMoment hr0one hr0three hdeltaStar Hcharge
  unfold
    BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
    at Hanalytic
  obtain ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
    Cpost, Cq, hdelta, htangent, hsigma, hwidth, hCpost,
    hcoefficient, hsync, hqUpper, Hinput⟩ :=
    Hanalytic
  have hcPos : 0 < c := by
    have hC0Pos : (0 : Real) < C0 := by norm_num [C0]
    exact hC0Pos.trans hc
  have Hterminal :
      BankPaperCanonicalDistributedSectionNineTerminalAtDepth
        c deltaStar depth :=
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_topFrozenSynchronizedPostHfit
      M B W K0 depth hdelta hcPos hr0one hr0three hdeltaStar
      hWtwo hprefix hMoment hMertens hrho hratio htangent hsigma
      hwidth hCpost hcoefficient hPNT hprime hsync hqUpper Hinput
  exact
    ⟨depth, W, r0, deltaStar, hdepth, hWtwo, hprefix, hMertens,
      hMoment, hr0one, hr0three, hdeltaStar, Hcharge, Hterminal⟩

end

end Erdos390.WholePaper
