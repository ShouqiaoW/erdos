import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareAnalyticCompletion

/-!
# Cutoff-aware source-first distributed Section 9 terminal

The source-first analytic completion chooses its Proposition 8.7 width
cutoff only after the common capacity depth has been fixed.  Consequently
the final paper width must be chosen after that cutoff is known.  This
connector performs that choice in the required order: it first obtains the
depth-uniform combined-charge terminal, then the analytic cutoff `W0`, and
finally takes one width dominating `W0` together with the anchor, Mertens,
moment, prime-count, and prime-occupancy cutoffs.

The tangent exponent and the combined-charge terminal are specialized only
at that final width.  Thus the analytic completion and the distributed
finite-payload event step use the same `W`, `deltaStar`, and capacity depth.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

namespace BankPaperRealization

/-- The cutoff-aware source-first analytic construction produces a
distributed Section 9 terminal at the same depth and tangent exponent as the
depth-uniform combined-charge terminal.

The conclusion retains the paper-range tangent certificate and the actual
combined-charge terminal.  In the proof, the final width is selected only
after the Proposition 8.7 cutoff supplied by the analytic completion. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
    {c : Real} (hc : C0 < c) :
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
  obtain ⟨W0, Hcompletion⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion
      hc depth hdepth
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
  let Wpaper : Nat :=
    max (2 * depth + 1)
      (max tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy)))
  let W : Nat := max W0 Wpaper
  have hW0 : W0 ≤ W := by
    dsimp only [W]
    exact le_max_left _ _
  have hWpaper : Wpaper ≤ W := by
    dsimp only [W]
    exact le_max_right _ _
  have hprefixPaper : 2 * depth + 1 ≤ Wpaper := by
    dsimp only [Wpaper]
    exact le_max_left _ _
  have hprefix : 2 * depth + 1 ≤ W :=
    hprefixPaper.trans hWpaper
  have hMertensBasePaper :
      tangentSelbergMertensBase ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      (le_max_left tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy))).trans
          (le_max_right _ _)
  have hMertensBase : tangentSelbergMertensBase ≤ W :=
    hMertensBasePaper.trans hWpaper
  have hWtwo : 2 ≤ W :=
    tangentSelbergMertensBase_ge_two.trans hMertensBase
  have hMertens : fullReciprocalSumUniformCutoff ≤ W :=
    tangentSelbergMertensBase_ge_cutoff.trans hMertensBase
  have hMomentPaper : canonicalActualMomentCutoff ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      ((le_max_left canonicalActualMomentCutoff
        (max WPNT Woccupancy)).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hMoment : canonicalActualMomentCutoff ≤ W :=
    hMomentPaper.trans hWpaper
  have hWPNTpaper : WPNT ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      (((le_max_left WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWPNTW : WPNT ≤ W :=
    hWPNTpaper.trans hWpaper
  have hWoccupancyPaper : Woccupancy ≤ Wpaper := by
    dsimp only [Wpaper]
    exact
      (((le_max_right WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWoccupancyW : Woccupancy ≤ W :=
    hWoccupancyPaper.trans hWpaper
  have hPNT : TangentFixedRatioPrimeCountLower W rho :=
    tangentFixedRatioPrimeCountLower_mono_cutoff hWPNTW hWPNT
  have hprime : TangentFixedRatioPrimeIntervalOccupied W rho :=
    tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
      hWoccupancyW hWoccupancy
  let deltaStar := paperCombinedTangentDeltaStar c W r0
  obtain ⟨hdeltaStar, Hcharge⟩ :=
    huniform W r0 hr0two
  have Hanalytic :=
    Hcompletion W hW0 hWtwo hprefix hMertens hMoment
      r0 deltaStar hr0one hr0three hdeltaStar Hcharge
  unfold
    BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
    at Hanalytic
  obtain
      ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
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

end BankPaperRealization

end

end Erdos390.WholePaper
