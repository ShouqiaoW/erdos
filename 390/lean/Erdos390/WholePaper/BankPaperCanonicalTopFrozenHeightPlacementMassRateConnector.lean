import Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector

/-!
# Height-only two-zero-cell mass at the strict placement scale

The rounded frozen-top source has already paid for the nearest-integer
normalization.  The subsequent Section 8 height adjustment puts the same
signed mass `-d/2` in each of the two zero-head cells.

The analytic ledger proves `d = O(secondOrderScale / L)`.  This connector
records the direct consequence needed by the literal placement-moment
theorem: the sum of the absolute values of the two actual height-only cell
masses is bounded by a fixed multiple of `secondOrderScale / L`.

This statement is deliberately about the height-only second rebalance.  The
combined normalization-and-height change is only known to be
`o(secondOrderScale)` in the current library.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- The actual height-only mass in either zero-head cell has the paper's
`secondOrderScale / L` scale. -/
theorem bankPaperCanonicalSymmetricHeightCellMassFamily_isBigO_secondOrderScale_div_L
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSymmetricHeightCellMassFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  have hd :=
    bankPaperCanonicalSectionEight_d_isBigO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hhalf := hd.const_mul_left (-(1 : Real) / 2)
  exact hhalf.congr_left fun n => by
    unfold bankPaperCanonicalSymmetricHeightCellMassFamily
    unfold bankPaperCanonicalSymmetricHeightCellMass
    unfold bankPaperCanonicalSmoothDRealFamily
    ring

/-- Eventual absolute two-cell mass budget consumed by
`abs_bankPaperCanonicalTopFrozenRoundedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate`.
The constant is chosen once, before `n`. -/
theorem eventually_bankPaperCanonicalSymmetricHeightCellMassFamily_abs_two_le
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∃ Cmass : Real, 0 <= Cmass ∧
      ∀ᶠ n : Nat in atTop,
        abs
            (bankPaperCanonicalSymmetricHeightCellMassFamily
              mu logY Lambda0 mFrozen qTilde n) +
          abs
            (bankPaperCanonicalSymmetricHeightCellMassFamily
              mu logY Lambda0 mFrozen qTilde n) <=
          Cmass * (secondOrderScale n / L n) := by
  have hheight :=
    bankPaperCanonicalSymmetricHeightCellMassFamily_isBigO_secondOrderScale_div_L
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  rcases (isBigO_iff').mp hheight with ⟨C, hC, hbound⟩
  refine ⟨2 * C, mul_nonneg (by norm_num) hC.le, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 1] with n hboundN hn
  have hscale :
      0 < secondOrderScale n / L n :=
    div_pos (secondOrderScale_pos (by omega)) (L_pos hn)
  have htwice := mul_le_mul_of_nonneg_left hboundN
    (by norm_num : (0 : Real) <= 2)
  have htwice' :
      2 *
          abs
            (bankPaperCanonicalSymmetricHeightCellMassFamily
              mu logY Lambda0 mFrozen qTilde n) <=
        2 * (C * (secondOrderScale n / L n)) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using htwice
  calc
    abs
          (bankPaperCanonicalSymmetricHeightCellMassFamily
            mu logY Lambda0 mFrozen qTilde n) +
        abs
          (bankPaperCanonicalSymmetricHeightCellMassFamily
            mu logY Lambda0 mFrozen qTilde n) =
      2 *
        abs
          (bankPaperCanonicalSymmetricHeightCellMassFamily
            mu logY Lambda0 mFrozen qTilde n) := by ring
    _ <= 2 * (C * (secondOrderScale n / L n)) := htwice'
    _ = (2 * C) * (secondOrderScale n / L n) := by ring

end BankPaperRealization

end

end Erdos390.WholePaper
