import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPhysicalMarginAlgebra

/-!
# Statement audit for the explicit post-height physical margin

The expanded examples below expose the literal rational intervals, the
fixed interpolation target, the generic `O(scale)` margin theorem, and its
application to the actual post-height height-to-mass ratio.
-/

open Filter Topology Set Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal data audit -/

example :
    bankPaperCanonicalSectionNinePostHeightPhysicalMu =
        Real.log ((3 : Real) / 2) ∧
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
          .minus = 1 ∧
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
          .minus = (4 : Real) / 3 ∧
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
          .plus = (5 : Real) / 3 ∧
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
          .plus = (7 : Real) / 4 := by
  simp [bankPaperCanonicalSectionNinePostHeightPhysicalMu]

example :
    (∀ sigma,
      1 ≤ bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
        sigma) ∧
    (∀ sigma,
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
        sigma ≤ 2) := by
  exact
    ⟨bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one,
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two⟩

example :
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.mu =
        bankPaperCanonicalSectionNinePostHeightPhysicalMu ∧
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta =
        bankPaperCanonicalSectionNinePostHeightPhysicalEta ∧
      0 < bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta ∧
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) ≤
        bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.mu -
          bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta ∧
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.mu +
          bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta ≤
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) := by
  exact
    ⟨rfl, rfl,
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta_pos,
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.minus_below,
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.plus_above⟩

/-! ## Expanded generic terminal -/

example
    {I : PhysicalIntervals}
    (K : PhysicalInterpolationTarget I)
    (physicalMeanError scale : Nat -> Real)
    (herror : physicalMeanError =O[atTop] scale)
    (hscale : Tendsto scale atTop (nhds 0)) :
    ∀ᶠ n : Nat in atTop,
      Real.log (I.upper .minus) ≤
          K.mu + physicalMeanError n - K.eta / 2 ∧
        K.mu + physicalMeanError n + K.eta / 2 ≤
          Real.log (I.lower .plus) := by
  exact
    eventually_bankPaperCanonicalSectionNinePostHeight_physicalMean_has_margin_of_error_isBigO
      K physicalMeanError scale herror hscale

/-! ## Expanded literal post-height terminal -/

example
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (herror :
      bankPaperCanonicalSmoothPhysicalMeanErrorFamily
          bankPaperCanonicalSectionNinePostHeightPhysicalMu
          logY Lambda0 mFrozen qTilde =O[atTop]
        (fun n => L n / secondOrderScale n)) :
    ∀ᶠ n : Nat in atTop,
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) ≤
        bankPaperCanonicalSmoothFinalActiveHeightFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen qTilde n /
            bankPaperCanonicalSmoothFinalActiveMassFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen qTilde n -
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
      bankPaperCanonicalSmoothFinalActiveHeightFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen qTilde n /
            bankPaperCanonicalSmoothFinalActiveMassFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen qTilde n +
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) := by
  exact
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin
      logY Lambda0 mFrozen qTilde herror

/-! ## Complete declaration census -/

#check bankPaperCanonicalSectionNinePostHeightPhysicalMu
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_minus
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_minus
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_plus
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_plus
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
#check bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
#check bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
#check bankPaperCanonicalSectionNinePostHeightPhysicalGap
#check bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos
#check bankPaperCanonicalSectionNinePostHeightPhysicalEta
#check bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
#check bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_minus_gap
#check bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_plus_gap
#check bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
#check bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_mu
#check bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_eta
#check bankPaperCanonical_L_div_secondOrderScale_tendsto_zero
#check
  eventually_bankPaperCanonicalSectionNinePostHeight_physicalMean_has_margin_of_error_isBigO
#check
  eventually_bankPaperCanonicalSectionNinePostHeight_fixedPhysicalMean_has_margin
#check
  eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin
#check
  eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin_of_analyticLedger

end

end Erdos390.WholePaper
