import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic

/-!
# The explicit post-height physical margin

This file fixes one completely explicit pair of paper-valid physical
intervals around

`mu = log (3 / 2)`.

The minus pool is `[1, 4 / 3]` and the plus pool is
`[5 / 3, 7 / 4]`.  Thus both pools lie in the paper's physical range
`[1, 2]`, and there is a fixed logarithmic gap on either side of `mu`.

The analytic input is kept transparent.  A generic lemma says that an
error which is `O(scale)` tends to zero whenever `scale` does, and hence
the corresponding centered mean eventually retains half of any fixed
`PhysicalInterpolationTarget` margin.  It is then applied to the literal
post-height physical-mean error and the paper's scale

`L / N`, where `N = secondOrderScale = n / L`.

No target/source wrapper and no conclusion-bearing premise is introduced.
-/

open Filter Topology Set Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Explicit paper-valid physical data -/

/-- The fixed logarithmic center used for the two physical pools. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalMu : Real :=
  Real.log ((3 : Real) / 2)

/-- Two explicit separated physical intervals contained in `[1, 2]`. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalIntervals :
    PhysicalIntervals where
  lower
    | .minus => 1
    | .plus => (5 : Real) / 3
  upper
    | .minus => (4 : Real) / 3
    | .plus => (7 : Real) / 4
  lower_pos := by
    intro sigma
    cases sigma <;> norm_num
  lower_lt_upper := by
    intro sigma
    cases sigma <;> norm_num
  separated := by
    norm_num

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_minus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower .minus =
      1 := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_minus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper .minus =
      (4 : Real) / 3 := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_plus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower .plus =
      (5 : Real) / 3 := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_plus :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper .plus =
      (7 : Real) / 4 := rfl

/-- The explicit intervals satisfy the lower endpoint restriction used by
the canonical guarded sample. -/
theorem bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
    (sigma : PhysicalSign) :
    1 ≤ bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
      sigma := by
  cases sigma <;> norm_num

/-- The explicit intervals satisfy the upper endpoint restriction used by
the canonical guarded sample. -/
theorem bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
    (sigma : PhysicalSign) :
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper sigma ≤
      2 := by
  cases sigma <;> norm_num

theorem bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos :
    0 < bankPaperCanonicalSectionNinePostHeightPhysicalMu := by
  unfold bankPaperCanonicalSectionNinePostHeightPhysicalMu
  exact Real.log_pos (by norm_num)

/-- The smaller of the two logarithmic gaps around the fixed center. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalGap : Real :=
  min
    (bankPaperCanonicalSectionNinePostHeightPhysicalMu -
      Real.log
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
          .minus))
    (Real.log
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
          .plus) -
      bankPaperCanonicalSectionNinePostHeightPhysicalMu)

theorem bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos :
    0 < bankPaperCanonicalSectionNinePostHeightPhysicalGap := by
  unfold bankPaperCanonicalSectionNinePostHeightPhysicalGap
  apply lt_min
  · apply sub_pos.mpr
    change
      Real.log ((4 : Real) / 3) <
        Real.log ((3 : Real) / 2)
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  · apply sub_pos.mpr
    change
      Real.log ((3 : Real) / 2) <
        Real.log ((5 : Real) / 3)
    exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)

/-- A fixed positive margin, chosen as half of the smaller endpoint gap. -/
def bankPaperCanonicalSectionNinePostHeightPhysicalEta : Real :=
  bankPaperCanonicalSectionNinePostHeightPhysicalGap / 2

theorem bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos :
    0 < bankPaperCanonicalSectionNinePostHeightPhysicalEta := by
  exact div_pos
    bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos (by norm_num)

theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_minus_gap :
    bankPaperCanonicalSectionNinePostHeightPhysicalEta ≤
      bankPaperCanonicalSectionNinePostHeightPhysicalMu -
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) := by
  calc
    bankPaperCanonicalSectionNinePostHeightPhysicalEta =
        bankPaperCanonicalSectionNinePostHeightPhysicalGap / 2 := rfl
    _ ≤ bankPaperCanonicalSectionNinePostHeightPhysicalGap := by
      linarith [bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos]
    _ ≤ bankPaperCanonicalSectionNinePostHeightPhysicalMu -
          Real.log
            (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
              .minus) := by
      unfold bankPaperCanonicalSectionNinePostHeightPhysicalGap
      exact min_le_left _ _

theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_plus_gap :
    bankPaperCanonicalSectionNinePostHeightPhysicalEta ≤
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) -
        bankPaperCanonicalSectionNinePostHeightPhysicalMu := by
  calc
    bankPaperCanonicalSectionNinePostHeightPhysicalEta =
        bankPaperCanonicalSectionNinePostHeightPhysicalGap / 2 := rfl
    _ ≤ bankPaperCanonicalSectionNinePostHeightPhysicalGap := by
      linarith [bankPaperCanonicalSectionNinePostHeightPhysicalGap_pos]
    _ ≤ Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) -
          bankPaperCanonicalSectionNinePostHeightPhysicalMu := by
      unfold bankPaperCanonicalSectionNinePostHeightPhysicalGap
      exact min_le_right _ _

/-- The explicit, fixed physical interpolation target. -/
def bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget :
    PhysicalInterpolationTarget
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals where
  mu := bankPaperCanonicalSectionNinePostHeightPhysicalMu
  eta := bankPaperCanonicalSectionNinePostHeightPhysicalEta
  eta_pos := bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
  minus_below := by
    linarith [
      bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_minus_gap]
  plus_above := by
    linarith [
      bankPaperCanonicalSectionNinePostHeightPhysicalEta_le_plus_gap]

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_mu :
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.mu =
      bankPaperCanonicalSectionNinePostHeightPhysicalMu := rfl

@[simp] theorem
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_eta :
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.eta =
      bankPaperCanonicalSectionNinePostHeightPhysicalEta := rfl

/-! ## The elementary asymptotic margin algebra -/

/-- The paper's physical error scale `L / N` tends to zero. -/
theorem bankPaperCanonical_L_div_secondOrderScale_tendsto_zero :
    Tendsto (fun n : Nat => L n / secondOrderScale n)
      atTop (nhds 0) := by
  have hzero :
      Tendsto (fun n : Nat => L n ^ 2 / (n : Real))
        atTop (nhds 0) := by
    simpa only [L, Function.comp_apply, id_eq] using
      ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := Real))).tendsto_div_nhds_zero
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hL : L n ≠ 0 := (L_pos hn).ne'
  have hnReal : (n : Real) ≠ 0 := by
    positivity
  change
    L n ^ 2 / (n : Real) =
      L n / ((n : Real) / L n)
  field_simp [hL, hnReal]

/-- Generic margin algebra: an `O(scale)` centered error tends to zero when
`scale` does, so the associated mean eventually retains half of the fixed
interpolation margin. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_physicalMean_has_margin_of_error_isBigO
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
  have herrorZero : Tendsto physicalMeanError atTop (nhds 0) :=
    herror.trans_tendsto hscale
  have hsmall :
      ∀ᶠ n : Nat in atTop,
        physicalMeanError n ∈ Set.Ioo (-K.eta / 2) (K.eta / 2) := by
    apply herrorZero.eventually
    exact Ioo_mem_nhds
      (by linarith [K.eta_pos])
      (by linarith [K.eta_pos])
  filter_upwards [hsmall] with n hn
  constructor
  · linarith [K.minus_below, hn.1]
  · linarith [K.plus_above, hn.2]

/-- Specialization of the generic margin lemma to the fixed paper data and
the scale `L / secondOrderScale`. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_fixedPhysicalMean_has_margin
    (physicalMeanError : Nat -> Real)
    (herror : physicalMeanError =O[atTop]
      (fun n => L n / secondOrderScale n)) :
    ∀ᶠ n : Nat in atTop,
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) ≤
        bankPaperCanonicalSectionNinePostHeightPhysicalMu +
            physicalMeanError n -
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
      bankPaperCanonicalSectionNinePostHeightPhysicalMu +
            physicalMeanError n +
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus) := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_mu,
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget_eta] using
    (eventually_bankPaperCanonicalSectionNinePostHeight_physicalMean_has_margin_of_error_isBigO
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
      physicalMeanError (fun n => L n / secondOrderScale n) herror
      bankPaperCanonical_L_div_secondOrderScale_tendsto_zero)

/-! ## The literal post-height physical mean -/

/-- The literal post-height height-to-mass ratio eventually lies strictly
inside the two logarithmic endpoints with the same fixed positive margin. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin
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
  have hfixed :=
    eventually_bankPaperCanonicalSectionNinePostHeight_fixedPhysicalMean_has_margin
      (bankPaperCanonicalSmoothPhysicalMeanErrorFamily
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        logY Lambda0 mFrozen qTilde)
      herror
  filter_upwards [hfixed] with n hn
  constructor
  · calc
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) ≤
          bankPaperCanonicalSectionNinePostHeightPhysicalMu +
              bankPaperCanonicalSmoothPhysicalMeanErrorFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n -
            bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 :=
        hn.1
      _ =
          bankPaperCanonicalSmoothFinalActiveHeightFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n /
              bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n -
            bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 := by
        unfold bankPaperCanonicalSmoothPhysicalMeanErrorFamily
        ring
  · calc
      bankPaperCanonicalSmoothFinalActiveHeightFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen qTilde n /
            bankPaperCanonicalSmoothFinalActiveMassFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen qTilde n +
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 =
        bankPaperCanonicalSectionNinePostHeightPhysicalMu +
              bankPaperCanonicalSmoothPhysicalMeanErrorFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n +
            bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 := by
        unfold bankPaperCanonicalSmoothPhysicalMeanErrorFamily
        ring
      _ ≤
          Real.log
            (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
              .plus) :=
        hn.2

/-- Direct Section 8 specialization: its proved `O(L / N)` physical error
supplies the fixed post-height margin. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin_of_analyticLedger
    (W K : Nat) {c betaAct : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
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
  apply
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin
  exact
    bankPaperCanonicalSectionEight_physicalMeanError_isBigO
      W K hc hbeta
        bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      logY Lambda0 mFrozen qTilde Hledger

end

end Erdos390.WholePaper
