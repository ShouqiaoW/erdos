import Erdos390.WholePaper.BankPaperCanonicalRoughRowCorrection
import Erdos390.WholePaper.UpperScale
import Mathlib.Algebra.Order.Round

/-!
# The exact smooth-row quota and height ledger from Section 8

This file records the algebraic part of the paper's smooth-row initialization
without replacing any actual finite mass by an asymptotic main term.

The literal active base component is the constant weight `betaAct / L n` on
the head-free, `yNat n`-smooth part of the broad interval.  Its exact support
is the complete-rough row with label one.  The later definitions follow the
paper verbatim:

* `Q_sm(0)` is the nearest integer to `m_sm,fr + qTilde`, with a half-integer
  tie sent to the smaller integer;
* `q0 = Q_sm(0) - m_sm,fr`;
* `Q_sm(d) = Q_sm(0) - d` and `qAct(d) = q0 - d`;
* `A0 = logY - Lambda0 - q0 * L` and `A(d) = A0 + d * L`;
* `d` is the tie-lower nearest integer to
  `(mu * q0 - A0) / (L + mu)`.

All displayed identities and the two nearest-integer errors are unconditional.
The analytic comparison between the raw base mass and the actual post-guard
mass is deliberately left to the companion asymptotic module.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal rough smooth base component -/

/-- The paper's pre-guard active smooth support: the complete-rough row of
label one inside the head-free broad interval. -/
def bankPaperCanonicalRawSmoothBasePool
    (W n h K : Nat) : Finset Nat :=
  roughCanonicalBroadCorrectionPool W n h K (yNat n) 1

/-- The literal pointwise active base weight `betaAct / L n`, extended by
zero away from its finite support. -/
def bankPaperCanonicalRawSmoothBaseWeight
    (W n h K : Nat) (betaAct : Real) (a : Nat) : Real :=
  if a ∈ bankPaperCanonicalRawSmoothBasePool W n h K then
    betaAct / L n
  else 0

/-- Exact finite mass of the active smooth base component. -/
def bankPaperCanonicalRawSmoothBaseMass
    (W n h K : Nat) (betaAct : Real) : Real :=
  betaAct / L n *
    ((bankPaperCanonicalRawSmoothBasePool W n h K).card : Real)

/-- On its support, the separated base weight agrees with the broad part of
the repository's literal rough raw weight. -/
theorem bankPaperCanonicalRawSmoothBaseWeight_eq_roughRawWeight
    {W n h K a : Nat} {alpha betaAct : Real}
    (ha : a ∈ bankPaperCanonicalRawSmoothBasePool W n h K) :
    bankPaperCanonicalRawSmoothBaseWeight W n h K betaAct a =
      roughHeadCompatibleRawWeight W n h K alpha betaAct (L n) a := by
  rw [roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool ha]
  simp [bankPaperCanonicalRawSmoothBaseWeight, ha]

/-- Summing the literal constant base weight gives exactly the declared
finite mass. -/
theorem sum_bankPaperCanonicalRawSmoothBaseWeight
    (W n h K : Nat) (betaAct : Real) :
    (∑ a ∈ bankPaperCanonicalRawSmoothBasePool W n h K,
        bankPaperCanonicalRawSmoothBaseWeight W n h K betaAct a) =
      bankPaperCanonicalRawSmoothBaseMass W n h K betaAct := by
  calc
    (∑ a ∈ bankPaperCanonicalRawSmoothBasePool W n h K,
        bankPaperCanonicalRawSmoothBaseWeight W n h K betaAct a) =
        ∑ _a ∈ bankPaperCanonicalRawSmoothBasePool W n h K,
          betaAct / L n := by
      apply Finset.sum_congr rfl
      intro a ha
      simp [bankPaperCanonicalRawSmoothBaseWeight, ha]
    _ = bankPaperCanonicalRawSmoothBaseMass W n h K betaAct := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      unfold bankPaperCanonicalRawSmoothBaseMass
      ring

/-- Label one is intrinsically a complete-rough label at every cutoff. -/
theorem isCompleteRoughLabel_one (y : Nat) :
    IsCompleteRoughLabel y 1 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp
  simp at hp

/-- Exact reindexing of the label-one base pool as the head-free smooth
interval used in the paper's displayed mass formula. -/
theorem bankPaperCanonicalRawSmoothBasePool_card_eq_headFreeSmoothInterval
    (W n h K : Nat) :
    (bankPaperCanonicalRawSmoothBasePool W n h K).card =
      (roughHeadFreeSmoothInterval W n (2 * n - K * h) (yNat n)).card := by
  unfold bankPaperCanonicalRawSmoothBasePool
  unfold roughCanonicalBroadCorrectionPool roughBroadLowerBlock
  simpa using
    (completeRoughRowFiber_headFreeIoc_card_eq_headFreeSmoothInterval
      (W := W) (lo := n) (hi := 2 * n - K * h)
      (y := yNat n) (label := 1)
      (isCompleteRoughLabel_one (yNat n)) (by simp))

/-- The exact base mass after the row-to-smooth quotient reindexing. -/
theorem bankPaperCanonicalRawSmoothBaseMass_eq_headFreeSmoothInterval
    (W n h K : Nat) (betaAct : Real) :
    bankPaperCanonicalRawSmoothBaseMass W n h K betaAct =
      betaAct / L n *
        ((roughHeadFreeSmoothInterval W n (2 * n - K * h)
          (yNat n)).card : Real) := by
  unfold bankPaperCanonicalRawSmoothBaseMass
  rw [bankPaperCanonicalRawSmoothBasePool_card_eq_headFreeSmoothInterval]

/-! ## Tie-lower nearest integers -/

/-- Nearest-integer rounding with the paper's convention: an exact
half-integer is sent to the smaller integer. -/
def bankPaperNearestIntegerTieLower (x : Real) : Int :=
  ⌈x - 1 / 2⌉

/-- The half-open Voronoi cell characterizing tie-lower rounding.  The closed
right endpoint is exactly the smaller-integer tie convention. -/
theorem bankPaperNearestIntegerTieLower_eq_iff
    (x : Real) (k : Int) :
    bankPaperNearestIntegerTieLower x = k ↔
      (k : Real) - 1 / 2 < x ∧ x ≤ (k : Real) + 1 / 2 := by
  unfold bankPaperNearestIntegerTieLower
  rw [Int.ceil_eq_iff]
  constructor <;> rintro ⟨hleft, hright⟩ <;>
    constructor <;> linarith

/-- Integer inputs are fixed. -/
@[simp] theorem bankPaperNearestIntegerTieLower_intCast (k : Int) :
    bankPaperNearestIntegerTieLower (k : Real) = k := by
  apply (bankPaperNearestIntegerTieLower_eq_iff (k : Real) k).2
  constructor <;> linarith

/-- At a positive half tie the smaller adjacent integer is selected. -/
@[simp] theorem bankPaperNearestIntegerTieLower_add_half (k : Int) :
    bankPaperNearestIntegerTieLower ((k : Real) + 1 / 2) = k := by
  apply (bankPaperNearestIntegerTieLower_eq_iff
    ((k : Real) + 1 / 2) k).2
  constructor <;> linarith

/-- The universal half-unit rounding error. -/
theorem bankPaperNearestIntegerTieLower_abs_sub_le (x : Real) :
    |(bankPaperNearestIntegerTieLower x : Real) - x| ≤ 1 / 2 := by
  have hcell :=
    (bankPaperNearestIntegerTieLower_eq_iff x
      (bankPaperNearestIntegerTieLower x)).1 rfl
  apply abs_le.mpr
  constructor <;> linarith

/-! ## Exact smooth-row quota initialization -/

/-- `Q_sm(0)`, formed from the actual frozen and post-guard active masses. -/
def bankPaperCanonicalSmoothInitialQuota
    (mFrozen qTilde : Real) : Int :=
  bankPaperNearestIntegerTieLower (mFrozen + qTilde)

/-- `q0 = Q_sm(0) - m_sm,fr`; this is a real mass, not an integer. -/
def bankPaperCanonicalSmoothInitialActiveMass
    (mFrozen qTilde : Real) : Real :=
  (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) - mFrozen

/-- If the actual pre-initialization row mass is already an integer, the
nearest-integer initialization returns that exact integer. -/
theorem bankPaperCanonicalSmoothInitialQuota_eq_of_total_eq_intCast
    {mFrozen qTilde : Real} {Q : Int}
    (hQ : mFrozen + qTilde = (Q : Real)) :
    bankPaperCanonicalSmoothInitialQuota mFrozen qTilde = Q := by
  unfold bankPaperCanonicalSmoothInitialQuota
  rw [hQ, bankPaperNearestIntegerTieLower_intCast]

/-- Exact expression for the initialization error. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_sub_actual
    (mFrozen qTilde : Real) :
    bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde =
      (bankPaperCanonicalSmoothInitialQuota mFrozen qTilde : Real) -
        (mFrozen + qTilde) := by
  unfold bankPaperCanonicalSmoothInitialActiveMass
  ring

/-- The paper's literal bound `|q0 - qTilde| <= 1/2`. -/
theorem bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| ≤
      1 / 2 := by
  rw [bankPaperCanonicalSmoothInitialActiveMass_sub_actual]
  exact bankPaperNearestIntegerTieLower_abs_sub_le (mFrozen + qTilde)

/-- The integer total smooth-row quota `Q_sm(d) = Q_sm(0) - d`. -/
def bankPaperCanonicalSmoothQuotaAt
    (mFrozen qTilde : Real) (d : Int) : Int :=
  bankPaperCanonicalSmoothInitialQuota mFrozen qTilde - d

/-- The real active quota `qAct(d) = q0 - d`. -/
def bankPaperCanonicalSmoothActiveMassAt
    (mFrozen qTilde : Real) (d : Int) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - (d : Real)

/-- The displayed active-mass identity, retained under its paper name. -/
theorem bankPaperCanonicalSmoothActiveMassAt_eq_q0_sub
    (mFrozen qTilde : Real) (d : Int) :
    bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d =
      bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - (d : Real) :=
  rfl

/-- Exact total-row ledger before splitting the frozen contributions. -/
theorem bankPaperCanonicalSmoothQuotaAt_cast_eq_frozen_add_active
    (mFrozen qTilde : Real) (d : Int) :
    (bankPaperCanonicalSmoothQuotaAt mFrozen qTilde d : Real) =
      mFrozen + bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d := by
  unfold bankPaperCanonicalSmoothQuotaAt
  unfold bankPaperCanonicalSmoothActiveMassAt
  unfold bankPaperCanonicalSmoothInitialActiveMass
  push_cast
  ring

/-- The exact frozen remainder
`m_sm,oth = m_sm,fr - m_sm,fix - topMass - protectedMass`. -/
def bankPaperCanonicalSmoothOtherFrozenMass
    (mFrozen : Real) (mFix : Int)
    (topMass protectedMass : Real) : Real :=
  mFrozen - (mFix : Real) - topMass - protectedMass

/-- The integer flexible quota `Q_sm(d) - m_sm,fix`. -/
def bankPaperCanonicalSmoothFlexibleQuotaAt
    (mFrozen qTilde : Real) (mFix d : Int) : Int :=
  bankPaperCanonicalSmoothQuotaAt mFrozen qTilde d - mFix

/-- The paper's boxed smooth quota ledger, with the remainder defined from
the actual frozen mass rather than from a cardinality surrogate. -/
theorem bankPaperCanonicalSmoothQuotaAt_exact_ledger
    (mFrozen qTilde : Real) (mFix d : Int)
    (topMass protectedMass : Real) :
    (bankPaperCanonicalSmoothQuotaAt mFrozen qTilde d : Real) =
      (mFix : Real) + topMass + protectedMass +
        bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d +
        bankPaperCanonicalSmoothOtherFrozenMass
          mFrozen mFix topMass protectedMass := by
  rw [bankPaperCanonicalSmoothQuotaAt_cast_eq_frozen_add_active]
  unfold bankPaperCanonicalSmoothOtherFrozenMass
  ring

/-- Casting the integer flexible quota removes precisely `m_sm,fix` from
the boxed ledger. -/
theorem bankPaperCanonicalSmoothFlexibleQuotaAt_exact_ledger
    (mFrozen qTilde : Real) (mFix d : Int)
    (topMass protectedMass : Real) :
    (bankPaperCanonicalSmoothFlexibleQuotaAt
        mFrozen qTilde mFix d : Real) =
      topMass + protectedMass +
        bankPaperCanonicalSmoothActiveMassAt mFrozen qTilde d +
        bankPaperCanonicalSmoothOtherFrozenMass
          mFrozen mFix topMass protectedMass := by
  unfold bankPaperCanonicalSmoothFlexibleQuotaAt
  push_cast
  rw [bankPaperCanonicalSmoothQuotaAt_exact_ledger]
  unfold bankPaperCanonicalSmoothOtherFrozenMass
  ring

/-! ## Exact frozen-height ledger and centered adjustment -/

/-- `A0 = logY - Lambda0 - q0 * L`. -/
def bankPaperCanonicalSmoothFrozenHeightDefect
    (n : Nat) (logY Lambda0 q0 : Real) : Real :=
  logY - Lambda0 - q0 * L n

/-- The active height after an arbitrary integer change `d`. -/
def bankPaperCanonicalSmoothActiveHeightAt
    (n : Nat) (logY Lambda0 q0 : Real) (d : Int) : Real :=
  logY - Lambda0 - (q0 - (d : Real)) * L n

/-- The exact identity `A(d) = A0 + d L`. -/
theorem bankPaperCanonicalSmoothActiveHeightAt_eq_defect_add
    (n : Nat) (logY Lambda0 q0 : Real) (d : Int) :
    bankPaperCanonicalSmoothActiveHeightAt n logY Lambda0 q0 d =
      bankPaperCanonicalSmoothFrozenHeightDefect n logY Lambda0 q0 +
        (d : Real) * L n := by
  unfold bankPaperCanonicalSmoothActiveHeightAt
  unfold bankPaperCanonicalSmoothFrozenHeightDefect
  ring

/-- The real height center `dStar = (mu q0 - A0) / (L + mu)`. -/
def bankPaperCanonicalSmoothHeightCenter
    (n : Nat) (mu q0 A0 : Real) : Real :=
  (mu * q0 - A0) / (L n + mu)

/-- The paper's integer height adjustment, with the same tie-lower rule as
the initial quota. -/
def bankPaperCanonicalSmoothHeightAdjustment
    (n : Nat) (mu q0 A0 : Real) : Int :=
  bankPaperNearestIntegerTieLower
    (bankPaperCanonicalSmoothHeightCenter n mu q0 A0)

/-- The rounded height adjustment is within one half of `dStar`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
    (n : Nat) (mu q0 A0 : Real) :
    |(bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu q0 A0| ≤ 1 / 2 :=
  bankPaperNearestIntegerTieLower_abs_sub_le
    (bankPaperCanonicalSmoothHeightCenter n mu q0 A0)

/-- The final active mass obtained from the height-centered integer. -/
def bankPaperCanonicalSmoothHeightAdjustedActiveMass
    (n : Nat) (mu q0 A0 : Real) : Real :=
  q0 - (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real)

/-- Literal `activeMass = q0 - d` for the constructed height adjustment. -/
theorem bankPaperCanonicalSmoothHeightAdjustedActiveMass_eq_q0_sub_d
    (n : Nat) (mu q0 A0 : Real) :
    bankPaperCanonicalSmoothHeightAdjustedActiveMass n mu q0 A0 =
      q0 - (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) :=
  rfl

/-- Before rounding, `dStar` centers the active component exactly.  After
rounding, the entire residual is the rounding error times `L + mu`. -/
theorem bankPaperCanonicalSmoothHeightCenter_exact_residual
    (n : Nat) (mu q0 A0 : Real) (d : Int)
    (hdenom : L n + mu ≠ 0) :
    A0 + (d : Real) * L n - mu * (q0 - (d : Real)) =
      ((d : Real) - bankPaperCanonicalSmoothHeightCenter n mu q0 A0) *
        (L n + mu) := by
  unfold bankPaperCanonicalSmoothHeightCenter
  rw [sub_mul, div_mul_cancel₀ _ hdenom]
  ring

/-- Hence the constructed integer has centered-height residual at most
`|L + mu| / 2`. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_centered_residual_bound
    (n : Nat) (mu q0 A0 : Real)
    (hdenom : L n + mu ≠ 0) :
    |A0 + (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) *
          L n -
        mu * (q0 -
          (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real))| ≤
      (1 / 2) * |L n + mu| := by
  rw [bankPaperCanonicalSmoothHeightCenter_exact_residual
    n mu q0 A0 (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0)
      hdenom, abs_mul]
  exact mul_le_mul_of_nonneg_right
    (bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
      n mu q0 A0) (abs_nonneg _)

/-- Exact mean error after division by a nonzero remaining active mass. -/
theorem bankPaperCanonicalSmoothHeightCenter_exact_mean_error
    (n : Nat) (mu q0 A0 : Real) (d : Int)
    (hdenom : L n + mu ≠ 0) (hmass : q0 - (d : Real) ≠ 0) :
    (A0 + (d : Real) * L n) / (q0 - (d : Real)) - mu =
      (((d : Real) - bankPaperCanonicalSmoothHeightCenter n mu q0 A0) *
        (L n + mu)) / (q0 - (d : Real)) := by
  have hres := bankPaperCanonicalSmoothHeightCenter_exact_residual
    n mu q0 A0 d hdenom
  calc
    (A0 + (d : Real) * L n) / (q0 - (d : Real)) - mu =
        (A0 + (d : Real) * L n -
          mu * (q0 - (d : Real))) / (q0 - (d : Real)) := by
      field_simp [hmass]
    _ = (((d : Real) -
          bankPaperCanonicalSmoothHeightCenter n mu q0 A0) *
        (L n + mu)) / (q0 - (d : Real)) := by
      rw [hres]

/-- With positive remaining active mass, the mean error is bounded by the
half-unit rounding error divided by that mass. -/
theorem bankPaperCanonicalSmoothHeightAdjustment_mean_error_bound
    (n : Nat) (mu q0 A0 : Real)
    (hdenom : L n + mu ≠ 0)
    (hmass : 0 < q0 -
      (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real)) :
    |(A0 +
          (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) *
            L n) /
          (q0 -
            (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real)) -
        mu| <=
      ((1 / 2) * |L n + mu|) /
        (q0 -
          (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real)) := by
  rw [bankPaperCanonicalSmoothHeightCenter_exact_mean_error n mu q0 A0
    (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0)
      hdenom hmass.ne', abs_div, abs_mul, abs_of_pos hmass]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
        n mu q0 A0) (abs_nonneg _)) hmass.le

/-- Specialization of the exact residual identity to the frozen ledger's
literal `A0`. -/
theorem bankPaperCanonicalSmoothActiveHeight_centered_residual
    (n : Nat) (mu logY Lambda0 q0 : Real) (d : Int)
    (hdenom : L n + mu ≠ 0) :
    bankPaperCanonicalSmoothActiveHeightAt n logY Lambda0 q0 d -
        mu * (q0 - (d : Real)) =
      ((d : Real) - bankPaperCanonicalSmoothHeightCenter n mu
          q0 (bankPaperCanonicalSmoothFrozenHeightDefect
            n logY Lambda0 q0)) * (L n + mu) := by
  rw [bankPaperCanonicalSmoothActiveHeightAt_eq_defect_add]
  exact bankPaperCanonicalSmoothHeightCenter_exact_residual
    n mu q0 (bankPaperCanonicalSmoothFrozenHeightDefect
      n logY Lambda0 q0) d hdenom

/-! ## Literal Section 8 families -/

/-- The paper's varying initial active mass `q0(n)`, built from the actual
frozen and post-guard mass families. -/
def bankPaperCanonicalSmoothQ0Family
    (mFrozen qTilde : Nat -> Real) (n : Nat) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass (mFrozen n) (qTilde n)

/-- The varying frozen height defect formed from the literal `q0` family. -/
def bankPaperCanonicalSmoothA0Family
    (logY Lambda0 mFrozen qTilde : Nat -> Real) (n : Nat) : Real :=
  bankPaperCanonicalSmoothFrozenHeightDefect n (logY n) (Lambda0 n)
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)

/-- The paper's varying real center `dStar(n)`. -/
def bankPaperCanonicalSmoothDStarFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothHeightCenter n mu
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde n)

/-- The literal integer height-adjustment family `d(n)`. -/
def bankPaperCanonicalSmoothDIntFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Int :=
  bankPaperCanonicalSmoothHeightAdjustment n mu
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde n)

/-- The same integer adjustment viewed as a real function for asymptotic
notation. -/
def bankPaperCanonicalSmoothDRealFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  (bankPaperCanonicalSmoothDIntFamily mu logY Lambda0 mFrozen qTilde n : Real)

/-- The final Section 8 active-mass family `qAct(d)`. -/
def bankPaperCanonicalSmoothFinalActiveMassFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
    bankPaperCanonicalSmoothDRealFamily mu logY Lambda0 mFrozen qTilde n

/-- The literal remaining active height after applying the integer family
`d(n)`. -/
def bankPaperCanonicalSmoothFinalActiveHeightFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothActiveHeightAt n (logY n) (Lambda0 n)
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothDIntFamily
      mu logY Lambda0 mFrozen qTilde n)

/-- The centered physical-mean error from the paper's display. -/
def bankPaperCanonicalSmoothPhysicalMeanErrorFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSmoothFinalActiveHeightFamily
      mu logY Lambda0 mFrozen qTilde n /
    bankPaperCanonicalSmoothFinalActiveMassFamily
      mu logY Lambda0 mFrozen qTilde n - mu

/-- The family-level exact identity `qAct(d) = q0 - d`. -/
theorem bankPaperCanonicalSmoothFinalActiveMassFamily_eq_q0_sub_d
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real) (n : Nat) :
    bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n =
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde n :=
  rfl

/-- Family-level half-unit initialization error. -/
theorem bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
    (mFrozen qTilde : Nat -> Real) (n : Nat) :
    |bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - qTilde n| <=
      1 / 2 :=
  bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    (mFrozen n) (qTilde n)

/-- Family-level half-unit height-adjustment error. -/
theorem bankPaperCanonicalSmoothDRealFamily_abs_sub_dStar_le
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real) (n : Nat) :
    |bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde n -
        bankPaperCanonicalSmoothDStarFamily
          mu logY Lambda0 mFrozen qTilde n| <= 1 / 2 :=
  bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le n mu
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde n)

/-- Pointwise physical-mean error bound for the literal Section 8 families. -/
theorem bankPaperCanonicalSmoothPhysicalMeanErrorFamily_bound
    {mu : Real} (logY Lambda0 mFrozen qTilde : Nat -> Real) (n : Nat)
    (hdenom : L n + mu ≠ 0)
    (hmass : 0 < bankPaperCanonicalSmoothFinalActiveMassFamily
      mu logY Lambda0 mFrozen qTilde n) :
    |bankPaperCanonicalSmoothPhysicalMeanErrorFamily
        mu logY Lambda0 mFrozen qTilde n| <=
      ((1 / 2) * |L n + mu|) /
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde n := by
  unfold bankPaperCanonicalSmoothPhysicalMeanErrorFamily
  unfold bankPaperCanonicalSmoothFinalActiveHeightFamily
  rw [bankPaperCanonicalSmoothActiveHeightAt_eq_defect_add]
  exact bankPaperCanonicalSmoothHeightAdjustment_mean_error_bound n mu
    (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
    (bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde n)
    hdenom hmass

end

end Erdos390.WholePaper
