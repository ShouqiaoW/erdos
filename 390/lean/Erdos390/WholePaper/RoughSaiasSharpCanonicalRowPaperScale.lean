import Erdos390.WholePaper.RoughSaiasSharpFixedHeadIntervalShift
import Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic

/-!
# Canonical sharp Saias row-scale geometry

This file specializes the closed sharp endpoint and fixed-head estimates to
the paper's literal balanced raw point.  The high-block multiplicity is
written as `K0 + 1`, so its positivity is built into the data rather than
assumed separately.
-/

open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Uniform control of the literal balanced coefficient -/

/-- The fixed head density is at most one. -/
theorem roughHeadDensity_le_one (W : ℕ) :
    roughHeadDensity W ≤ 1 := by
  have hmod : (0 : ℝ) < (roughHeadModulus W : ℝ) := by
    exact_mod_cast roughHeadModulus_pos W
  have htot :
      ((roughHeadModulus W).totient : ℝ) ≤
        (roughHeadModulus W : ℝ) := by
    exact_mod_cast Nat.totient_le (roughHeadModulus W)
  unfold roughHeadDensity
  exact (div_le_one hmod).2 htot

/-- A lower bound for the integral tail gives a constant bound for the
balanced high-block coefficient. -/
theorem roughHeadBalancedAlpha_abs_le_of_tail_lower
    {W n h K : ℕ} {beta L c : ℝ}
    (hc : 0 < c) (hn : 0 < n) (hK : 0 < K) (hL : 0 < L)
    (htail : c * (n : ℝ) / L ≤ (h : ℝ)) :
    |roughHeadBalancedAlpha W n h K beta L| ≤
      1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
  have hdelta : 0 < roughHeadDensity W := roughHeadDensity_pos W
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have htailPos : 0 < c * (n : ℝ) / L := by positivity
  have hhReal : (0 : ℝ) < (h : ℝ) := htailPos.trans_le htail
  have hden :
      0 < (K : ℝ) * (h : ℝ) := mul_pos hKReal hhReal
  have hsubCast :
      (((n - K * h : ℕ) : ℝ)) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hsubCastNonneg :
      (0 : ℝ) ≤ (((n - K * h : ℕ) : ℝ)) := by
    positivity
  have hnum :
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
    calc
      |(h : ℝ) / roughHeadDensity W -
          (beta / L) * (((n - K * h : ℕ) : ℝ))| ≤
        |(h : ℝ) / roughHeadDensity W| +
          |(beta / L) * (((n - K * h : ℕ) : ℝ))| :=
        abs_sub _ _
      _ = (h : ℝ) / roughHeadDensity W +
          (|beta| / L) * (((n - K * h : ℕ) : ℝ)) := by
        rw [abs_div, abs_of_pos hdelta, abs_of_nonneg hhReal.le,
          abs_mul, abs_div, abs_of_pos hL,
          abs_of_nonneg hsubCastNonneg]
      _ ≤ (h : ℝ) / roughHeadDensity W +
          |beta| / L * (n : ℝ) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hsubCast
            (div_nonneg (abs_nonneg beta) hL.le))
  have hcross : c * (n : ℝ) ≤ (h : ℝ) * L := by
    have := (div_le_iff₀ hL).mp htail
    simpa only [mul_comm] using this
  have hnDiv : (n : ℝ) ≤ ((h : ℝ) * L) / c :=
    (le_div_iff₀ hc).2 (by
      calc
        (n : ℝ) * c = c * (n : ℝ) := by ring
        _ ≤ (h : ℝ) * L := hcross)
  have hratio :
      (n : ℝ) / ((h : ℝ) * L) ≤ 1 / c := by
    calc
      (n : ℝ) / ((h : ℝ) * L) ≤
          (((h : ℝ) * L) / c) / ((h : ℝ) * L) :=
        div_le_div_of_nonneg_right hnDiv
          (mul_nonneg hhReal.le hL.le)
      _ = 1 / c := by field_simp
  unfold roughHeadBalancedAlpha
  norm_num only [Nat.cast_mul]
  rw [abs_div, abs_of_pos hden]
  calc
    |(h : ℝ) / roughHeadDensity W -
        (beta / L) * (((n - K * h : ℕ) : ℝ))| /
          ((K : ℝ) * (h : ℝ)) ≤
      ((h : ℝ) / roughHeadDensity W +
        |beta| / L * (n : ℝ)) /
          ((K : ℝ) * (h : ℝ)) :=
        (div_le_div_iff_of_pos_right hden).2 hnum
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) *
          ((n : ℝ) / ((h : ℝ) * L)) := by
      field_simp [hdelta.ne', hKReal.ne', hhReal.ne', hL.ne']
    _ ≤ 1 / ((K : ℝ) * roughHeadDensity W) +
        (|beta| / (K : ℝ)) * (1 / c) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hratio
          (div_nonneg (abs_nonneg beta) hKReal.le))
    _ = 1 / ((K : ℝ) * roughHeadDensity W) +
        |beta| / ((K : ℝ) * c) := by
      field_simp [hKReal.ne', hc.ne']

/-- With the paper tail and the positive multiplicity `K0+1`, the
balanced coefficient is uniformly bounded by a constant chosen before
`n`. -/
theorem roughHeadBalancedAlpha_succ_abs_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n : ℕ} (hn : 2 ≤ n) :
    |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n)| ≤
      1 / (((K0 + 1 : ℕ) : ℝ) * roughHeadDensity W) +
        |beta| / (((K0 + 1 : ℕ) : ℝ) * c) := by
  have hL : 0 < L n := L_pos (by omega)
  have htail :
      c * (n : ℝ) / L n ≤ (upperTailLength c n : ℝ) := by
    rw [upperTailLength]
    calc
      c * (n : ℝ) / L n = c * secondOrderScale n := by
        unfold secondOrderScale L
        ring
      _ ≤ (Nat.ceil (c * secondOrderScale n) : ℝ) :=
        Nat.le_ceil (c * secondOrderScale n)
  exact roughHeadBalancedAlpha_abs_le_of_tail_lower
    hc (by omega) (by omega) hL htail

/-! ## Fixed constants for the three row ledgers -/

/-- The uniform bound for the literal balanced coefficient when the high
block multiplicity is written as `K0 + 1`. -/
noncomputable def roughBalancedAlphaConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  1 / (((K0 + 1 : ℕ) : ℝ) * roughHeadDensity W) +
    |beta| / (((K0 + 1 : ℕ) : ℝ) * c)

theorem roughBalancedAlphaConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughBalancedAlphaConstant W K0 c beta := by
  unfold roughBalancedAlphaConstant
  have hK : (0 : ℝ) <
      (((K0 + 1 : ℕ) : ℝ)) := by positivity
  have hdelta : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  positivity

/-- A fixed coefficient paying the Dickman displacement ledger and its
four quotient-floor errors. -/
noncomputable def roughCanonicalSharpMainRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  (30 * c + 15) +
    (roughBalancedAlphaConstant W K0 c beta + |beta|) *
      (10 * (((K0 + 1 : ℕ) : ℝ)) * c + 5) +
    10 * |beta| +
    (2 + 2 * roughBalancedAlphaConstant W K0 c beta +
      2 * |beta|)

/-- A fixed coefficient paying the three weighted sharp Saias pair
budgets.  The broad pair already carries its defining `beta/L` factor. -/
noncomputable def roughCanonicalSharpTransitionRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  (3000 * roughSaiasSharpDefectConstant + 50 * c + 25) +
    roughBalancedAlphaConstant W K0 c beta *
      (1500 * roughSaiasSharpDefectConstant +
        50 * (((K0 + 1 : ℕ) : ℝ)) * c + 25) +
    |beta| * (1000 * roughSaiasSharpDefectConstant + 75)

/-- The coefficient attached to one fixed head divisor.  It pays both
sharp interval branches as well as the bounded small-row branch. -/
noncomputable def roughCanonicalSharpHeadDivisorRowScaleConstant
    (W K0 d : ℕ) (c beta : ℝ) : ℝ :=
  roughBalancedAlphaConstant W K0 c beta *
      (31 +
        (Real.log (d : ℝ) + 12) / (d : ℝ) *
          (10 * (((K0 + 1 : ℕ) : ℝ)) * c + 5) +
        3000 * roughSaiasSharpDefectConstant / (d : ℝ)) +
    |beta| *
      (31 + 10 * (Real.log (d : ℝ) + 12) / (d : ℝ) +
        2000 * roughSaiasSharpDefectConstant / (d : ℝ)) +
    4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)

/-- The fixed-head divisor sum is finite before `n` is chosen, hence gives
one honest constant depending only on the fixed paper parameters. -/
noncomputable def roughCanonicalSharpHeadRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  ∑ d ∈ (roughHeadModulus W).divisors,
    |(ArithmeticFunction.moebius d : ℝ)| *
      roughCanonicalSharpHeadDivisorRowScaleConstant W K0 d c beta

/-- One fixed constant which simultaneously dominates the main,
transition, and fixed-head row ledgers. -/
noncomputable def roughCanonicalSharpUnifiedRowScaleConstant
    (W K0 : ℕ) (c beta : ℝ) : ℝ :=
  roughCanonicalSharpMainRowScaleConstant W K0 c beta +
    roughCanonicalSharpTransitionRowScaleConstant W K0 c beta +
    roughCanonicalSharpHeadRowScaleConstant W K0 c beta

/-! ## Quotient and logarithmic geometry -/

/-- A natural quotient differs from the corresponding real quotient by
strictly less than one. -/
theorem roughNatQuotient_sub_realQuotient_abs_lt_one
    {N r : ℕ} (hr : 0 < r) :
    |(((N / r : ℕ) : ℝ)) - (N : ℝ) / (r : ℝ)| < 1 := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hle :
      (((N / r : ℕ) : ℝ)) ≤ (N : ℝ) / (r : ℝ) :=
    Nat.cast_div_le
  rw [abs_of_nonpos (sub_nonpos.mpr hle), neg_sub]
  have hdecomp :=
    congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.div_add_mod N r)
  norm_num only [Nat.cast_add, Nat.cast_mul] at hdecomp
  have hmod : (((N % r : ℕ) : ℝ)) < (r : ℝ) := by
    exact_mod_cast Nat.mod_lt N hr
  calc
    (N : ℝ) / (r : ℝ) - ((N / r : ℕ) : ℝ) =
        ((N % r : ℕ) : ℝ) / (r : ℝ) := by
      field_simp [hrReal.ne']
      nlinarith
    _ < 1 := (div_lt_one hrReal).2 hmod

/-- The real quotient lies below the natural quotient plus one. -/
theorem roughRealQuotient_lt_natQuotient_add_one
    {N r : ℕ} (hr : 0 < r) :
    (N : ℝ) / (r : ℝ) < ((N / r : ℕ) : ℝ) + 1 := by
  have hfloor :=
    roughNatQuotient_sub_realQuotient_abs_lt_one
      (N := N) hr
  rw [abs_lt] at hfloor
  linarith

/-- The length of a quotient interval is bounded by its real length plus
one. -/
theorem roughQuotientGap_cast_le
    {A B r : ℕ} (hr : 0 < r) (hAB : A ≤ B) :
    (((B / r - A / r : ℕ) : ℝ)) ≤
      (((B - A : ℕ) : ℝ)) / (r : ℝ) + 1 := by
  have hfloor :=
    quotientIocLength_sub_realLengthDiv_abs_lt_one hr hAB
  rw [abs_lt] at hfloor
  linarith

/-- For an active row, the doubled quotient is at most three times the
half-scale quotient. -/
theorem roughTwoQuotient_le_three_halfQuotient
    {n r : ℕ} (hr : 0 < r) (hrn : r ≤ n) :
    (2 * n) / r ≤ 3 * (n / r) := by
  have hx : 0 < n / r := Nat.div_pos hrn hr
  have htwo :
      (2 * n) / r ≤ 2 * (n / r) + 1 := by
    have hadd :
        (n + n) / r ≤ n / r + n / r + 1 := by
      rw [Nat.add_div hr]
      split_ifs <;> omega
    simpa only [two_mul] using hadd
  omega

/-- If the upper tail is no longer than `n`, its quotient endpoint is at
most three times the central quotient endpoint. -/
theorem roughUpperQuotient_le_three_centralQuotient
    {n h r : ℕ} (hr : 0 < r) (hrn : r ≤ n) (hh : h ≤ n) :
    (2 * n + h) / r ≤ 3 * ((2 * n) / r) := by
  let X := (2 * n) / r
  have hdecomp := Nat.div_add_mod (2 * n) r
  have hmod := Nat.mod_lt (2 * n) hr
  have hXr : n ≤ X * r := by
    have hdecompX :
        X * r + (2 * n) % r = 2 * n := by
      simpa only [X, Nat.mul_comm] using hdecomp
    have hremLe : (2 * n) % r ≤ n :=
      (Nat.le_of_lt hmod).trans hrn
    omega
  have hnum : 2 * n + h ≤ (3 * X) * r := by
    nlinarith
  have hlt : 2 * n + h < (3 * X + 1) * r := by
    nlinarith
  have hquot :
      (2 * n + h) / r < 3 * X + 1 :=
    (Nat.div_lt_iff_lt_mul hr).2 hlt
  dsimp only [X] at hquot ⊢
  omega

/-- Multiplying a logarithmic displacement by its lower endpoint costs at
most the endpoint gap. -/
theorem roughLowerEndpoint_mul_logRatio_le_gap
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    A * (Real.log B - Real.log A) ≤ B - A := by
  have hB : 0 < B := hA.trans_le hAB
  have hratio : 0 < B / A := div_pos hB hA
  have hlog :=
    Real.log_le_sub_one_of_pos hratio
  have hlogDiv :
      Real.log (B / A) = Real.log B - Real.log A := by
    rw [Real.log_div hB.ne' hA.ne']
  calc
    A * (Real.log B - Real.log A) =
        A * Real.log (B / A) := by rw [hlogDiv]
    _ ≤ A * (B / A - 1) :=
      mul_le_mul_of_nonneg_left hlog hA.le
    _ = B - A := by field_simp [hA.ne']

/-- If the upper endpoint is at most three times the lower endpoint, the
same estimate with the upper endpoint costs only a factor three. -/
theorem roughUpperEndpoint_mul_logRatio_le_three_gap
    {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hBA : B ≤ 3 * A) :
    B * (Real.log B - Real.log A) ≤ 3 * (B - A) := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogNonneg :
      0 ≤ Real.log B - Real.log A := by
    exact sub_nonneg.mpr
      (Real.log_le_log hA hAB)
  calc
    B * (Real.log B - Real.log A) ≤
        (3 * A) * (Real.log B - Real.log A) :=
      mul_le_mul_of_nonneg_right hBA hlogNonneg
    _ = 3 * (A * (Real.log B - Real.log A)) := by ring
    _ ≤ 3 * (B - A) := by
      exact mul_le_mul_of_nonneg_left
        (roughLowerEndpoint_mul_logRatio_le_gap hA hAB)
        (by norm_num)

theorem roughDickmanUpperWeightedDisplacement_le_three_gap
    {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hBA : B ≤ 3 * A) (hy : 2 ≤ y) :
    (B : ℝ) *
        |FriableAsymptotic.dickmanU B y -
          FriableAsymptotic.dickmanU A y| ≤
      3 * (((B - A : ℕ) : ℝ)) / Real.log (y : ℝ) := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogDiff :
      0 ≤ Real.log (B : ℝ) - Real.log (A : ℝ) := by
    exact sub_nonneg.mpr
      (Real.log_le_log (by exact_mod_cast hA)
        (by exact_mod_cast hAB))
  have hu :
      |FriableAsymptotic.dickmanU B y -
          FriableAsymptotic.dickmanU A y| =
        (Real.log (B : ℝ) - Real.log (A : ℝ)) /
          Real.log (y : ℝ) := by
    simp only [FriableAsymptotic.dickmanU]
    rw [← sub_div, abs_of_nonneg
      (div_nonneg hlogDiff hlogY.le)]
  rw [hu, Nat.cast_sub hAB]
  calc
    (B : ℝ) *
          ((Real.log (B : ℝ) - Real.log (A : ℝ)) /
            Real.log (y : ℝ)) =
        ((B : ℝ) *
          (Real.log (B : ℝ) - Real.log (A : ℝ))) /
            Real.log (y : ℝ) := by ring
    _ ≤ (3 * ((B : ℝ) - (A : ℝ))) /
          Real.log (y : ℝ) := by
      exact div_le_div_of_nonneg_right
        (roughUpperEndpoint_mul_logRatio_le_three_gap
          (by exact_mod_cast hA) (by exact_mod_cast hAB)
          (by exact_mod_cast hBA))
        hlogY.le
    _ = 3 * ((B : ℝ) - (A : ℝ)) /
          Real.log (y : ℝ) := by ring

theorem roughDickmanLowerWeightedDisplacement_le_gap
    {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hy : 2 ≤ y) :
    (A : ℝ) *
        |FriableAsymptotic.dickmanU A y -
          FriableAsymptotic.dickmanU B y| ≤
      (((B - A : ℕ) : ℝ)) / Real.log (y : ℝ) := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogDiff :
      0 ≤ Real.log (B : ℝ) - Real.log (A : ℝ) := by
    exact sub_nonneg.mpr
      (Real.log_le_log (by exact_mod_cast hA)
        (by exact_mod_cast hAB))
  have hu :
      |FriableAsymptotic.dickmanU A y -
          FriableAsymptotic.dickmanU B y| =
        (Real.log (B : ℝ) - Real.log (A : ℝ)) /
          Real.log (y : ℝ) := by
    simp only [FriableAsymptotic.dickmanU]
    rw [show
        Real.log (A : ℝ) / Real.log (y : ℝ) -
            Real.log (B : ℝ) / Real.log (y : ℝ) =
          -((Real.log (B : ℝ) - Real.log (A : ℝ)) /
            Real.log (y : ℝ)) by ring,
      abs_neg, abs_of_nonneg
        (div_nonneg hlogDiff hlogY.le)]
  rw [hu, Nat.cast_sub hAB]
  calc
    (A : ℝ) *
          ((Real.log (B : ℝ) - Real.log (A : ℝ)) /
            Real.log (y : ℝ)) =
        ((A : ℝ) *
          (Real.log (B : ℝ) - Real.log (A : ℝ))) /
            Real.log (y : ℝ) := by ring
    _ ≤ (((B : ℝ) - (A : ℝ))) /
          Real.log (y : ℝ) := by
      exact div_le_div_of_nonneg_right
        (roughLowerEndpoint_mul_logRatio_le_gap
          (by exact_mod_cast hA) (by exact_mod_cast hAB))
        hlogY.le

/-- Dividing the paper tail bound by an active row label replaces the real
row scale by the natural row scale plus one. -/
theorem roughTail_div_row_cast_le
    {n h r : ℕ} {c L : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hL : 0 < L)
    (htail : (h : ℝ) ≤ 2 * c * (n : ℝ) / L) :
    (h : ℝ) / (r : ℝ) ≤
      2 * c * (((n / r : ℕ) : ℝ) + 1) / L := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hnQuot :
      (n : ℝ) / (r : ℝ) ≤
        ((n / r : ℕ) : ℝ) + 1 :=
    (roughRealQuotient_lt_natQuotient_add_one hr).le
  calc
    (h : ℝ) / (r : ℝ) ≤
        (2 * c * (n : ℝ) / L) / (r : ℝ) :=
      div_le_div_of_nonneg_right htail hrReal.le
    _ = 2 * c * ((n : ℝ) / (r : ℝ)) / L := by ring
    _ ≤ 2 * c * (((n / r : ℕ) : ℝ) + 1) / L := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnQuot
          (mul_nonneg (by norm_num) hc))
        hL.le

/-- The elementary scale comparisons repeatedly used below. -/
theorem roughRowScale_elementary
    {x L : ℝ} (hx : 0 ≤ x) (hL : 1 ≤ L) :
    1 ≤ x / L ^ 2 + 1 ∧
    1 / L ≤ x / L ^ 2 + 1 ∧
    (x + 1) / L ^ 2 ≤ x / L ^ 2 + 1 := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hLSq : 1 ≤ L ^ 2 := by nlinarith
  have hinvL : 1 / L ≤ 1 := (div_le_one hLPos).2 hL
  have hinvLSq : 1 / L ^ 2 ≤ 1 :=
    (div_le_one (sq_pos_of_pos hLPos)).2 hLSq
  have hxScale : 0 ≤ x / L ^ 2 :=
    div_nonneg hx (sq_nonneg L)
  constructor
  · linarith
  constructor
  · exact hinvL.trans (by linarith)
  · calc
      (x + 1) / L ^ 2 =
          x / L ^ 2 + 1 / L ^ 2 := by ring
      _ ≤ x / L ^ 2 + 1 :=
        add_le_add le_rfl hinvLSq

/-- Exact real first-moment cancellation at the four unfloored canonical
row endpoints. -/
theorem roughBalancedCanonicalContinuousFirstMoment_eq_zero
    {W n h K r : ℕ} {beta L : ℝ}
    (hr : 0 < r) (hKh : K * h ≤ n) (hKhPos : 0 < K * h) :
    ∑ i : Fin 4,
      roughPhysicalBlockCoefficient (roughHeadDensity W)
          (roughHeadBalancedAlpha W n h K beta L) beta L i *
        ((roughPhysicalNatEndpoint
            (2 * n + h) (2 * n) (2 * n - K * h) n i : ℝ) /
          (r : ℝ)) = 0 := by
  have hrReal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hKhTwo : K * h ≤ 2 * n := by omega
  have hnorm :=
    roughHeadBalancedAlpha_length_normalization
      (W := W) (n := n) (h := h) (K := K)
      (beta := beta) (L := L) hKhPos
  have hminus :
      (((n - K * h : ℕ) : ℝ)) =
        (n : ℝ) - (K : ℝ) * (h : ℝ) := by
    rw [Nat.cast_sub hKh, Nat.cast_mul]
  have hminusTwo :
      (((2 * n - K * h : ℕ) : ℝ)) =
        2 * (n : ℝ) - (K : ℝ) * (h : ℝ) := by
    rw [Nat.cast_sub hKhTwo, Nat.cast_mul, Nat.cast_mul]
    norm_num
  have hnormReal :
      roughHeadDensity W *
          (roughHeadBalancedAlpha W n h K beta L *
              ((K : ℝ) * (h : ℝ)) +
            (beta / L) *
              ((n : ℝ) - (K : ℝ) * (h : ℝ))) =
        (h : ℝ) := by
    simpa only [Nat.cast_mul, hminus] using hnorm
  rw [Fin.sum_univ_four]
  change
    1 * (((2 * n + h : ℕ) : ℝ) / (r : ℝ)) +
      (-(1 + roughHeadDensity W *
          roughHeadBalancedAlpha W n h K beta L)) *
        (((2 * n : ℕ) : ℝ) / (r : ℝ)) +
      roughHeadDensity W *
          (roughHeadBalancedAlpha W n h K beta L - beta / L) *
        (((2 * n - K * h : ℕ) : ℝ) / (r : ℝ)) +
      roughHeadDensity W * (beta / L) *
        ((n : ℝ) / (r : ℝ)) = 0
  rw [hminusTwo]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  calc
    1 * ((2 * (n : ℝ) + (h : ℝ)) / (r : ℝ)) +
          (-(1 + roughHeadDensity W *
              roughHeadBalancedAlpha W n h K beta L)) *
            ((2 * (n : ℝ)) / (r : ℝ)) +
          roughHeadDensity W *
              (roughHeadBalancedAlpha W n h K beta L - beta / L) *
            ((2 * (n : ℝ) - (K : ℝ) * (h : ℝ)) / (r : ℝ)) +
          roughHeadDensity W * (beta / L) *
            ((n : ℝ) / (r : ℝ)) =
        ((h : ℝ) -
          roughHeadDensity W *
            (roughHeadBalancedAlpha W n h K beta L *
                ((K : ℝ) * (h : ℝ)) +
              (beta / L) *
                ((n : ℝ) - (K : ℝ) * (h : ℝ)))) /
          (r : ℝ) := by ring
    _ = 0 := by rw [hnormReal, sub_self, zero_div]

/-- Quotient floors can spoil the exact first moment by at most the sum of
the four absolute coefficients. -/
theorem roughBalancedCanonicalNaturalFirstMoment_abs_le
    {W n h K r : ℕ} {beta L : ℝ}
    (hr : 0 < r) (hKh : K * h ≤ n) (hKhPos : 0 < K * h) :
    |∑ i : Fin 4,
      roughPhysicalBlockCoefficient (roughHeadDensity W)
          (roughHeadBalancedAlpha W n h K beta L) beta L i *
        (roughPhysicalNatEndpoint
          ((2 * n + h) / r) ((2 * n) / r)
          ((2 * n - K * h) / r) (n / r) i : ℝ)| ≤
      ∑ i : Fin 4,
        |roughPhysicalBlockCoefficient (roughHeadDensity W)
          (roughHeadBalancedAlpha W n h K beta L) beta L i| := by
  let numerator : Fin 4 → ℕ :=
    roughPhysicalNatEndpoint
      (2 * n + h) (2 * n) (2 * n - K * h) n
  have hbalance :
      ∑ i : Fin 4,
        roughPhysicalBlockCoefficient (roughHeadDensity W)
            (roughHeadBalancedAlpha W n h K beta L) beta L i *
          ((numerator i : ℝ) / (r : ℝ)) = 0 := by
    simpa only [numerator] using
      roughBalancedCanonicalContinuousFirstMoment_eq_zero
        (W := W) (beta := beta) (L := L) hr hKh hKhPos
  have hendpoint :
      ∀ i : Fin 4,
        roughPhysicalNatEndpoint
            ((2 * n + h) / r) ((2 * n) / r)
            ((2 * n - K * h) / r) (n / r) i =
          numerator i / r := by
    intro i
    fin_cases i <;>
      simp [roughPhysicalNatEndpoint, numerator]
  rw [← sub_zero
      (∑ i : Fin 4,
        roughPhysicalBlockCoefficient (roughHeadDensity W)
          (roughHeadBalancedAlpha W n h K beta L) beta L i *
        (roughPhysicalNatEndpoint
          ((2 * n + h) / r) ((2 * n) / r)
          ((2 * n - K * h) / r) (n / r) i : ℝ)),
    ← hbalance, ← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin 4,
        (roughPhysicalBlockCoefficient (roughHeadDensity W)
            (roughHeadBalancedAlpha W n h K beta L) beta L i *
          (roughPhysicalNatEndpoint
            ((2 * n + h) / r) ((2 * n) / r)
            ((2 * n - K * h) / r) (n / r) i : ℝ) -
        roughPhysicalBlockCoefficient (roughHeadDensity W)
            (roughHeadBalancedAlpha W n h K beta L) beta L i *
          ((numerator i : ℝ) / (r : ℝ)))| =
      |∑ i : Fin 4,
        roughPhysicalBlockCoefficient (roughHeadDensity W)
            (roughHeadBalancedAlpha W n h K beta L) beta L i *
          ((((numerator i / r : ℕ) : ℝ)) -
            (numerator i : ℝ) / (r : ℝ))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hendpoint i]
      ring
    _ ≤ ∑ i : Fin 4,
        |roughPhysicalBlockCoefficient (roughHeadDensity W)
            (roughHeadBalancedAlpha W n h K beta L) beta L i *
          ((((numerator i / r : ℕ) : ℝ)) -
            (numerator i : ℝ) / (r : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 4,
        |roughPhysicalBlockCoefficient (roughHeadDensity W)
          (roughHeadBalancedAlpha W n h K beta L) beta L i| := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left
          (roughNatQuotient_sub_realQuotient_abs_lt_one
            (N := numerator i) hr).le
          (abs_nonneg
            (roughPhysicalBlockCoefficient (roughHeadDensity W)
              (roughHeadBalancedAlpha W n h K beta L) beta L i)))

/-- Under `delta≤1` and `L≥1`, the four physical coefficients have a
uniform elementary `l¹` bound. -/
theorem sum_abs_roughPhysicalBlockCoefficient_le
    {delta alpha beta L : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 1)
    (hL : 1 ≤ L) :
    (∑ i : Fin 4,
      |roughPhysicalBlockCoefficient delta alpha beta L i|) ≤
      2 + 2 * |alpha| + 2 * |beta| := by
  have hLPos : 0 < L := zero_lt_one.trans_le hL
  have hbetaDiv : |beta / L| ≤ |beta| := by
    rw [abs_div, abs_of_pos hLPos]
    exact (div_le_iff₀ hLPos).2
      (by
        have := mul_le_mul_of_nonneg_left hL (abs_nonneg beta)
        simpa only [mul_one] using this)
  have hdeltaAbs : |delta| ≤ 1 := by
    rw [abs_of_nonneg hdelta0]
    exact hdelta1
  have hdeltaMul (z : ℝ) : |delta * z| ≤ |z| := by
    rw [abs_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hdeltaAbs (abs_nonneg z)
  rw [Fin.sum_univ_four]
  change
    |(1 : ℝ)| + |-(1 + delta * alpha)| +
        |delta * (alpha - beta / L)| +
        |delta * (beta / L)| ≤
      2 + 2 * |alpha| + 2 * |beta|
  have honeAlpha :
      |-(1 + delta * alpha)| ≤ 1 + |alpha| := by
    rw [abs_neg]
    exact (abs_add_le _ _).trans
      (add_le_add (by norm_num) (hdeltaMul alpha))
  have hmiddle :
      |delta * (alpha - beta / L)| ≤
        |alpha| + |beta| := by
    exact (hdeltaMul (alpha - beta / L)).trans
      ((abs_sub _ _).trans
        (by
          simpa only [add_comm] using
            (add_le_add_right hbetaDiv |alpha|)))
  have hbroad :
      |delta * (beta / L)| ≤ |beta| :=
    (hdeltaMul (beta / L)).trans hbetaDiv
  norm_num only [abs_one]
  linarith

/-! ## The balanced Dickman main ledger -/

/-- Ordered four-endpoint geometry reduces the Dickman displacement sum to
the three visible quotient gaps. -/
theorem roughPhysicalDickmanDisplacementSum_le_three_gaps
    {delta alpha beta L : ℝ}
    {Xplus X Xminus Xhalf y : ℕ}
    (hy : 2 ≤ y)
    (hhalf : 0 < Xhalf) (hHalfMinus : Xhalf ≤ Xminus)
    (hMinusX : Xminus ≤ X) (hXPlus : X ≤ Xplus)
    (hPlusThree : Xplus ≤ 3 * X) :
    (∑ i : Fin 4,
      |roughPhysicalBlockCoefficient delta alpha beta L i| *
        (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
          |FriableAsymptotic.dickmanU
                (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
            FriableAsymptotic.dickmanU X y|) ≤
      3 * (((Xplus - X : ℕ) : ℝ)) / Real.log (y : ℝ) +
        |delta * (alpha - beta / L)| *
          ((((X - Xminus : ℕ) : ℝ)) / Real.log (y : ℝ)) +
        |delta * (beta / L)| *
          ((((X - Xhalf : ℕ) : ℝ)) /
            Real.log (y : ℝ)) := by
  have hminus : 0 < Xminus := hhalf.trans_le hHalfMinus
  have hx : 0 < X := hminus.trans_le hMinusX
  have hHalfX : Xhalf ≤ X := hHalfMinus.trans hMinusX
  have hupper :=
    roughDickmanUpperWeightedDisplacement_le_three_gap
      hx hXPlus hPlusThree hy
  have hlower :=
    roughDickmanLowerWeightedDisplacement_le_gap
      hminus hMinusX hy
  have hbroad :=
    roughDickmanLowerWeightedDisplacement_le_gap
      hhalf hHalfX hy
  rw [Fin.sum_univ_four]
  change
    |(1 : ℝ)| * (Xplus : ℝ) *
          |FriableAsymptotic.dickmanU Xplus y -
            FriableAsymptotic.dickmanU X y| +
      |-(1 + delta * alpha)| * (X : ℝ) *
          |FriableAsymptotic.dickmanU X y -
            FriableAsymptotic.dickmanU X y| +
      |delta * (alpha - beta / L)| * (Xminus : ℝ) *
          |FriableAsymptotic.dickmanU Xminus y -
            FriableAsymptotic.dickmanU X y| +
      |delta * (beta / L)| * (Xhalf : ℝ) *
          |FriableAsymptotic.dickmanU Xhalf y -
            FriableAsymptotic.dickmanU X y| ≤ _
  norm_num only [abs_one, one_mul, sub_self, abs_zero, mul_zero,
    add_zero]
  exact add_le_add
    (add_le_add hupper
      (by
        simpa only [mul_assoc] using
          (mul_le_mul_of_nonneg_left hlower
            (abs_nonneg (delta * (alpha - beta / L))))))
    (by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hbroad
          (abs_nonneg (delta * (beta / L)))))

/-- The literal balanced canonical-row Dickman ledger has the paper size
`Xhalf/L²+1`, with a constant fixed before `n` and the row are chosen. -/
theorem roughCanonicalBalancedDickmanTransitionLedger_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n r y : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (hrn : r ≤ n)
    (hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n)
    (htailPos : 0 < upperTailLength c n) :
    roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        ((2 * n + upperTailLength c n) / r)
        ((2 * n) / r)
        ((2 * n - (K0 + 1) * upperTailLength c n) / r)
        (n / r) y ≤
      roughCanonicalSharpMainRowScaleConstant W K0 c beta *
        (((n / r : ℕ) : ℝ) / L n ^ 2 + 1) := by
  let K : ℕ := K0 + 1
  let h : ℕ := upperTailLength c n
  let alpha : ℝ :=
    roughHeadBalancedAlpha W n h K beta (L n)
  let x : ℝ := ((n / r : ℕ) : ℝ)
  let S : ℝ := x / L n ^ 2 + 1
  have hK : 0 < K := by simp [K]
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hlogPos : 0 < Real.log (y : ℝ) := by
    have : 0 < L n / 5 := by positivity
    exact this.trans_le hlogY
  have hdelta0 : 0 ≤ roughHeadDensity W :=
    (roughHeadDensity_pos W).le
  have hdelta1 : roughHeadDensity W ≤ 1 :=
    roughHeadDensity_le_one W
  have hxNat : 0 < n / r := Nat.div_pos hrn hr
  have hx : 0 < x := by
    dsimp only [x]
    exact_mod_cast hxNat
  have hscale := roughRowScale_elementary hx.le hLone
  have hS : S = x / L n ^ 2 + 1 := rfl
  have hSinv : 1 / L n ≤ S := by simpa only [hS] using hscale.2.1
  have hSplus :
      (x + 1) / L n ^ 2 ≤ S := by
    simpa only [hS] using hscale.2.2
  have hSone : 1 ≤ S := by simpa only [hS] using hscale.1
  have hSnonneg : 0 ≤ S := le_trans (by norm_num) hSone
  have hinvLog : 1 / Real.log (y : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogPos hLPos).2
    nlinarith [hlogY]
  have htailRow :
      (h : ℝ) / (r : ℝ) ≤ 2 * c * (x + 1) / L n := by
    simpa only [h, x] using
      roughTail_div_row_cast_le hr hc.le hLPos htail
  have hKh' : K * h ≤ n := by
    simpa only [K, h] using hKh
  have hh : h ≤ n :=
    (Nat.le_mul_of_pos_left h hK).trans hKh'
  have hKhPos : 0 < K * h := mul_pos hK (by simpa only [h] using htailPos)
  have hhalfMinus :
      n / r ≤ (2 * n - K * h) / r := by
    apply Nat.div_le_div_right
    omega
  have hminusX :
      (2 * n - K * h) / r ≤ (2 * n) / r :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hxPlus :
      (2 * n) / r ≤ (2 * n + h) / r :=
    Nat.div_le_div_right (by omega)
  have hXthree :
      (2 * n) / r ≤ 3 * (n / r) :=
    roughTwoQuotient_le_three_halfQuotient hr hrn
  have hPlusThree :
      (2 * n + h) / r ≤ 3 * ((2 * n) / r) :=
    roughUpperQuotient_le_three_centralQuotient hr hrn hh
  have hgapUpper :
      ((((2 * n + h) / r - (2 * n) / r : ℕ) : ℝ)) ≤
        2 * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := r) hr (show 2 * n ≤ 2 * n + h by omega)
    rw [show 2 * n + h - 2 * n = h by omega] at hq
    exact hq.trans (add_le_add htailRow le_rfl)
  have hgapLower :
      ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) ≤
        2 * (K : ℝ) * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := r) hr (show 2 * n - K * h ≤ 2 * n by omega)
    rw [show 2 * n - (2 * n - K * h) = K * h by omega,
      Nat.cast_mul] at hq
    calc
      ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) ≤
          ((K : ℝ) * (h : ℝ)) / (r : ℝ) + 1 := hq
      _ = (K : ℝ) * ((h : ℝ) / (r : ℝ)) + 1 := by ring
      _ ≤ (K : ℝ) * (2 * c * (x + 1) / L n) + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left htailRow hKReal.le) le_rfl
      _ = 2 * (K : ℝ) * c * (x + 1) / L n + 1 := by ring
  have hgapBroad :
      ((((2 * n) / r - n / r : ℕ) : ℝ)) ≤
        2 * x := by
    have hhalfX : n / r ≤ (2 * n) / r :=
      hhalfMinus.trans hminusX
    rw [Nat.cast_sub hhalfX]
    dsimp only [x]
    exact_mod_cast (show
      (2 * n) / r - n / r ≤ 2 * (n / r) by omega)
  have halpha :
      |alpha| ≤ roughBalancedAlphaConstant W K0 c beta := by
    dsimp only [alpha, h, K, roughBalancedAlphaConstant]
    exact roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  have hbetaDiv : |beta / L n| ≤ |beta| := by
    rw [abs_div, abs_of_pos hLPos]
    exact (div_le_iff₀ hLPos).2
      (by
        have := mul_le_mul_of_nonneg_left hLone (abs_nonneg beta)
        simpa only [mul_one] using this)
  have hmiddleCoeff :
      |roughHeadDensity W * (alpha - beta / L n)| ≤
        roughBalancedAlphaConstant W K0 c beta + |beta| := by
    rw [abs_mul, abs_of_nonneg hdelta0]
    calc
      roughHeadDensity W * |alpha - beta / L n| ≤
          1 * |alpha - beta / L n| :=
        mul_le_mul_of_nonneg_right hdelta1 (abs_nonneg _)
      _ = |alpha - beta / L n| := one_mul _
      _ ≤ |alpha| + |beta / L n| := abs_sub _ _
      _ ≤ roughBalancedAlphaConstant W K0 c beta + |beta| :=
        add_le_add halpha hbetaDiv
  have hbroadCoeff :
      |roughHeadDensity W * (beta / L n)| ≤ |beta| / L n := by
    rw [abs_mul, abs_of_nonneg hdelta0, abs_div,
      abs_of_pos hLPos]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hdelta1
        (div_nonneg (abs_nonneg beta) hLPos.le)
  have hdisplacement :=
    roughPhysicalDickmanDisplacementSum_le_three_gaps
      (delta := roughHeadDensity W) (alpha := alpha)
      (beta := beta) (L := L n)
      (Xplus := (2 * n + h) / r)
      (X := (2 * n) / r)
      (Xminus := (2 * n - K * h) / r)
      (Xhalf := n / r) hy hxNat hhalfMinus hminusX hxPlus hPlusThree
  have hupperTerm :
      3 * ((((2 * n + h) / r - (2 * n) / r : ℕ) : ℝ)) /
          Real.log (y : ℝ) ≤
        (30 * c + 15) * S := by
    calc
      3 * ((((2 * n + h) / r - (2 * n) / r : ℕ) : ℝ)) /
          Real.log (y : ℝ) =
          (3 * ((((2 * n + h) / r -
            (2 * n) / r : ℕ) : ℝ))) *
            (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (3 * (2 * c * (x + 1) / L n + 1)) *
          (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapUpper (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 30 * c * ((x + 1) / L n ^ 2) +
          15 * (1 / L n) := by ring
      _ ≤ 30 * c * S + 15 * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSplus
            (mul_nonneg (by norm_num) hc.le))
          (mul_le_mul_of_nonneg_left hSinv (by norm_num))
      _ = (30 * c + 15) * S := by ring
  have hlowerTerm :
      |roughHeadDensity W * (alpha - beta / L n)| *
          (((((2 * n) / r -
            (2 * n - K * h) / r : ℕ) : ℝ)) /
            Real.log (y : ℝ)) ≤
        (roughBalancedAlphaConstant W K0 c beta + |beta|) *
          (10 * (K : ℝ) * c + 5) * S := by
    calc
      |roughHeadDensity W * (alpha - beta / L n)| *
          (((((2 * n) / r -
            (2 * n - K * h) / r : ℕ) : ℝ)) /
            Real.log (y : ℝ)) =
        |roughHeadDensity W * (alpha - beta / L n)| *
          ((((2 * n) / r -
            (2 * n - K * h) / r : ℕ) : ℝ)) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (roughBalancedAlphaConstant W K0 c beta + |beta|) *
          (2 * (K : ℝ) * c * (x + 1) / L n + 1) *
          (5 / L n) := by
        have hmiddleNonneg :
            0 ≤ roughBalancedAlphaConstant W K0 c beta + |beta| :=
          add_nonneg
            (roughBalancedAlphaConstant_nonneg W K0
              (beta := beta) hc)
            (abs_nonneg beta)
        have hgapLowerNonneg :
            0 ≤ 2 * (K : ℝ) * c * (x + 1) / L n + 1 :=
          (Nat.cast_nonneg _).trans hgapLower
        have hproduct :
            |roughHeadDensity W * (alpha - beta / L n)| *
                ((((2 * n) / r -
                  (2 * n - K * h) / r : ℕ) : ℝ)) ≤
              (roughBalancedAlphaConstant W K0 c beta + |beta|) *
                (2 * (K : ℝ) * c * (x + 1) / L n + 1) :=
          (mul_le_mul_of_nonneg_left hgapLower (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hmiddleCoeff hgapLowerNonneg)
        exact
          (mul_le_mul_of_nonneg_right hproduct
              (one_div_nonneg.mpr hlogPos.le)).trans
            (mul_le_mul_of_nonneg_left hinvLog
              (mul_nonneg hmiddleNonneg hgapLowerNonneg))
      _ = (roughBalancedAlphaConstant W K0 c beta + |beta|) *
          (10 * (K : ℝ) * c * ((x + 1) / L n ^ 2) +
            5 * (1 / L n)) := by ring
      _ ≤ (roughBalancedAlphaConstant W K0 c beta + |beta|) *
          (10 * (K : ℝ) * c * S + 5 * S) := by
        apply mul_le_mul_of_nonneg_left
        · exact add_le_add
            (mul_le_mul_of_nonneg_left hSplus
              (mul_nonneg
                (mul_nonneg (by norm_num) hKReal.le) hc.le))
            (mul_le_mul_of_nonneg_left hSinv (by norm_num))
        · exact add_nonneg
            (roughBalancedAlphaConstant_nonneg W K0
              (beta := beta) hc)
            (abs_nonneg beta)
      _ = (roughBalancedAlphaConstant W K0 c beta + |beta|) *
          (10 * (K : ℝ) * c + 5) * S := by ring
  have hbroadTerm :
      |roughHeadDensity W * (beta / L n)| *
          (((((2 * n) / r - n / r : ℕ) : ℝ)) /
            Real.log (y : ℝ)) ≤
        10 * |beta| * (x / L n ^ 2) := by
    calc
      |roughHeadDensity W * (beta / L n)| *
          (((((2 * n) / r - n / r : ℕ) : ℝ)) /
            Real.log (y : ℝ)) =
        |roughHeadDensity W * (beta / L n)| *
          ((((2 * n) / r - n / r : ℕ) : ℝ)) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (|beta| / L n) * (2 * x) * (5 / L n) := by
        have hbetaDivNonneg : 0 ≤ |beta| / L n :=
          div_nonneg (abs_nonneg beta) hLPos.le
        have hgapBroadNonneg : 0 ≤ 2 * x :=
          mul_nonneg (by norm_num) hx.le
        have hproduct :
            |roughHeadDensity W * (beta / L n)| *
                ((((2 * n) / r - n / r : ℕ) : ℝ)) ≤
              (|beta| / L n) * (2 * x) :=
          (mul_le_mul_of_nonneg_left hgapBroad (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hbroadCoeff hgapBroadNonneg)
        exact
          (mul_le_mul_of_nonneg_right hproduct
              (one_div_nonneg.mpr hlogPos.le)).trans
            (mul_le_mul_of_nonneg_left hinvLog
              (mul_nonneg hbetaDivNonneg hgapBroadNonneg))
      _ = 10 * |beta| * (x / L n ^ 2) := by ring
  have hfirstMoment :=
    roughBalancedCanonicalNaturalFirstMoment_abs_le
      (W := W) (n := n) (h := h) (K := K) (r := r)
      (beta := beta) (L := L n) hr hKh' hKhPos
  have hcoefficientSum :
      (∑ i : Fin 4,
        |roughPhysicalBlockCoefficient (roughHeadDensity W)
          alpha beta (L n) i|) ≤
        2 + 2 * roughBalancedAlphaConstant W K0 c beta +
          2 * |beta| := by
    calc
      _ ≤ 2 + 2 * |alpha| + 2 * |beta| :=
        sum_abs_roughPhysicalBlockCoefficient_le
          hdelta0 hdelta1 hLone
      _ ≤ 2 + 2 * roughBalancedAlphaConstant W K0 c beta +
          2 * |beta| := by linarith
  unfold roughPhysicalDickmanTransitionLedger
  change
    (∑ i : Fin 4,
      |roughPhysicalBlockCoefficient (roughHeadDensity W)
          alpha beta (L n) i| *
        (roughPhysicalNatEndpoint
          ((2 * n + h) / r) ((2 * n) / r)
          ((2 * n - K * h) / r) (n / r) i : ℝ) *
        |FriableAsymptotic.dickmanU
            (roughPhysicalNatEndpoint
              ((2 * n + h) / r) ((2 * n) / r)
              ((2 * n - K * h) / r) (n / r) i) y -
          FriableAsymptotic.dickmanU ((2 * n) / r) y|) +
      |∑ i : Fin 4,
        roughPhysicalBlockCoefficient (roughHeadDensity W)
          alpha beta (L n) i *
        (roughPhysicalNatEndpoint
          ((2 * n + h) / r) ((2 * n) / r)
          ((2 * n - K * h) / r) (n / r) i : ℝ)| ≤ _
  calc
    _ ≤ ((30 * c + 15) * S +
          (roughBalancedAlphaConstant W K0 c beta + |beta|) *
            (10 * (K : ℝ) * c + 5) * S +
          10 * |beta| * (x / L n ^ 2)) +
        (2 + 2 * roughBalancedAlphaConstant W K0 c beta +
          2 * |beta|) := by
      exact add_le_add
        (hdisplacement.trans
          (add_le_add
            (add_le_add hupperTerm hlowerTerm)
            hbroadTerm))
        (hfirstMoment.trans hcoefficientSum)
    _ ≤ ((30 * c + 15) * S +
          (roughBalancedAlphaConstant W K0 c beta + |beta|) *
            (10 * (K : ℝ) * c + 5) * S +
          10 * |beta| * S) +
        (2 + 2 * roughBalancedAlphaConstant W K0 c beta +
          2 * |beta|) * S := by
      have hxScale : x / L n ^ 2 ≤ S := by
        dsimp only [S]
        linarith
      exact add_le_add
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10)
              (abs_nonneg beta))))
        (by
          have hA0 :
              0 ≤ roughBalancedAlphaConstant W K0 c beta :=
            roughBalancedAlphaConstant_nonneg W K0
              (beta := beta) hc
          have hcoefficientNonneg :
              0 ≤ 2 + 2 * roughBalancedAlphaConstant W K0 c beta +
                2 * |beta| :=
            add_nonneg
              (add_nonneg (by norm_num : (0 : ℝ) ≤ 2)
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hA0))
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
                (abs_nonneg beta))
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hSone hcoefficientNonneg))
    _ = roughCanonicalSharpMainRowScaleConstant W K0 c beta * S := by
      unfold roughCanonicalSharpMainRowScaleConstant
      dsimp only [K]
      ring

/-! ## The weighted sharp Saias transition ledger -/

/-- The three literal weighted sharp Saias pair budgets have the same
canonical row scale. -/
theorem roughCanonicalBalancedSaiasTransitionBudget_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n r y : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (hrn : r ≤ n)
    (_hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n) :
    roughPhysicalSaiasTransitionBudget
        (roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant)
        (roughHeadDensity W)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        ((2 * n + upperTailLength c n) / r)
        ((2 * n) / r)
        ((2 * n - (K0 + 1) * upperTailLength c n) / r)
        (n / r) y ≤
      roughCanonicalSharpTransitionRowScaleConstant W K0 c beta *
        (((n / r : ℕ) : ℝ) / L n ^ 2 + 1) := by
  let K : ℕ := K0 + 1
  let h : ℕ := upperTailLength c n
  let alpha : ℝ :=
    roughHeadBalancedAlpha W n h K beta (L n)
  let x : ℝ := ((n / r : ℕ) : ℝ)
  let S : ℝ := x / L n ^ 2 + 1
  let C : ℝ := roughSaiasSharpDefectConstant
  have hK : 0 < K := by simp [K]
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hlogPos : 0 < Real.log (y : ℝ) := by
    have : 0 < L n / 5 := by positivity
    exact this.trans_le hlogY
  have hdelta0 : 0 ≤ roughHeadDensity W :=
    (roughHeadDensity_pos W).le
  have hdelta1 : roughHeadDensity W ≤ 1 :=
    roughHeadDensity_le_one W
  have hC : 0 ≤ C := by
    dsimp only [C]
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hxNat : 0 < n / r := Nat.div_pos hrn hr
  have hx : 0 < x := by
    dsimp only [x]
    exact_mod_cast hxNat
  have hscale := roughRowScale_elementary hx.le hLone
  have hSinv : 1 / L n ≤ S := by
    simpa only [S] using hscale.2.1
  have hSplus :
      (x + 1) / L n ^ 2 ≤ S := by
    simpa only [S] using hscale.2.2
  have hSone : 1 ≤ S := by simpa only [S] using hscale.1
  have hSnonneg : 0 ≤ S := le_trans (by norm_num) hSone
  have hinvLSq : 1 / L n ^ 2 ≤ S := by
    have hLSq : 1 ≤ L n ^ 2 := by nlinarith
    exact ((div_le_one (sq_pos_of_pos hLPos)).2 hLSq).trans hSone
  have hxScale : x / L n ^ 2 ≤ S := by
    dsimp only [S]
    linarith
  have hinvL : 1 / L n ≤ 1 :=
    (div_le_one hLPos).2 hLone
  have hinvLog : 1 / Real.log (y : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogPos hLPos).2
    nlinarith [hlogY]
  have hinvLogSq :
      1 / Real.log (y : ℝ) ^ 2 ≤ 25 / L n ^ 2 := by
    have hsquare :=
      (sq_le_sq₀
        (by positivity :
          0 ≤ 1 / Real.log (y : ℝ))
        (by positivity : 0 ≤ 5 / L n)).2 hinvLog
    calc
      1 / Real.log (y : ℝ) ^ 2 =
          (1 / Real.log (y : ℝ)) ^ 2 := by ring
      _ ≤ (5 / L n) ^ 2 := hsquare
      _ = 25 / L n ^ 2 := by ring
  have htailRow :
      (h : ℝ) / (r : ℝ) ≤ 2 * c * (x + 1) / L n := by
    simpa only [h, x] using
      roughTail_div_row_cast_le hr hc.le hLPos htail
  have hKh' : K * h ≤ n := by
    simpa only [K, h] using hKh
  have hh : h ≤ n :=
    (Nat.le_mul_of_pos_left h hK).trans hKh'
  have hhalfMinus :
      n / r ≤ (2 * n - K * h) / r := by
    apply Nat.div_le_div_right
    omega
  have hminusX :
      (2 * n - K * h) / r ≤ (2 * n) / r :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hxPlus :
      (2 * n) / r ≤ (2 * n + h) / r :=
    Nat.div_le_div_right (by omega)
  have hXthree :
      (2 * n) / r ≤ 3 * (n / r) :=
    roughTwoQuotient_le_three_halfQuotient hr hrn
  have hPlusThree :
      (2 * n + h) / r ≤ 3 * ((2 * n) / r) :=
    roughUpperQuotient_le_three_centralQuotient hr hrn hh
  have hgapUpper :
      ((((2 * n + h) / r - (2 * n) / r : ℕ) : ℝ)) ≤
        2 * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := r) hr (show 2 * n ≤ 2 * n + h by omega)
    rw [show 2 * n + h - 2 * n = h by omega] at hq
    exact hq.trans (add_le_add htailRow le_rfl)
  have hgapLower :
      ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) ≤
        2 * (K : ℝ) * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := r) hr (show 2 * n - K * h ≤ 2 * n by omega)
    rw [show 2 * n - (2 * n - K * h) = K * h by omega,
      Nat.cast_mul] at hq
    calc
      ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) ≤
          ((K : ℝ) * (h : ℝ)) / (r : ℝ) + 1 := hq
      _ = (K : ℝ) * ((h : ℝ) / (r : ℝ)) + 1 := by ring
      _ ≤ (K : ℝ) * (2 * c * (x + 1) / L n) + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left htailRow hKReal.le) le_rfl
      _ = 2 * (K : ℝ) * c * (x + 1) / L n + 1 := by ring
  have hgapBroad :
      ((((2 * n - K * h) / r - n / r : ℕ) : ℝ)) ≤
        2 * x := by
    rw [Nat.cast_sub hhalfMinus]
    have hminusThree :
        ((2 * n - K * h) / r : ℕ) ≤ 3 * (n / r) :=
      hminusX.trans hXthree
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / r - n / r ≤ 2 * (n / r) by omega)
  have hupperEndpoints :
      (((2 * n) / r : ℕ) : ℝ) +
          (((2 * n + h) / r : ℕ) : ℝ) ≤ 12 * x := by
    dsimp only [x]
    exact_mod_cast (show
      (2 * n) / r + (2 * n + h) / r ≤
        12 * (n / r) by omega)
  have hlowerEndpoints :
      (((2 * n - K * h) / r : ℕ) : ℝ) +
          (((2 * n) / r : ℕ) : ℝ) ≤ 6 * x := by
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / r + (2 * n) / r ≤
        6 * (n / r) by omega)
  have hbroadEndpoints :
      (((n / r : ℕ) : ℝ)) +
          (((2 * n - K * h) / r : ℕ) : ℝ) ≤ 4 * x := by
    dsimp only [x]
    exact_mod_cast (show
      n / r + (2 * n - K * h) / r ≤
        4 * (n / r) by omega)
  have halpha :
      |alpha| ≤ roughBalancedAlphaConstant W K0 c beta := by
    dsimp only [alpha, h, K, roughBalancedAlphaConstant]
    exact roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  have hdeltaAlpha :
      |roughHeadDensity W * alpha| ≤
        roughBalancedAlphaConstant W K0 c beta := by
    rw [abs_mul, abs_of_nonneg hdelta0]
    exact (mul_le_mul_of_nonneg_right hdelta1
      (abs_nonneg alpha)).trans (by simpa using halpha)
  have hdeltaBeta :
      |roughHeadDensity W * (beta / L n)| ≤ |beta| / L n := by
    rw [abs_mul, abs_of_nonneg hdelta0, abs_div,
      abs_of_pos hLPos]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hdelta1
        (div_nonneg (abs_nonneg beta) hLPos.le)
  have heta :
      roughSaiasInvLogSqEndpointRate C y =
        10 * C / Real.log (y : ℝ) ^ 2 := rfl
  have hupperEta :
      roughSaiasInvLogSqEndpointRate C y *
          ((((2 * n) / r : ℕ) : ℝ) +
            (((2 * n + h) / r : ℕ) : ℝ)) ≤
        3000 * C * (x / L n ^ 2) := by
    rw [heta]
    calc
      (10 * C / Real.log (y : ℝ) ^ 2) *
          ((((2 * n) / r : ℕ) : ℝ) +
            (((2 * n + h) / r : ℕ) : ℝ)) ≤
        (10 * C / Real.log (y : ℝ) ^ 2) * (12 * x) :=
          mul_le_mul_of_nonneg_left hupperEndpoints (by positivity)
      _ = 120 * C * x *
          (1 / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ 120 * C * x * (25 / L n ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinvLogSq
          (mul_nonneg
            (mul_nonneg (by norm_num) hC) hx.le)
      _ = 3000 * C * (x / L n ^ 2) := by ring
  have hupperGap :
      5 * ((((2 * n + h) / r -
          (2 * n) / r : ℕ) : ℝ)) /
        Real.log (y : ℝ) ≤
      (50 * c + 25) * S := by
    calc
      5 * ((((2 * n + h) / r -
          (2 * n) / r : ℕ) : ℝ)) /
          Real.log (y : ℝ) =
        (5 * ((((2 * n + h) / r -
          (2 * n) / r : ℕ) : ℝ))) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (5 * (2 * c * (x + 1) / L n + 1)) *
          (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapUpper (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 50 * c * ((x + 1) / L n ^ 2) +
          25 * (1 / L n) := by ring
      _ ≤ 50 * c * S + 25 * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSplus
            (mul_nonneg (by norm_num) hc.le))
          (mul_le_mul_of_nonneg_left hSinv (by norm_num))
      _ = (50 * c + 25) * S := by ring
  have hupperPair :
      roughSaiasPairTransitionBudget
          (roughSaiasInvLogSqEndpointRate C)
          ((2 * n) / r) ((2 * n + h) / r) y ≤
        (3000 * C + 50 * c + 25) * S := by
    unfold roughSaiasPairTransitionBudget
    calc
      _ ≤ 3000 * C * (x / L n ^ 2) +
          (50 * c + 25) * S :=
        add_le_add hupperEta hupperGap
      _ ≤ 3000 * C * S + (50 * c + 25) * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3000) hC)) le_rfl
      _ = (3000 * C + 50 * c + 25) * S := by ring
  have hlowerEta :
      roughSaiasInvLogSqEndpointRate C y *
          ((((2 * n - K * h) / r : ℕ) : ℝ) +
            (((2 * n) / r : ℕ) : ℝ)) ≤
        1500 * C * (x / L n ^ 2) := by
    rw [heta]
    calc
      (10 * C / Real.log (y : ℝ) ^ 2) *
          ((((2 * n - K * h) / r : ℕ) : ℝ) +
            (((2 * n) / r : ℕ) : ℝ)) ≤
        (10 * C / Real.log (y : ℝ) ^ 2) * (6 * x) :=
          mul_le_mul_of_nonneg_left hlowerEndpoints (by positivity)
      _ = 60 * C * x *
          (1 / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ 60 * C * x * (25 / L n ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinvLogSq
          (mul_nonneg
            (mul_nonneg (by norm_num) hC) hx.le)
      _ = 1500 * C * (x / L n ^ 2) := by ring
  have hlowerGap :
      5 * ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) /
        Real.log (y : ℝ) ≤
      (50 * (K : ℝ) * c + 25) * S := by
    calc
      5 * ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ)) /
          Real.log (y : ℝ) =
        (5 * ((((2 * n) / r -
          (2 * n - K * h) / r : ℕ) : ℝ))) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤
          (5 * (2 * (K : ℝ) * c * (x + 1) / L n + 1)) *
            (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapLower (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 50 * (K : ℝ) * c *
          ((x + 1) / L n ^ 2) + 25 * (1 / L n) := by ring
      _ ≤ 50 * (K : ℝ) * c * S + 25 * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hSplus
            (mul_nonneg
              (mul_nonneg (by norm_num) hKReal.le) hc.le))
          (mul_le_mul_of_nonneg_left hSinv (by norm_num))
      _ = (50 * (K : ℝ) * c + 25) * S := by ring
  have hlowerPair :
      roughSaiasPairTransitionBudget
          (roughSaiasInvLogSqEndpointRate C)
          ((2 * n - K * h) / r) ((2 * n) / r) y ≤
        (1500 * C + 50 * (K : ℝ) * c + 25) * S := by
    unfold roughSaiasPairTransitionBudget
    calc
      _ ≤ 1500 * C * (x / L n ^ 2) +
          (50 * (K : ℝ) * c + 25) * S :=
        add_le_add hlowerEta hlowerGap
      _ ≤ 1500 * C * S +
          (50 * (K : ℝ) * c + 25) * S :=
        add_le_add
          (mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1500) hC)) le_rfl
      _ = (1500 * C + 50 * (K : ℝ) * c + 25) * S := by ring
  have hbroadEta :
      roughSaiasInvLogSqEndpointRate C y *
          ((((n / r : ℕ) : ℝ)) +
            (((2 * n - K * h) / r : ℕ) : ℝ)) ≤
        1000 * C * (x / L n ^ 2) := by
    rw [heta]
    calc
      (10 * C / Real.log (y : ℝ) ^ 2) *
          ((((n / r : ℕ) : ℝ)) +
            (((2 * n - K * h) / r : ℕ) : ℝ)) ≤
        (10 * C / Real.log (y : ℝ) ^ 2) * (4 * x) :=
          mul_le_mul_of_nonneg_left hbroadEndpoints (by positivity)
      _ = 40 * C * x *
          (1 / Real.log (y : ℝ) ^ 2) := by ring
      _ ≤ 40 * C * x * (25 / L n ^ 2) := by
        exact mul_le_mul_of_nonneg_left hinvLogSq
          (mul_nonneg
            (mul_nonneg (by norm_num) hC) hx.le)
      _ = 1000 * C * (x / L n ^ 2) := by ring
  have hbroadGap :
      5 * ((((2 * n - K * h) / r -
          n / r : ℕ) : ℝ)) / Real.log (y : ℝ) ≤
        50 * (x / L n) := by
    calc
      5 * ((((2 * n - K * h) / r -
          n / r : ℕ) : ℝ)) / Real.log (y : ℝ) =
        (5 * ((((2 * n - K * h) / r -
          n / r : ℕ) : ℝ))) *
          (1 / Real.log (y : ℝ)) := by ring
      _ ≤ (5 * (2 * x)) * (5 / L n) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hgapBroad (by norm_num))
          hinvLog (by positivity) (by positivity)
      _ = 50 * (x / L n) := by ring
  have hbroadWeighted :
      |roughHeadDensity W * (beta / L n)| *
          roughSaiasPairTransitionBudget
            (roughSaiasInvLogSqEndpointRate C)
            (n / r) ((2 * n - K * h) / r) y ≤
        |beta| * (1000 * C + 75) * S := by
    unfold roughSaiasPairTransitionBudget
    calc
      |roughHeadDensity W * (beta / L n)| *
          (roughSaiasInvLogSqEndpointRate C y *
              ((((n / r : ℕ) : ℝ)) +
                (((2 * n - K * h) / r : ℕ) : ℝ)) +
            5 * ((((2 * n - K * h) / r -
                n / r : ℕ) : ℝ)) /
              Real.log (y : ℝ)) ≤
        (|beta| / L n) *
          (1000 * C * (x / L n ^ 2) +
            50 * (x / L n)) := by
        have hbudgetNonneg :
            0 ≤ 1000 * C * (x / L n ^ 2) +
                50 * (x / L n) :=
          add_nonneg
            (mul_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hC)
              (div_nonneg hx.le (sq_nonneg (L n))))
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50)
              (div_nonneg hx.le hLPos.le))
        exact
          (mul_le_mul_of_nonneg_left
              (add_le_add hbroadEta hbroadGap) (abs_nonneg _)).trans
            (mul_le_mul_of_nonneg_right hdeltaBeta hbudgetNonneg)
      _ = |beta| *
          (1000 * C * (x / L n ^ 2) * (1 / L n) +
            50 * (x / L n ^ 2)) := by ring
      _ ≤ |beta| *
          (1000 * C * (x / L n ^ 2) +
            50 * (x / L n ^ 2)) := by
        apply mul_le_mul_of_nonneg_left
        · have hmul :
              1000 * C * (x / L n ^ 2) * (1 / L n) ≤
                1000 * C * (x / L n ^ 2) := by
            have hraw :=
              mul_le_mul_of_nonneg_left hinvL
                (mul_nonneg
                  (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1000) hC)
                  (div_nonneg hx.le (sq_nonneg (L n))))
            simpa only [mul_one] using hraw
          exact add_le_add hmul le_rfl
        · exact abs_nonneg beta
      _ ≤ |beta| * ((1000 * C + 50) * S) := by
        rw [show
          1000 * C * (x / L n ^ 2) +
              50 * (x / L n ^ 2) =
            (1000 * C + 50) * (x / L n ^ 2) by ring]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hxScale
            (add_nonneg
              (mul_nonneg (by norm_num) hC) (by norm_num)))
          (abs_nonneg beta)
      _ ≤ |beta| * ((1000 * C + 75) * S) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_right
            (by norm_num : (1000 * C + 50) ≤ 1000 * C + 75)
            hSnonneg
        · exact abs_nonneg beta
      _ = |beta| * (1000 * C + 75) * S := by ring
  unfold roughPhysicalSaiasTransitionBudget
  calc
    roughSaiasPairTransitionBudget
          (roughSaiasInvLogSqEndpointRate C)
          ((2 * n) / r) ((2 * n + h) / r) y +
        |roughHeadDensity W * alpha| *
          roughSaiasPairTransitionBudget
            (roughSaiasInvLogSqEndpointRate C)
            ((2 * n - K * h) / r) ((2 * n) / r) y +
        |roughHeadDensity W * (beta / L n)| *
          roughSaiasPairTransitionBudget
            (roughSaiasInvLogSqEndpointRate C)
            (n / r) ((2 * n - K * h) / r) y ≤
      (3000 * C + 50 * c + 25) * S +
        roughBalancedAlphaConstant W K0 c beta *
          (1500 * C + 50 * (K : ℝ) * c + 25) * S +
        |beta| * (1000 * C + 75) * S := by
      have hlowerBoundNonneg :
          0 ≤ (1500 * C + 50 * (K : ℝ) * c + 25) * S :=
        mul_nonneg
          (add_nonneg
            (add_nonneg
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1500) hC)
              (mul_nonneg
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 50)
                  hKReal.le)
                hc.le))
            (by norm_num))
          hSnonneg
      exact add_le_add
        (add_le_add hupperPair
          (by
            simpa only [mul_assoc] using
              ((mul_le_mul_of_nonneg_left hlowerPair (abs_nonneg _)).trans
                (mul_le_mul_of_nonneg_right hdeltaAlpha
                  hlowerBoundNonneg))))
        hbroadWeighted
    _ = roughCanonicalSharpTransitionRowScaleConstant
          W K0 c beta * S := by
      unfold roughCanonicalSharpTransitionRowScaleConstant
      dsimp only [K, C]
      ring

/-! ## Absorption of the sharp fixed-head divisor sum -/

set_option maxHeartbeats 4000000 in
/-- The all-row sharp fixed-head budget is bounded by the fixed divisor
constant at the same canonical row scale. -/
theorem roughCanonicalBalancedSharpFixedHeadBudget_le
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n y : ℕ} (hn : 2 ≤ n) (_hy : 2 ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hrowN : row.1 ≤ n)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n) :
    roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n (upperTailLength c n) (K0 + 1) y
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row ≤
      roughCanonicalSharpHeadRowScaleConstant W K0 c beta *
        (((n / row.1 : ℕ) : ℝ) / L n ^ 2 + 1) := by
  let K : ℕ := K0 + 1
  let h : ℕ := upperTailLength c n
  let alpha : ℝ :=
    roughHeadBalancedAlpha W n h K beta (L n)
  let x : ℝ := ((n / row.1 : ℕ) : ℝ)
  let S : ℝ := x / L n ^ 2 + 1
  let C : ℝ := roughSaiasSharpDefectConstant
  have hr : 0 < row.1 :=
    canonicalCompleteRoughRow_label_pos y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row
  have hK : 0 < K := by simp [K]
  have hKReal : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hlogPos : 0 < Real.log (y : ℝ) := by
    have : 0 < L n / 5 := by positivity
    exact this.trans_le hlogY
  have hC : 0 ≤ C := by
    dsimp only [C]
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hxNat : 0 < n / row.1 := Nat.div_pos hrowN hr
  have hx : 0 < x := by
    dsimp only [x]
    exact_mod_cast hxNat
  have hscale := roughRowScale_elementary hx.le hLone
  have hSinv : 1 / L n ≤ S := by
    simpa only [S] using hscale.2.1
  have hSplus :
      (x + 1) / L n ^ 2 ≤ S := by
    simpa only [S] using hscale.2.2
  have hSone : 1 ≤ S := by simpa only [S] using hscale.1
  have hSnonneg : 0 ≤ S := le_trans (by norm_num) hSone
  have hinvLSq : 1 / L n ^ 2 ≤ S := by
    have hLSq : 1 ≤ L n ^ 2 := by nlinarith
    exact ((div_le_one (sq_pos_of_pos hLPos)).2 hLSq).trans hSone
  have hxScale : x / L n ^ 2 ≤ S := by
    dsimp only [S]
    linarith
  have hinvL : 1 / L n ≤ 1 :=
    (div_le_one hLPos).2 hLone
  have hinvLog : 1 / Real.log (y : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogPos hLPos).2
    nlinarith [hlogY]
  have hinvLogSq :
      1 / Real.log (y : ℝ) ^ 2 ≤ 25 / L n ^ 2 := by
    have hsquare :=
      (sq_le_sq₀
        (by positivity :
          0 ≤ 1 / Real.log (y : ℝ))
        (by positivity : 0 ≤ 5 / L n)).2 hinvLog
    calc
      1 / Real.log (y : ℝ) ^ 2 =
          (1 / Real.log (y : ℝ)) ^ 2 := by ring
      _ ≤ (5 / L n) ^ 2 := hsquare
      _ = 25 / L n ^ 2 := by ring
  have htailRow :
      (h : ℝ) / (row.1 : ℝ) ≤
        2 * c * (x + 1) / L n := by
    simpa only [h, x] using
      roughTail_div_row_cast_le hr hc.le hLPos htail
  have hKh' : K * h ≤ n := by
    simpa only [K, h] using hKh
  have hhalfMinus :
      n / row.1 ≤ (2 * n - K * h) / row.1 := by
    apply Nat.div_le_div_right
    omega
  have hminusX :
      (2 * n - K * h) / row.1 ≤ (2 * n) / row.1 :=
    Nat.div_le_div_right (Nat.sub_le _ _)
  have hXthree :
      (2 * n) / row.1 ≤ 3 * (n / row.1) :=
    roughTwoQuotient_le_three_halfQuotient hr hrowN
  have hgapHigh :
      ((((2 * n) / row.1 -
          (2 * n - K * h) / row.1 : ℕ) : ℝ)) ≤
        2 * (K : ℝ) * c * (x + 1) / L n + 1 := by
    have hq := roughQuotientGap_cast_le
      (r := row.1) hr
      (show 2 * n - K * h ≤ 2 * n by omega)
    rw [show 2 * n - (2 * n - K * h) = K * h by omega,
      Nat.cast_mul] at hq
    calc
      ((((2 * n) / row.1 -
          (2 * n - K * h) / row.1 : ℕ) : ℝ)) ≤
          ((K : ℝ) * (h : ℝ)) / (row.1 : ℝ) + 1 := hq
      _ = (K : ℝ) * ((h : ℝ) / (row.1 : ℝ)) + 1 := by ring
      _ ≤ (K : ℝ) * (2 * c * (x + 1) / L n) + 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left htailRow hKReal.le) le_rfl
      _ = 2 * (K : ℝ) * c * (x + 1) / L n + 1 := by ring
  have hgapBroad :
      ((((2 * n - K * h) / row.1 -
          n / row.1 : ℕ) : ℝ)) ≤ 2 * x := by
    rw [Nat.cast_sub hhalfMinus]
    have hminusThree :
        ((2 * n - K * h) / row.1 : ℕ) ≤
          3 * (n / row.1) :=
      hminusX.trans hXthree
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / row.1 - n / row.1 ≤
        2 * (n / row.1) by omega)
  have hhighEndpoints :
      (((2 * n - K * h) / row.1 : ℕ) : ℝ) +
          (((2 * n) / row.1 : ℕ) : ℝ) ≤ 6 * x := by
    dsimp only [x]
    exact_mod_cast (show
      (2 * n - K * h) / row.1 + (2 * n) / row.1 ≤
        6 * (n / row.1) by omega)
  have hbroadEndpoints :
      (((n / row.1 : ℕ) : ℝ)) +
          (((2 * n - K * h) / row.1 : ℕ) : ℝ) ≤ 4 * x := by
    dsimp only [x]
    exact_mod_cast (show
      n / row.1 + (2 * n - K * h) / row.1 ≤
        4 * (n / row.1) by omega)
  have halpha :
      |alpha| ≤ roughBalancedAlphaConstant W K0 c beta := by
    dsimp only [alpha, h, K, roughBalancedAlphaConstant]
    exact roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  unfold roughCanonicalSharpFixedHeadShiftBudgetAllRows
    roughCanonicalSharpHeadRowScaleConstant
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro d hdMem
  have hd : 0 < d := Nat.pos_of_mem_divisors hdMem
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  let G : ℝ := (Real.log (d : ℝ) + 12) / (d : ℝ)
  have hG : 0 ≤ G := by
    dsimp only [G]
    positivity
  let Hhigh : ℝ :=
    31 + G * (10 * (K : ℝ) * c + 5) +
      3000 * C / (d : ℝ)
  let Hbroad : ℝ :=
    31 + 10 * G + 2000 * C / (d : ℝ)
  have hHhigh : 0 ≤ Hhigh := by
    dsimp only [Hhigh]
    positivity
  have hHbroad : 0 ≤ Hbroad := by
    dsimp only [Hbroad]
    positivity
  have hhighBudget :
      roughSaiasSharpIntervalFixedDivisorBudget
          ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y d ≤
        Hhigh * S := by
    unfold roughSaiasSharpIntervalFixedDivisorBudget
    have hconst :
        6 + 5 / Real.log (y : ℝ) ≤ 31 * S := by
      calc
        6 + 5 / Real.log (y : ℝ) =
            6 + 5 * (1 / Real.log (y : ℝ)) := by ring
        _ ≤ 6 + 5 * (5 / L n) :=
          add_le_add_right
            (mul_le_mul_of_nonneg_left hinvLog
              (by norm_num : (0 : ℝ) ≤ 5)) 6
        _ = 6 + 25 * (1 / L n) := by ring
        _ ≤ 6 * S + 25 * S :=
          add_le_add
            (by
              simpa only [mul_one] using
                mul_le_mul_of_nonneg_left hSone
                  (by norm_num : (0 : ℝ) ≤ 6))
            (mul_le_mul_of_nonneg_left hSinv
              (by norm_num : (0 : ℝ) ≤ 25))
        _ = 31 * S := by ring
    have hgapTerm :
        ((((2 * n) / row.1 -
            (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ)) ≤
          (G * (10 * (K : ℝ) * c + 5)) * S := by
      calc
        ((((2 * n) / row.1 -
            (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ)) =
          ((((2 * n) / row.1 -
              (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            G * (1 / Real.log (y : ℝ)) := by
              dsimp only [G]
              ring
        _ ≤ (2 * (K : ℝ) * c * (x + 1) / L n + 1) *
            G * (5 / L n) := by
          exact mul_le_mul
            (mul_le_mul_of_nonneg_right hgapHigh hG)
            hinvLog (by positivity) (by positivity)
        _ = G *
            (10 * (K : ℝ) * c *
                ((x + 1) / L n ^ 2) +
              5 * (1 / L n)) := by ring
        _ ≤ G * (10 * (K : ℝ) * c * S + 5 * S) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hSplus
                (mul_nonneg
                  (mul_nonneg (by norm_num) hKReal.le) hc.le))
              (mul_le_mul_of_nonneg_left hSinv (by norm_num))
          · exact hG
        _ = (G * (10 * (K : ℝ) * c + 5)) * S := by ring
    have hendpointTerm :
        20 * C *
            ((((2 * n - K * h) / row.1 : ℕ) : ℝ) +
              (((2 * n) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) ≤
          (3000 * C / (d : ℝ)) * S := by
      calc
        20 * C *
            ((((2 * n - K * h) / row.1 : ℕ) : ℝ) +
              (((2 * n) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) ≤
          20 * C * (6 * x) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hhighEndpoints
                (mul_nonneg (by norm_num) hC))
              (mul_nonneg hdReal.le (sq_nonneg _))
        _ = (120 * C * x / (d : ℝ)) *
            (1 / Real.log (y : ℝ) ^ 2) := by ring
        _ ≤ (120 * C * x / (d : ℝ)) *
            (25 / L n ^ 2) := by
          exact mul_le_mul_of_nonneg_left hinvLogSq (by positivity)
        _ = (3000 * C / (d : ℝ)) *
            (x / L n ^ 2) := by ring
        _ ≤ (3000 * C / (d : ℝ)) * S :=
          mul_le_mul_of_nonneg_left hxScale (by positivity)
    calc
      6 + 5 / Real.log (y : ℝ) +
          ((((2 * n) / row.1 -
              (2 * n - K * h) / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ)) +
          20 * C *
            ((((2 * n - K * h) / row.1 : ℕ) : ℝ) +
              (((2 * n) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2) ≤
        31 * S +
          (G * (10 * (K : ℝ) * c + 5)) * S +
          (3000 * C / (d : ℝ)) * S :=
        add_le_add (add_le_add hconst hgapTerm) hendpointTerm
      _ = Hhigh * S := by
        dsimp only [Hhigh]
        ring
  have hhighWeighted :
      |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget
            ((2 * n - K * h) / row.1)
            ((2 * n) / row.1) y d ≤
        roughBalancedAlphaConstant W K0 c beta *
          Hhigh * S := by
    have hbudget0 : 0 ≤
        roughSaiasSharpIntervalFixedDivisorBudget
          ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y d := by
      unfold roughSaiasSharpIntervalFixedDivisorBudget
      positivity
    calc
      |alpha| * roughSaiasSharpIntervalFixedDivisorBudget
          ((2 * n - K * h) / row.1)
          ((2 * n) / row.1) y d ≤
        roughBalancedAlphaConstant W K0 c beta *
          roughSaiasSharpIntervalFixedDivisorBudget
            ((2 * n - K * h) / row.1)
            ((2 * n) / row.1) y d :=
          mul_le_mul_of_nonneg_right halpha hbudget0
      _ ≤ roughBalancedAlphaConstant W K0 c beta *
          (Hhigh * S) :=
        mul_le_mul_of_nonneg_left hhighBudget
          (roughBalancedAlphaConstant_nonneg
            W K0 (beta := beta) hc)
      _ = roughBalancedAlphaConstant W K0 c beta *
          Hhigh * S := by ring
  have hbroadWeighted :
      |beta / L n| *
          roughSaiasSharpIntervalFixedDivisorBudget
            (n / row.1) ((2 * n - K * h) / row.1) y d ≤
        |beta| * Hbroad * S := by
    unfold roughSaiasSharpIntervalFixedDivisorBudget
    rw [abs_div, abs_of_pos hLPos]
    have hconst :
        (|beta| / L n) *
            (6 + 5 / Real.log (y : ℝ)) ≤
          |beta| * 31 * S := by
      calc
        (|beta| / L n) *
            (6 + 5 / Real.log (y : ℝ)) =
          |beta| *
            (6 * (1 / L n) +
              5 * (1 / L n) *
                (1 / Real.log (y : ℝ))) := by ring
        _ ≤ |beta| *
            (6 * (1 / L n) +
              5 * (1 / L n) * (5 / L n)) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add_right
              (mul_le_mul_of_nonneg_left hinvLog
                (mul_nonneg
                  (by norm_num : (0 : ℝ) ≤ 5)
                  (div_nonneg
                    (by norm_num : (0 : ℝ) ≤ 1) hLPos.le)))
              (6 * (1 / L n))
          · exact abs_nonneg beta
        _ = |beta| *
            (6 * (1 / L n) + 25 * (1 / L n ^ 2)) := by ring
        _ ≤ |beta| * (6 * S + 25 * S) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hSinv (by norm_num))
              (mul_le_mul_of_nonneg_left hinvLSq (by norm_num))
          · exact abs_nonneg beta
        _ = |beta| * 31 * S := by ring
    have hgapTerm :
        (|beta| / L n) *
          (((((2 * n - K * h) / row.1 -
              n / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ))) ≤
          |beta| * (10 * G) * S := by
      calc
        (|beta| / L n) *
          (((((2 * n - K * h) / row.1 -
              n / row.1 : ℕ) : ℝ)) *
            (Real.log (d : ℝ) + 12) /
              ((d : ℝ) * Real.log (y : ℝ))) =
          |beta| * ((((2 * n - K * h) / row.1 -
              n / row.1 : ℕ) : ℝ)) * G *
            (1 / Real.log (y : ℝ)) * (1 / L n) := by
              dsimp only [G]
              ring
        _ ≤ |beta| * (2 * x) * G *
            (5 / L n) * (1 / L n) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hgapBroad
                  (abs_nonneg beta)) hG)
              hinvLog
              (div_nonneg
                (by norm_num : (0 : ℝ) ≤ 1) hlogPos.le)
              (mul_nonneg
                (mul_nonneg (abs_nonneg beta)
                  (mul_nonneg
                    (by norm_num : (0 : ℝ) ≤ 2) hx.le)) hG))
            (div_nonneg
              (by norm_num : (0 : ℝ) ≤ 1) hLPos.le)
        _ = |beta| * (10 * G) * (x / L n ^ 2) := by ring
        _ ≤ |beta| * (10 * G) * S :=
          mul_le_mul_of_nonneg_left hxScale
            (mul_nonneg (abs_nonneg beta)
              (mul_nonneg
                (by norm_num : (0 : ℝ) ≤ 10) hG))
    have hendpointTerm :
        (|beta| / L n) *
          (20 * C *
            ((((n / row.1 : ℕ) : ℝ)) +
              (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2)) ≤
          |beta| * (2000 * C / (d : ℝ)) * S := by
      calc
        (|beta| / L n) *
          (20 * C *
            ((((n / row.1 : ℕ) : ℝ)) +
              (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2)) ≤
          (|beta| / L n) *
            (20 * C * (4 * x) /
              ((d : ℝ) * Real.log (y : ℝ) ^ 2)) := by
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hbroadEndpoints
                  (mul_nonneg (by norm_num) hC))
                (mul_nonneg hdReal.le (sq_nonneg _)))
              (div_nonneg (abs_nonneg beta) hLPos.le)
        _ = |beta| * (80 * C * x / (d : ℝ)) *
            (1 / Real.log (y : ℝ) ^ 2) *
            (1 / L n) := by ring
        _ ≤ |beta| * (80 * C * x / (d : ℝ)) *
            (25 / L n ^ 2) * (1 / L n) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hinvLogSq (by positivity))
            (div_nonneg (by norm_num) hLPos.le)
        _ = |beta| * (2000 * C / (d : ℝ)) *
            (x / L n ^ 2) * (1 / L n) := by ring
        _ ≤ |beta| * (2000 * C / (d : ℝ)) *
            (x / L n ^ 2) := by
          have hmul :=
            mul_le_mul_of_nonneg_left hinvL
              (show 0 ≤ |beta| * (2000 * C / (d : ℝ)) *
                (x / L n ^ 2) by positivity)
          simpa only [mul_one] using hmul
        _ ≤ |beta| * (2000 * C / (d : ℝ)) * S :=
          mul_le_mul_of_nonneg_left hxScale (by positivity)
    calc
      (|beta| / L n) *
          (6 + 5 / Real.log (y : ℝ) +
            ((((2 * n - K * h) / row.1 -
                n / row.1 : ℕ) : ℝ)) *
              (Real.log (d : ℝ) + 12) /
                ((d : ℝ) * Real.log (y : ℝ)) +
            20 * C *
              ((((n / row.1 : ℕ) : ℝ)) +
                (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
                ((d : ℝ) * Real.log (y : ℝ) ^ 2)) =
        (|beta| / L n) *
            (6 + 5 / Real.log (y : ℝ)) +
          (|beta| / L n) *
            (((((2 * n - K * h) / row.1 -
                n / row.1 : ℕ) : ℝ)) *
              (Real.log (d : ℝ) + 12) /
                ((d : ℝ) * Real.log (y : ℝ))) +
          (|beta| / L n) *
            (20 * C *
              ((((n / row.1 : ℕ) : ℝ)) +
                (((2 * n - K * h) / row.1 : ℕ) : ℝ)) /
                ((d : ℝ) * Real.log (y : ℝ) ^ 2)) := by ring
      _ ≤ |beta| * 31 * S +
          |beta| * (10 * G) * S +
          |beta| * (2000 * C / (d : ℝ)) * S :=
        add_le_add (add_le_add hconst hgapTerm) hendpointTerm
      _ = |beta| * Hbroad * S := by
        dsimp only [Hbroad]
        ring
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  by_cases hdLo : d ≤ n / row.1
  · rw [if_pos hdLo]
    calc
      |alpha| *
            roughSaiasSharpIntervalFixedDivisorBudget
              ((2 * n - K * h) / row.1)
              ((2 * n) / row.1) y d +
          |beta / L n| *
            roughSaiasSharpIntervalFixedDivisorBudget
              (n / row.1) ((2 * n - K * h) / row.1) y d ≤
        roughBalancedAlphaConstant W K0 c beta * Hhigh * S +
          |beta| * Hbroad * S :=
        add_le_add hhighWeighted hbroadWeighted
      _ ≤
        (roughBalancedAlphaConstant W K0 c beta * Hhigh +
          |beta| * Hbroad +
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
            S := by
        have hsmall0 :
            0 ≤ 4 *
              (roughBalancedAlphaConstant W K0 c beta + |beta|) :=
          mul_nonneg (by norm_num)
            (add_nonneg
              (roughBalancedAlphaConstant_nonneg
                W K0 (beta := beta) hc)
              (abs_nonneg beta))
        calc
          roughBalancedAlphaConstant W K0 c beta * Hhigh * S +
                |beta| * Hbroad * S =
              (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                |beta| * Hbroad) * S := by ring
          _ ≤
              (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                |beta| * Hbroad +
                4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
                  S :=
            mul_le_mul_of_nonneg_right
              (by
                simpa only [add_zero] using
                  add_le_add_right hsmall0
                    (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                      |beta| * Hbroad))
              hSnonneg
      _ =
        roughCanonicalSharpHeadDivisorRowScaleConstant
          W K0 d c beta * S := by
        unfold roughCanonicalSharpHeadDivisorRowScaleConstant
        dsimp only [Hhigh, Hbroad, G, C]
        ring
  · rw [if_neg hdLo]
    have hsmall :
        4 * (|alpha| + |beta / L n|) ≤
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) := by
      have hbetaAbs : |beta / L n| ≤ |beta| := by
        rw [abs_div, abs_of_pos hLPos]
        exact (div_le_iff₀ hLPos).2
          (by
            have := mul_le_mul_of_nonneg_left hLone (abs_nonneg beta)
            simpa only [mul_one] using this)
      exact mul_le_mul_of_nonneg_left
        (add_le_add halpha hbetaAbs) (by norm_num)
    calc
      4 * (|alpha| + |beta / L n|) ≤
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) :=
        hsmall
      _ ≤
        (roughBalancedAlphaConstant W K0 c beta * Hhigh +
          |beta| * Hbroad +
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
            S := by
        have hbase0 :
            0 ≤ roughBalancedAlphaConstant W K0 c beta * Hhigh +
              |beta| * Hbroad := by
          exact add_nonneg
            (mul_nonneg
              (roughBalancedAlphaConstant_nonneg
                W K0 (beta := beta) hc) hHhigh)
            (mul_nonneg (abs_nonneg beta) hHbroad)
        have hsmall0 :
            0 ≤ 4 *
              (roughBalancedAlphaConstant W K0 c beta + |beta|) := by
          exact mul_nonneg (by norm_num)
            (add_nonneg
              (roughBalancedAlphaConstant_nonneg
                W K0 (beta := beta) hc)
              (abs_nonneg beta))
        calc
          4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) ≤
              4 * (roughBalancedAlphaConstant W K0 c beta + |beta|) * S := by
            simpa only [mul_one] using
              mul_le_mul_of_nonneg_left hSone hsmall0
          _ ≤
              (roughBalancedAlphaConstant W K0 c beta * Hhigh +
                |beta| * Hbroad +
                4 * (roughBalancedAlphaConstant W K0 c beta + |beta|)) *
                  S :=
            mul_le_mul_of_nonneg_right
              (by
                simpa only [zero_add] using
                  add_le_add_left hbase0
                    (4 * (roughBalancedAlphaConstant W K0 c beta +
                      |beta|)))
              hSnonneg
      _ =
        roughCanonicalSharpHeadDivisorRowScaleConstant
          W K0 d c beta * S := by
        unfold roughCanonicalSharpHeadDivisorRowScaleConstant
        dsimp only [Hhigh, Hbroad, G, C]
        ring

/-! ## One unified canonical raw-row allowance -/

theorem roughCanonicalSharpMainRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpMainRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpMainRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hK : (0 : ℝ) ≤ (((K0 + 1 : ℕ) : ℝ)) := by positivity
  positivity

theorem roughCanonicalSharpTransitionRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpTransitionRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpTransitionRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  positivity

theorem roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {d : ℕ} (hd : 0 < d) :
    0 ≤ roughCanonicalSharpHeadDivisorRowScaleConstant
      W K0 d c beta := by
  unfold roughCanonicalSharpHeadDivisorRowScaleConstant
  have hA :=
    roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc
  have hC : 0 ≤ roughSaiasSharpDefectConstant := by
    unfold roughSaiasSharpDefectConstant
    have htheta : 0 ≤ roughSaiasThetaFourthPowerConstant :=
      roughSaiasThetaFourthPowerConstant_pos.le
    positivity
  have hdReal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  positivity

theorem roughCanonicalSharpHeadRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpHeadRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpHeadRowScaleConstant
  apply Finset.sum_nonneg
  intro d hdMem
  exact mul_nonneg (abs_nonneg _)
    (roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
      W K0 (beta := beta) hc (Nat.pos_of_mem_divisors hdMem))

theorem roughCanonicalSharpUnifiedRowScaleConstant_nonneg
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c) :
    0 ≤ roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta := by
  unfold roughCanonicalSharpUnifiedRowScaleConstant
  exact add_nonneg
    (add_nonneg
      (roughCanonicalSharpMainRowScaleConstant_nonneg
        W K0 (beta := beta) hc)
      (roughCanonicalSharpTransitionRowScaleConstant_nonneg
        W K0 (beta := beta) hc))
    (roughCanonicalSharpHeadRowScaleConstant_nonneg
      W K0 (beta := beta) hc)

/-- The balanced literal raw row is controlled by one fixed
`C_W * (Xrow/L²+1)` allowance after all three analytic ledgers have been
discharged. -/
theorem roughCanonicalBalancedRawRowQuotaError_abs_le_unified
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n y : ℕ} (hn : 2 ≤ n)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hrowN : row.1 ≤ n)
    (hWy : W ≤ y)
    (hY :
      roughSaiasInvLogSqEndpointCutoff
        roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n)
    (htailPos : 0 < upperTailLength c n)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughCanonicalRawRowQuotaError
        W n (upperTailLength c n) (K0 + 1) y
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row| ≤
      3 * (roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta *
        ((((n / row.1 : ℕ) : ℝ)) / L n ^ 2 + 1)) := by
  let S : ℝ := (((n / row.1 : ℕ) : ℝ)) / L n ^ 2 + 1
  have hx0 : 0 ≤ (((n / row.1 : ℕ) : ℝ)) :=
    Nat.cast_nonneg _
  have hS0 : 0 ≤ S := by
    dsimp only [S]
    exact add_nonneg
      (div_nonneg hx0 (sq_nonneg (L n))) (by norm_num)
  have hmain0 :=
    roughCanonicalSharpMainRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have htransition0 :=
    roughCanonicalSharpTransitionRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hhead0 :=
    roughCanonicalSharpHeadRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hmainBase :=
    roughCanonicalBalancedDickmanTransitionLedger_le
      W K0 (beta := beta) (n := n) (r := row.1) (y := y)
      hc hn
      (canonicalCompleteRoughRow_label_pos y
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row)
      hrowN hy hLone hlogY htail hKh htailPos
  have htransitionBase :=
    roughCanonicalBalancedSaiasTransitionBudget_le
      W K0 (beta := beta) (n := n) (r := row.1) (y := y)
      hc hn
      (canonicalCompleteRoughRow_label_pos y
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row)
      hrowN hy hLone hlogY htail hKh
  have hheadBase :=
    roughCanonicalBalancedSharpFixedHeadBudget_le
      W K0 (beta := beta) (n := n) (y := y)
      hc hn hy row hrowN hLone hlogY htail hKh
  have hmain :
      roughPhysicalDickmanTransitionLedger
          (roughHeadDensity W)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) y ≤
        roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta * S := by
    apply hmainBase.trans
    apply mul_le_mul_of_nonneg_right _ hS0
    unfold roughCanonicalSharpUnifiedRowScaleConstant
    linarith
  have htransition :
      roughPhysicalSaiasTransitionBudget
          (roughSaiasInvLogSqEndpointRate
            roughSaiasSharpDefectConstant)
          (roughHeadDensity W)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) y ≤
        roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta * S := by
    apply htransitionBase.trans
    apply mul_le_mul_of_nonneg_right _ hS0
    unfold roughCanonicalSharpUnifiedRowScaleConstant
    linarith
  have hhead :
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
          W n (upperTailLength c n) (K0 + 1) y
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) row ≤
        roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta * S := by
    apply hheadBase.trans
    apply mul_le_mul_of_nonneg_right _ hS0
    unfold roughCanonicalSharpUnifiedRowScaleConstant
    linarith
  simpa only [S] using
    (roughCanonicalRawRowQuotaError_abs_le_three_mul_sharpAllowance
      hWy row hrowN hKh hY hy hlogs hmain htransition hhead)

end

end Erdos390.WholePaper
