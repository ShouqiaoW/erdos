import Erdos390.WholePaper.BankPaperFourFiveRoughChamberReduction
import Erdos390.Full.PrimeBandQuadrature

/-!
# The prime-counting endpoint used by the four/five chamber

The ordered-prime calculation needs a local prime-counting estimate with
enough logarithmic saving to survive the later partial summations.  This
file derives that estimate from the already audited power-saving PNT for
Chebyshev's theta function.

The main term below is the standard two-endpoint logarithmic-integral
increment

`B / log B - A / log A + integral_A^B dt / log(t)^2`.

Keeping this exact integration-by-parts presentation avoids introducing a
new global normalization for `li`.  Subtracting Mathlib's exact
`primeCounting_eq_theta_div_log_add_integral` identity at `A` and `B`
then leaves only the theta error.  A fourth-log theta error gives a
fifth-log local prime-counting error, uniformly in both endpoints.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory
open Erdos390.Full.PrimeBandQuadrature

/-- The two-endpoint logarithmic-integral main term, in the exact form
produced by integration by parts. -/
def fourFiveLogIntegralIncrement (A B : Real) : Real :=
  B / Real.log B - A / Real.log A +
    ∫ t in A..B, 1 / Real.log t ^ 2

/-- The theta-error integrand left after extracting the logarithmic-integral
main term from the exact prime-counting identity. -/
def fourFivePrimeCountingErrorKernel (t : Real) : Real :=
  thetaError t / (t * Real.log t ^ 2)

private lemma intervalIntegrable_fourFivePrimeCountingThetaKernel
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    IntervalIntegrable
      (fun t : Real => Chebyshev.theta t / (t * Real.log t ^ 2))
      volume A B := by
  have hfull := Chebyshev.integrableOn_theta_div_id_mul_log_sq B
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
  apply hfull.mono_set
  intro t ht
  exact Set.mem_Icc.mpr (by
    constructor
    · exact hA.trans ht.1
    · exact ht.2)

private lemma continuousOn_fourFivePrimeCountingMainKernel
    {A B : Real} (hA : 2 <= A) :
    ContinuousOn (fun t : Real => 1 / Real.log t ^ 2) (Icc A B) := by
  intro t ht
  have ht1 : 1 < t := by linarith [hA, ht.1]
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht1)
  have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  exact ContinuousAt.continuousWithinAt
    ((continuousAt_const.div
      ((Real.continuousAt_log ht0).pow 2) (pow_ne_zero 2 hlog0)))

private lemma intervalIntegrable_fourFivePrimeCountingMainKernel
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    IntervalIntegrable (fun t : Real => 1 / Real.log t ^ 2)
      volume A B :=
  (continuousOn_fourFivePrimeCountingMainKernel (A := A) (B := B) hA)
    |>.intervalIntegrable_of_Icc hAB

private lemma hasDerivAt_fourFive_id_div_log
    {x : Real} (hx : 1 < x) :
    HasDerivAt (fun t : Real => t / Real.log t)
      ((Real.log x - 1) / Real.log x ^ 2) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  convert (hasDerivAt_id x).div (Real.hasDerivAt_log hx0) hlog0 using 1;
    simp only [id_eq];
    field_simp [hx0, hlog0]

private lemma intervalIntegrable_fourFivePrimeCountingInvLogKernel
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    IntervalIntegrable (fun t : Real => 1 / Real.log t) volume A B := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAB
  intro t ht
  have ht1 : 1 < t := by linarith [hA, ht.1]
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht1)
  have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  exact ContinuousAt.continuousWithinAt
    (continuousAt_const.div (Real.continuousAt_log ht0) hlog0)

/-- The displayed main term really is the logarithmic-integral increment
`integral_A^B dt / log t`; the definition merely stores its partial-
integration normal form used by the theta identity. -/
theorem fourFiveLogIntegralIncrement_eq_integral_inv_log
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    fourFiveLogIntegralIncrement A B =
      ∫ t in A..B, 1 / Real.log t := by
  have hderiv :
      (∫ t in A..B, (Real.log t - 1) / Real.log t ^ 2) =
        B / Real.log B - A / Real.log A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hAB] at ht
      exact hasDerivAt_fourFive_id_div_log (by linarith [hA, ht.1])
    · have hmain :=
        intervalIntegrable_fourFivePrimeCountingMainKernel hA hAB
      have hinv :=
        intervalIntegrable_fourFivePrimeCountingInvLogKernel hA hAB
      have hsub := hinv.sub hmain
      apply hsub.congr
      intro t ht
      have ht1 : 1 < t := by
        rw [uIoc_of_le hAB] at ht
        linarith [hA, ht.1]
      have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
      field_simp [hlog0]
  have hinv :=
    intervalIntegrable_fourFivePrimeCountingInvLogKernel hA hAB
  have hmain :=
    intervalIntegrable_fourFivePrimeCountingMainKernel hA hAB
  have hsplit :
      (∫ t in A..B, (Real.log t - 1) / Real.log t ^ 2) =
        (∫ t in A..B, 1 / Real.log t) -
          ∫ t in A..B, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_sub hinv hmain]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1 : 1 < t := by
      rw [uIcc_of_le hAB] at ht
      linarith [hA, ht.1]
    have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    field_simp [hlog0]
  unfold fourFiveLogIntegralIncrement
  rw [← hderiv, hsplit]
  ring

private lemma fourFivePrimeCountingThetaKernel_eq_main_add_error
    {t : Real} (ht : 1 < t) :
    Chebyshev.theta t / (t * Real.log t ^ 2) =
      1 / Real.log t ^ 2 + fourFivePrimeCountingErrorKernel t := by
  have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht)
  have hlog0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  unfold fourFivePrimeCountingErrorKernel thetaError
  field_simp [ht0, hlog0]; ring

private lemma intervalIntegrable_fourFivePrimeCountingErrorKernel
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    IntervalIntegrable fourFivePrimeCountingErrorKernel volume A B := by
  have htheta :=
    intervalIntegrable_fourFivePrimeCountingThetaKernel hA hAB
  have hmain :=
    intervalIntegrable_fourFivePrimeCountingMainKernel hA hAB
  have hsub := htheta.sub hmain
  apply hsub.congr
  intro t ht
  change Chebyshev.theta t / (t * Real.log t ^ 2) -
      1 / Real.log t ^ 2 = fourFivePrimeCountingErrorKernel t
  rw [fourFivePrimeCountingThetaKernel_eq_main_add_error (by
    rw [uIoc_of_le hAB] at ht
    linarith [hA, ht.1])]
  ring

private lemma integral_fourFivePrimeCountingThetaKernel_sub
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    (∫ t in (2 : Real)..B,
        Chebyshev.theta t / (t * Real.log t ^ 2)) -
      (∫ t in (2 : Real)..A,
        Chebyshev.theta t / (t * Real.log t ^ 2)) =
      ∫ t in A..B,
        Chebyshev.theta t / (t * Real.log t ^ 2) := by
  have hleft : IntervalIntegrable
      (fun t : Real => Chebyshev.theta t / (t * Real.log t ^ 2))
      volume 2 A := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hA]
    exact Chebyshev.integrableOn_theta_div_id_mul_log_sq A
  have hright :=
    intervalIntegrable_fourFivePrimeCountingThetaKernel hA hAB
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

/-- Exact two-endpoint prime-counting identity.  Its left side is the
prime-counting increment minus the logarithmic-integral increment, and every
term on the right contains the genuine theta error. -/
theorem fourFivePrimeCounting_sub_logIntegralIncrement_eq_thetaError
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    ((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        fourFiveLogIntegralIncrement A B =
      thetaError B / Real.log B - thetaError A / Real.log A +
        ∫ t in A..B, fourFivePrimeCountingErrorKernel t := by
  have hB2 : 2 <= B := hA.trans hAB
  have hcountB := Chebyshev.primeCounting_eq_theta_div_log_add_integral hB2
  have hcountA := Chebyshev.primeCounting_eq_theta_div_log_add_integral hA
  have hthetaSub := integral_fourFivePrimeCountingThetaKernel_sub hA hAB
  have htheta :=
    intervalIntegrable_fourFivePrimeCountingThetaKernel hA hAB
  have hmain :=
    intervalIntegrable_fourFivePrimeCountingMainKernel hA hAB
  have herr :=
    intervalIntegrable_fourFivePrimeCountingErrorKernel hA hAB
  have hsplit :
      (∫ t in A..B,
          Chebyshev.theta t / (t * Real.log t ^ 2)) =
        (∫ t in A..B, 1 / Real.log t ^ 2) +
          ∫ t in A..B, fourFivePrimeCountingErrorKernel t := by
    rw [← intervalIntegral.integral_add hmain herr]
    apply intervalIntegral.integral_congr
    intro t ht
    exact fourFivePrimeCountingThetaKernel_eq_main_add_error (by
      rw [uIcc_of_le hAB] at ht
      linarith [hA, ht.1])
  have hA0 : A ≠ 0 := by linarith
  have hB0 : B ≠ 0 := by linarith
  have hlogA0 : Real.log A ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  have hlogB0 : Real.log B ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith))
  rw [hcountB, hcountA]
  unfold fourFiveLogIntegralIncrement
  calc
    (Chebyshev.theta B / Real.log B +
          (∫ t in (2 : Real)..B,
            Chebyshev.theta t / (t * Real.log t ^ 2))) -
        (Chebyshev.theta A / Real.log A +
          ∫ t in (2 : Real)..A,
            Chebyshev.theta t / (t * Real.log t ^ 2)) -
        (B / Real.log B - A / Real.log A +
          ∫ t in A..B, 1 / Real.log t ^ 2) =
      Chebyshev.theta B / Real.log B -
        Chebyshev.theta A / Real.log A +
        ((∫ t in (2 : Real)..B,
            Chebyshev.theta t / (t * Real.log t ^ 2)) -
          ∫ t in (2 : Real)..A,
            Chebyshev.theta t / (t * Real.log t ^ 2)) -
        (B / Real.log B - A / Real.log A +
          ∫ t in A..B, 1 / Real.log t ^ 2) := by ring
    _ = Chebyshev.theta B / Real.log B -
        Chebyshev.theta A / Real.log A +
        (∫ t in A..B,
          Chebyshev.theta t / (t * Real.log t ^ 2)) -
        (B / Real.log B - A / Real.log A +
          ∫ t in A..B, 1 / Real.log t ^ 2) := by rw [hthetaSub]
    _ = _ := by
      rw [hsplit]
      unfold thetaError
      field_simp [hA0, hB0, hlogA0, hlogB0]; ring

/-- Literal `pi-li` form of the exact endpoint identity. -/
theorem fourFivePrimeCounting_sub_integral_inv_log_eq_thetaError
    {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    ((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        (∫ t in A..B, 1 / Real.log t) =
      thetaError B / Real.log B - thetaError A / Real.log A +
        ∫ t in A..B, fourFivePrimeCountingErrorKernel t := by
  rw [← fourFiveLogIntegralIncrement_eq_integral_inv_log hA hAB]
  exact fourFivePrimeCounting_sub_logIntegralIncrement_eq_thetaError hA hAB

private lemma abs_fourFivePrimeCountingErrorKernel_le
    {A B C t : Real} (hA : 3 <= A) (_hAB : A <= B)
    (hC : 0 <= C) (ht : t ∈ Icc A B)
    (hTheta : |thetaError t| <= C * t / Real.log t ^ 4) :
    |fourFivePrimeCountingErrorKernel t| <=
      C / Real.log A ^ 5 := by
  have htpos : 0 < t := by linarith [hA, ht.1]
  have hlogApos : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith [hA, ht.1])
  have hApos : 0 < A := by linarith
  have hlogAt : Real.log A <= Real.log t :=
    Real.log_le_log (by linarith [hA]) ht.1
  have hlogAone : 1 <= Real.log A := by
    have hexp : Real.exp 1 < A := Real.exp_one_lt_three.trans_le hA
    exact ((Real.lt_log_iff_exp_lt hApos).2 hexp).le
  unfold fourFivePrimeCountingErrorKernel
  rw [abs_div, abs_of_pos (mul_pos htpos (sq_pos_of_pos hlogtpos))]
  calc
    |thetaError t| / (t * Real.log t ^ 2) <=
        (C * t / Real.log t ^ 4) /
          (t * Real.log t ^ 2) := by
      exact div_le_div_of_nonneg_right hTheta
        (mul_pos htpos (sq_pos_of_pos hlogtpos)).le
    _ = C / Real.log t ^ 6 := by
      field_simp [ne_of_gt htpos, ne_of_gt hlogtpos]
    _ <= C / Real.log A ^ 6 := by
      exact div_le_div_of_nonneg_left hC
        (pow_pos hlogApos 6) (pow_le_pow_left₀ hlogApos.le hlogAt 6)
    _ <= C / Real.log A ^ 5 := by
      have hpow : Real.log A ^ 5 <= Real.log A ^ 6 := by
        calc
          Real.log A ^ 5 = Real.log A ^ 5 * 1 := by ring
          _ <= Real.log A ^ 5 * Real.log A :=
            mul_le_mul_of_nonneg_left hlogAone (pow_nonneg hlogApos.le 5)
          _ = Real.log A ^ 6 := by ring
      exact div_le_div_of_nonneg_left hC (pow_pos hlogApos 5) hpow

/-- A fourth-log theta error on one interval gives a fifth-log local
prime-counting error.  The factor `B` is the interval-length scale; this is
the form that remains uniform for the moving endpoints in the four/five
chamber. -/
theorem abs_fourFivePrimeCounting_sub_logIntegralIncrement_le
    {A B C : Real} (hA : 3 <= A) (hAB : A <= B) (hC : 0 <= C)
    (hTheta : ∀ t ∈ Icc A B,
      |thetaError t| <= C * t / Real.log t ^ 4) :
    abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        fourFiveLogIntegralIncrement A B) <=
      3 * C * B / Real.log A ^ 5 := by
  have hApos : 0 < A := by linarith
  have hBpos : 0 < B := hApos.trans_le hAB
  have hlogApos : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogBpos : 0 < Real.log B := Real.log_pos (by linarith)
  have hlogAB : Real.log A <= Real.log B :=
    Real.log_le_log hApos hAB
  have hThetaA := hTheta A ⟨le_rfl, hAB⟩
  have hThetaB := hTheta B ⟨hAB, le_rfl⟩
  have hAterm :
      |thetaError A / Real.log A| <=
        C * B / Real.log A ^ 5 := by
    rw [abs_div, abs_of_pos hlogApos]
    calc
      |thetaError A| / Real.log A <=
          (C * A / Real.log A ^ 4) / Real.log A := by
        exact div_le_div_of_nonneg_right hThetaA hlogApos.le
      _ = C * A / Real.log A ^ 5 := by
        field_simp [ne_of_gt hApos, ne_of_gt hlogApos]
      _ <= C * B / Real.log A ^ 5 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAB hC)
          (pow_pos hlogApos 5).le
  have hBterm :
      |thetaError B / Real.log B| <=
        C * B / Real.log A ^ 5 := by
    rw [abs_div, abs_of_pos hlogBpos]
    calc
      |thetaError B| / Real.log B <=
          (C * B / Real.log B ^ 4) / Real.log B := by
        exact div_le_div_of_nonneg_right hThetaB hlogBpos.le
      _ = C * B / Real.log B ^ 5 := by
        field_simp [ne_of_gt hBpos, ne_of_gt hlogBpos]
      _ <= C * B / Real.log A ^ 5 := by
        exact div_le_div_of_nonneg_left (mul_nonneg hC hBpos.le)
          (pow_pos hlogApos 5) (pow_le_pow_left₀ hlogApos.le hlogAB 5)
  have hInt :
      |∫ t in A..B, fourFivePrimeCountingErrorKernel t| <=
        C * B / Real.log A ^ 5 := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fourFivePrimeCountingErrorKernel)
      (C := C / Real.log A ^ 5)
      (a := A) (b := B) (fun t ht => by
        rw [Real.norm_eq_abs]
        apply abs_fourFivePrimeCountingErrorKernel_le hA hAB hC
        · have ht' := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le hAB] using ht'
        · apply hTheta t
          have ht' := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le hAB] using ht')
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hAB)] at hnorm
    calc
      |∫ t in A..B, fourFivePrimeCountingErrorKernel t| <=
          (C / Real.log A ^ 5) * (B - A) := hnorm
      _ <= (C / Real.log A ^ 5) * B := by
        exact mul_le_mul_of_nonneg_left (by linarith [hA]) (by positivity)
      _ = C * B / Real.log A ^ 5 := by ring
  rw [fourFivePrimeCounting_sub_logIntegralIncrement_eq_thetaError
    (by linarith [hA]) hAB]
  calc
    |thetaError B / Real.log B - thetaError A / Real.log A +
        ∫ t in A..B, fourFivePrimeCountingErrorKernel t| <=
      |thetaError B / Real.log B| +
        |thetaError A / Real.log A| +
        |∫ t in A..B, fourFivePrimeCountingErrorKernel t| := by
      have h1 := abs_add_le
        (thetaError B / Real.log B - thetaError A / Real.log A)
        (∫ t in A..B, fourFivePrimeCountingErrorKernel t)
      have h2 := abs_sub
        (thetaError B / Real.log B) (thetaError A / Real.log A)
      linarith
    _ <= C * B / Real.log A ^ 5 +
        C * B / Real.log A ^ 5 +
        C * B / Real.log A ^ 5 := by linarith
    _ = 3 * C * B / Real.log A ^ 5 := by ring

/-- Literal logarithmic-integral corollary of the fifth-log endpoint
estimate. -/
theorem abs_fourFivePrimeCounting_sub_integral_inv_log_le
    {A B C : Real} (hA : 3 <= A) (hAB : A <= B) (hC : 0 <= C)
    (hTheta : ∀ t ∈ Icc A B,
      |thetaError t| <= C * t / Real.log t ^ 4) :
    abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        (∫ t in A..B, 1 / Real.log t)) <=
      3 * C * B / Real.log A ^ 5 := by
  rw [← fourFiveLogIntegralIncrement_eq_integral_inv_log
    (by linarith [hA]) hAB]
  exact abs_fourFivePrimeCounting_sub_logIntegralIncrement_le
    hA hAB hC hTheta

/-- Unconditional uniform endpoint theorem obtained from the repository's
audited theta-PNT.  One positive constant and one real cutoff work for every
later pair of endpoints. -/
theorem exists_abs_fourFivePrimeCounting_sub_logIntegralIncrement_le :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      forall A B : Real, X0 <= A -> A <= B ->
        abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
            (Nat.primeCounting ⌊A⌋₊ : Real)) -
            fourFiveLogIntegralIncrement A B) <=
          3 * C * B / Real.log A ^ 5 := by
  obtain ⟨C, hC, hbound⟩ :=
    (Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power
      (4 : Real)).exists_pos
  rw [Asymptotics.IsBigOWith, Filter.eventually_atTop] at hbound
  obtain ⟨X0, hTheta⟩ := hbound
  refine ⟨C, hC, max X0 3, le_max_right X0 3, ?_⟩
  intro A B hA hAB
  apply abs_fourFivePrimeCounting_sub_logIntegralIncrement_le
    ((le_max_right X0 3).trans hA) hAB hC.le
  intro t ht
  have htX0 : X0 <= t :=
    (le_max_left X0 3).trans (hA.trans ht.1)
  have ht3 : (3 : Real) <= t :=
    (le_max_right X0 3).trans (hA.trans ht.1)
  have htpos : 0 < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have htarget : 0 <= t / Real.log t ^ ((4 : Nat) : Real) := by positivity
  have hb := hTheta t htX0
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hb
  calc
    |thetaError t| = |Chebyshev.theta t - t| := rfl
    _ <= C * |t / Real.log t ^ ((4 : Nat) : Real)| := hb
    _ = C * (t / Real.log t ^ ((4 : Nat) : Real)) := by
      rw [abs_of_nonneg htarget]
    _ = C * t / Real.log t ^ 4 := by
      rw [Real.rpow_natCast]
      ring

/-- Unconditional literal `pi-li` endpoint estimate, with one constant and
cutoff uniform in both endpoints. -/
theorem exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      forall A B : Real, X0 <= A -> A <= B ->
        abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
            (Nat.primeCounting ⌊A⌋₊ : Real)) -
            (∫ t in A..B, 1 / Real.log t)) <=
          3 * C * B / Real.log A ^ 5 := by
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_abs_fourFivePrimeCounting_sub_logIntegralIncrement_le
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro A B hA hAB
  rw [← fourFiveLogIntegralIncrement_eq_integral_inv_log
    (by linarith [hX0, hA]) hAB]
  exact hbound A B hA hAB

end Erdos390.WholePaper.BankPaperRealization
