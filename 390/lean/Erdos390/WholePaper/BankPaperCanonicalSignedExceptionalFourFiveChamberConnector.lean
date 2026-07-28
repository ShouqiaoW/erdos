import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalOrderedMixtureConnector
import Erdos390.WholePaper.BankPaperCanonicalFourFiveKernelVariation

/-!
# Four/five chamber connector for the signed exceptional core

This file joins the four pieces which are already formalized separately.

* The ordered four/five estimate is converted to the paper rate on every
  certified exceptional physical interval.
* The continuum kernel is frozen at the literal coordinate
  `log((2n)/b) / log(yNat n)`.
* Natural quotient lengths are compared with the three ideal balanced
  lengths.
* Three frozen deep estimates and three positive cutoff estimates are
  assembled into the signed exceptional-core chamber.

The remaining input is deliberately exposed by
`RoughCanonicalSignedExceptionalFourFiveChamberInputAt`.  It consists of
the three interval estimates after the elementary displacement and clipping
budgets, together with the padded coordinate range for the prime-power
samples of the frozen kernel.  No unproved analytic assertion is hidden in
the connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The geometry-facing ordered-to-rough rate -/

/-- The natural upper scale attached to a physical interval at smooth core
`b`.  It is the scale supplied by
`RoughCanonicalExceptionalPhysicalIntervalGeometry`. -/
def roughCanonicalExceptionalPhysicalRateScale (n b : Nat) : Real :=
  (3 * n / b + 1 : Nat)

/-- The fixed coefficient in the ordered-to-rough paper-rate conversion. -/
def roughCanonicalFourFiveIntervalPaperRateConstant (C : Real) : Real :=
  125 * (1 +
    fourFiveSignedCoreAssemblyLogCubeConstant C
      fourFiveCompactReciprocalMass)

theorem roughCanonicalFourFiveIntervalPaperRateConstant_nonneg
    {C : Real} (hC : 0 <= C) :
    0 <= roughCanonicalFourFiveIntervalPaperRateConstant C := by
  unfold roughCanonicalFourFiveIntervalPaperRateConstant
  have hassembly :
      0 <= fourFiveSignedCoreAssemblyLogCubeConstant C
        fourFiveCompactReciprocalMass :=
    fourFiveSignedCoreAssemblyLogCubeConstant_nonneg
      hC fourFiveCompactReciprocalMass_pos.le
  positivity

/-- Eventually the elementary repeated-prime loss is bounded by the same
log-cube scale as the four/five assembly error. -/
theorem eventually_log_yNat_cube_le_yNat :
    ∀ᶠ n : Nat in atTop,
      Real.log (yNat n : Real) ^ 3 <= (yNat n : Real) := by
  have hreal :
      Tendsto
        (fun x : Real =>
          Real.log x ^ (3 : Real) / x ^ (1 : Real))
        atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop
      (3 : Real) (by norm_num : (0 : Real) < 1)).tendsto_div_nhds_zero
  have hyReal :
      Tendsto (fun n : Nat => (yNat n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      roughCanonicalExceptional_yNat_tendsto_atTop
  have hratio :
      Tendsto
        (fun n : Nat =>
          Real.log (yNat n : Real) ^ 3 / (yNat n : Real))
        atTop (nhds 0) := by
    simpa [Function.comp_def, Real.rpow_natCast, Real.rpow_one] using
      hreal.comp hyReal
  have hratioOne :
      ∀ᶠ n : Nat in atTop,
        Real.log (yNat n : Real) ^ 3 / (yNat n : Real) <= 1 :=
    hratio.eventually
      (eventually_le_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [
      hratioOne,
      roughCanonicalExceptional_yNat_tendsto_atTop.eventually
        (eventually_gt_atTop 0)]
      with n hnRatio hyPos
  have hyRealPos : (0 : Real) < (yNat n : Real) := by
    exact_mod_cast hyPos
  have hproduct := (div_le_iff₀ hyRealPos).mp hnRatio
  simpa only [one_mul] using hproduct

/-- Finite conversion of one geometry-certified ordered estimate to the
paper's `Z/L^3` rough-counting rate. -/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_mixtureIntegral_le_paperRate
    {n b A B : Nat} {deltaStar C : Real}
    (hn : 1 < n)
    (hC : 0 <= C)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= yNat n)
    (hlogOne : 1 <= Real.log (yNat n : Real))
    (hlogLeY : Real.log (yNat n : Real) <= (yNat n : Real))
    (hlogCubeLeY :
      Real.log (yNat n : Real) ^ 3 <= (yNat n : Real))
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hprimeMass :
      fourFivePrimeCoordinateReciprocalMass (yNat n) B <=
        fourFiveCompactReciprocalMass)
    (hordered :
      FourFiveOrderedPrimeMixtureEstimate (yNat n) A B
        (fourFiveContinuumMixtureIntegralMain (yNat n) A B)
        (fourFiveRealEndpointFullyBoundedAssemblyError
          C (yNat n) A B fourFiveCompactReciprocalMass)) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
      roughCanonicalFourFiveIntervalPaperRateConstant C *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) := by
  have hinputs := hgeometry.counting_inputs
  have hy : 2 <= yNat n :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hcut
  have hZ0 :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hL : 0 < L n := L_pos hn
  simpa only [
      roughCanonicalFourFiveIntervalPaperRateConstant,
      roughCanonicalExceptionalPhysicalRateScale] using
    (abs_fourFiveRoughInterval_card_sub_mixtureIntegral_le_paperRate
      (C := C) (M := fourFiveCompactReciprocalMass)
      (Z := roughCanonicalExceptionalPhysicalRateScale n b)
      (Lpaper := L n)
      hC fourFiveCompactReciprocalMass_pos.le
      hy hinputs.1 hinputs.2.1 hcut hinputs.2.2.1
      hinputs.2.2.2.1 hlogOne hlogLeY hlogCubeLeY
      hinputs.2.2.2.2.2 hZ0 hL hlogLower hprimeMass hordered)

/-- Uniform eventual rough-counting estimate for every certified exceptional
physical interval.  The constant is independent of `n`, the smooth core,
and both endpoints. -/
theorem
    exists_eventually_roughCanonicalExceptionalPhysicalInterval_paperRate
    {deltaStar : Real} :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop, ∀ b A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
              fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
            roughCanonicalFourFiveIntervalPaperRateConstant C *
              (roughCanonicalExceptionalPhysicalRateScale n b /
                L n ^ 3) := by
  obtain ⟨C, hC,
      horderedEventually⟩ :=
    exists_eventually_roughCanonicalExceptionalPhysicalInterval_orderedMixtureEstimate
      (deltaStar := deltaStar)
  refine ⟨C, hC, ?_⟩
  filter_upwards [
      horderedEventually,
      eventually_gt_atTop 1,
      roughCanonicalExceptional_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop fourFiveReciprocalBVSafeCutoff),
      roughCanonicalExceptional_log_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop 1),
      roughCanonicalExceptional_log_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop
          (5 * fullReciprocalSumUniformConstant)),
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_log_yNat_cube_le_yNat]
      with n horderedAll hn hcut hlogOne hlogConstant
        hlogLower hlogCubeLeY
  intro b A B hgeometry
  have hy : 2 <= yNat n :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hcut
  have hyRealPos : (0 : Real) < (yNat n : Real) := by
    exact_mod_cast (show 0 < yNat n by omega)
  have hlogLeY :
      Real.log (yNat n : Real) <= (yNat n : Real) := by
    have hlogSub :=
      Real.log_le_sub_one_of_pos hyRealPos
    linarith
  have herror :
      fourFiveReciprocalBVError (yNat n) <= 1 :=
    fourFiveReciprocalBVError_le_one_of_log_large
      hlogOne hlogConstant
  have hrange :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        fourFiveRealLogCoordinate (yNat n) t ∈
          Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
    simpa only [fourFiveRealLogCoordinate] using
      hgeometry.padded_log_range
  have hspan :=
    fourFiveLogLogPrimitive_sub_le_log_twentyfour_fifths_of_paperRange
      hy hgeometry.rough_cutoff_le_lower
      hgeometry.lower_le_upper hrange
  have hmass :=
    fourFive_actual_and_continuum_mass_le_compact
      hcut
      (hgeometry.rough_cutoff_le_lower.trans
        hgeometry.lower_le_upper)
      hspan herror
  have hprimeMass :
      fourFivePrimeCoordinateReciprocalMass (yNat n) B <=
        fourFiveCompactReciprocalMass := by
    have hmassEq :
        fourFivePrimeCoordinateReciprocalMass (yNat n) B =
          ∑ p ∈ Finset.Ioc (yNat n) B,
            |fourFiveAnchoredReciprocalPrimeAtom (yNat n) p| := by
      unfold fourFivePrimeCoordinateReciprocalMass
        fourFivePrimeCoordinateBand
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hyp : yNat n < p := (Finset.mem_Ioc.mp hp).1
      by_cases hprime : p.Prime
      · have hinv : 0 <= ((p : Real)⁻¹) := by positivity
        simp [fourFiveAnchoredReciprocalPrimeAtom,
          fourFiveReciprocalPrimeAtom, hyp, hprime, one_div,
          abs_of_nonneg hinv]
      · simp [fourFiveAnchoredReciprocalPrimeAtom,
          fourFiveReciprocalPrimeAtom, hyp, hprime]
    calc
      fourFivePrimeCoordinateReciprocalMass (yNat n) B =
          ∑ p ∈ Finset.Ioc (yNat n) B,
            |fourFiveAnchoredReciprocalPrimeAtom (yNat n) p| := hmassEq
      _ <= fourFiveCompactReciprocalMass := hmass.1
  exact
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_mixtureIntegral_le_paperRate
      hn hC.le hgeometry hcut hlogOne hlogLeY hlogCubeLeY
      hlogLower hprimeMass
      (horderedAll b A B hgeometry)

/-! ## One-interval freezing and quotient normalization -/

/-- Freeze a geometry-certified physical interval and replace its literal
natural length by an arbitrary ideal length.

The first term is the arithmetic-to-continuum error, the second is the
kernel displacement, and the last is the quotient/clipping endpoint loss.
-/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
    {n b A B : Nat} {deltaStar : Real}
    {arithmeticError Ckernel D u0 idealLength endpointError : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        arithmeticError)
    (hCkernel : 0 <= Ckernel) (hD : 0 <= D)
    (hendpointError : 0 <= endpointError)
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= Ckernel ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= Ckernel)
    (hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) - u0) <= D)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <= endpointError) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      arithmeticError +
        (((((B - A : Nat) : Real)) /
          Real.log (yNat n : Real)) * Ckernel) * D +
        (Ckernel / Real.log (yNat n : Real)) * endpointError := by
  have hAB := hgeometry.lower_le_upper
  have hlog : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hintegrable :=
    intervalIntegrable_fourFiveContinuumMixtureKernel_of_paperRange
      hy hgeometry.rough_cutoff_le_lower hAB
      hgeometry.padded_log_range
  have hfreeze0 :=
    abs_fourFiveContinuumMixtureIntegralMain_sub_frozen_le
      hAB hlog hCkernel hD hu0 hgeometry.padded_log_range
      hdisplacement (fun z hz => (hbound z hz).2) hintegrable
  have hfreeze :
      abs (fourFiveContinuumMixtureIntegralMain (yNat n) A B -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * ((B - A : Nat) : Real)) <=
        (((((B - A : Nat) : Real)) /
          Real.log (yNat n : Real)) * Ckernel) * D := by
    rw [show
      (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * ((B - A : Nat) : Real) =
        (((B : Real) - (A : Real)) /
          Real.log (yNat n : Real)) *
            fourFiveContinuumMixtureKernel u0 by
      rw [Nat.cast_sub hAB]
      ring]
    simpa only [Nat.cast_sub hAB] using hfreeze0
  have hkernel :
      abs (fourFiveContinuumMixtureKernel u0 /
        Real.log (yNat n : Real)) <=
          Ckernel / Real.log (yNat n : Real) := by
    rw [abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (hbound u0 hu0).1 hlog.le
  exact
    abs_count_sub_idealFrozen_le
      harithmetic hfreeze hlength hkernel
      hendpointError (div_nonneg hCkernel hlog.le)

/-- If clipping does not move the lower quotient endpoint, the literal
natural interval length differs from the ideal divided length by at most
one. -/
theorem
    abs_roughCanonicalExceptionalPhysicalEndpoint_length_sub_ideal_le_one
    {n b lo hi : Nat} {deltaStar : Real}
    (hb : 0 < b) (hlohi : lo <= hi)
    (hclip :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <= lo / b) :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b lo : Nat) : Real) -
        ((hi - lo : Nat) : Real) / (b : Real)) <= 1 := by
  simpa only [
      roughCanonicalExceptionalPhysicalUpperEndpoint,
      roughCanonicalExceptionalPhysicalLowerEndpoint,
      max_eq_left hclip] using
    (abs_natQuotientIntervalLength_sub_realLength_le_one
      hb hlohi)

/-- Simultaneous quotient-length normalization for the upper, high, and
broad intervals.  The three displayed no-clipping hypotheses isolate the
only obstruction introduced by the exceptional floor. -/
theorem
    roughCanonicalExceptional_threePhysicalInterval_quotient_lengths
    {n K0 b h : Nat} {deltaStar : Real}
    (hb : 0 < b) (hdepth : (K0 + 1) * h <= n)
    (hclipUpper :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n) / b)
    (hclipHigh :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n - (K0 + 1) * h) / b)
    (hclipBroad :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <= n / b) :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n + h) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Nat) : Real) -
        (h : Real) / (b : Real)) <= 1 ∧
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n - (K0 + 1) * h) : Nat) : Real) -
        (((K0 + 1) * h : Nat) : Real) / (b : Real)) <= 1 ∧
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * h) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Nat) : Real) -
        ((n - (K0 + 1) * h : Nat) : Real) / (b : Real)) <= 1 := by
  have hupper :=
    abs_roughCanonicalExceptionalPhysicalEndpoint_length_sub_ideal_le_one
      (n := n) (b := b) (lo := 2 * n) (hi := 2 * n + h)
      (deltaStar := deltaStar) hb (by omega) hclipUpper
  have hhigh :=
    abs_roughCanonicalExceptionalPhysicalEndpoint_length_sub_ideal_le_one
      (n := n) (b := b)
      (lo := 2 * n - (K0 + 1) * h) (hi := 2 * n)
      (deltaStar := deltaStar) hb (by omega) hclipHigh
  have hbroad :=
    abs_roughCanonicalExceptionalPhysicalEndpoint_length_sub_ideal_le_one
      (n := n) (b := b) (lo := n)
      (hi := 2 * n - (K0 + 1) * h)
      (deltaStar := deltaStar) hb (by omega) hclipBroad
  have hupperLength : 2 * n + h - 2 * n = h := by omega
  have hhighLength :
      2 * n - (2 * n - (K0 + 1) * h) = (K0 + 1) * h := by
    omega
  have hbroadLength :
      (2 * n - (K0 + 1) * h) - n =
        n - (K0 + 1) * h := by
    omega
  exact ⟨by simpa only [hupperLength] using hupper,
    by simpa only [hhighLength] using hhigh,
    by simpa only [hbroadLength] using hbroad⟩

/-! ## Three-interval certificates -/

/-- The three already-frozen, ideal-length estimates needed on a deep
smooth core. -/
structure RoughCanonicalSignedExceptionalDeepIntervalEstimate
    (K0 n b : Nat) (c deltaStar : Real)
    (Cplus Chigh Cbroad : Real) : Prop where
  upper :
    abs (((roughCanonicalExceptionalUpperPhysicalRoughInterval
          n (upperTailLength c n) deltaStar b).card : Real) -
        (fourFiveContinuumMixtureKernel
            (roughCanonicalFourFiveFrozenCoordinate n b) /
          Real.log (yNat n : Real)) *
            ((upperTailLength c n : Real) / (b : Real))) <=
      Cplus *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1)
  high :
    abs (((roughCanonicalExceptionalHighPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) -
        (fourFiveContinuumMixtureKernel
            (roughCanonicalFourFiveFrozenCoordinate n b) /
          Real.log (yNat n : Real)) *
            ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
              (b : Real))) <=
      Chigh *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1)
  broad :
    abs (((roughCanonicalExceptionalBroadPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) -
        (fourFiveContinuumMixtureKernel
            (roughCanonicalFourFiveFrozenCoordinate n b) /
          Real.log (yNat n : Real)) *
            (((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
              (b : Real))) <=
      Cbroad *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1)

/-- The three positive estimates needed on the one cutoff band. -/
structure RoughCanonicalSignedExceptionalCutoffIntervalEstimate
    (K0 n b : Nat) (c deltaStar : Real)
    (Cplus Chigh Cbroad : Real) : Prop where
  upper :
    ((roughCanonicalExceptionalUpperPhysicalRoughInterval
        n (upperTailLength c n) deltaStar b).card : Real) <=
      Cplus *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1)
  high :
    ((roughCanonicalExceptionalHighPhysicalRoughInterval
        n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) <=
      Chigh *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1)
  broad :
    ((roughCanonicalExceptionalBroadPhysicalRoughInterval
        n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) <=
      Cbroad *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)

/-! ## Replacing the physical upper scale by `n/b` -/

theorem roughCanonicalExceptionalPhysicalRateScale_div_L_cube_add_one_le
    {n b : Nat} (hb : 0 < b) (hLone : 1 <= L n) :
    roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1 <=
      4 * ((n : Real) / ((b : Real) * L n ^ 3) + 1) := by
  have hbReal : (0 : Real) < (b : Real) := by exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hscale :
      roughCanonicalExceptionalPhysicalRateScale n b <=
        3 * (n : Real) / (b : Real) + 1 := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    rw [Nat.cast_add, Nat.cast_one]
    calc
      ((3 * n / b : Nat) : Real) + 1 <=
          ((3 * n : Nat) : Real) / (b : Real) + 1 :=
        add_le_add Nat.cast_div_le le_rfl
      _ = 3 * (n : Real) / (b : Real) + 1 := by
        have hcast :
            ((3 * n : Nat) : Real) =
              (3 : Real) * (n : Real) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        exact congrArg
          (fun x : Real => x / (b : Real) + 1) hcast
  have hInv : 1 / L n ^ 3 <= 1 :=
    (div_le_one (pow_pos hL 3)).2 (one_le_pow₀ (n := 3) hLone)
  have hcore :
      0 <= (n : Real) / ((b : Real) * L n ^ 3) := by
    positivity
  calc
    roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1 <=
        (3 * (n : Real) / (b : Real) + 1) / L n ^ 3 + 1 :=
      add_le_add
        (div_le_div_of_nonneg_right hscale (pow_pos hL 3).le)
        le_rfl
    _ = 3 * ((n : Real) / ((b : Real) * L n ^ 3)) +
        1 / L n ^ 3 + 1 := by ring
    _ <= 4 * ((n : Real) / ((b : Real) * L n ^ 3) + 1) := by
      nlinarith

theorem roughCanonicalExceptionalPhysicalRateScale_div_L_sq_add_one_le
    {n b : Nat} (hb : 0 < b) (hLone : 1 <= L n) :
    roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1 <=
      4 * ((n : Real) / ((b : Real) * L n ^ 2) + 1) := by
  have hbReal : (0 : Real) < (b : Real) := by exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hscale :
      roughCanonicalExceptionalPhysicalRateScale n b <=
        3 * (n : Real) / (b : Real) + 1 := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    rw [Nat.cast_add, Nat.cast_one]
    calc
      ((3 * n / b : Nat) : Real) + 1 <=
          ((3 * n : Nat) : Real) / (b : Real) + 1 :=
        add_le_add Nat.cast_div_le le_rfl
      _ = 3 * (n : Real) / (b : Real) + 1 := by
        have hcast :
            ((3 * n : Nat) : Real) =
              (3 : Real) * (n : Real) := by
          norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        exact congrArg
          (fun x : Real => x / (b : Real) + 1) hcast
  have hInv : 1 / L n ^ 2 <= 1 :=
    (div_le_one (pow_pos hL 2)).2 (one_le_pow₀ (n := 2) hLone)
  have hcore :
      0 <= (n : Real) / ((b : Real) * L n ^ 2) := by
    positivity
  calc
    roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1 <=
        (3 * (n : Real) / (b : Real) + 1) / L n ^ 2 + 1 :=
      add_le_add
        (div_le_div_of_nonneg_right hscale (pow_pos hL 2).le)
        le_rfl
    _ = 3 * ((n : Real) / ((b : Real) * L n ^ 2)) +
        1 / L n ^ 2 + 1 := by ring
    _ <= 4 * ((n : Real) / ((b : Real) * L n ^ 2) + 1) := by
      nlinarith

/-! ## Signed deep and cutoff bounds -/

/-- The literal error left after removing the frozen periodic main term
from one signed smooth core. -/
def roughCanonicalFourFiveSignedExceptionalCoreError
    (W K0 n b : Nat) (c deltaStar beta : Real) : Real :=
  roughCanonicalSignedExceptionalCoreMass
      n (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadCompatibleRawWeight
        W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha
          W n (upperTailLength c n) (K0 + 1) beta (L n))
        beta (L n)) b -
    ((upperTailLength c n : Real) /
      Real.log (yNat n : Real)) *
      roughHeadPeriodicCoreCoefficient W b *
        roughCanonicalFourFiveFrozenKernelWeight n b

def roughCanonicalFourFiveDeepCoreConstant
    (W K0 : Nat) (c beta Cplus Chigh Cbroad : Real) : Real :=
  4 * (Cplus +
    roughBalancedAlphaConstant W K0 c beta * Chigh +
    abs beta * Cbroad)

def roughCanonicalFourFiveCutoffCoreConstant
    (W K0 : Nat) (c beta Cplus Chigh Cbroad : Real) : Real :=
  4 * (Cplus +
    roughBalancedAlphaConstant W K0 c beta * Chigh +
    abs beta * Cbroad)

theorem roughCanonicalFourFiveDeepCoreConstant_nonneg
    {W K0 : Nat} {c beta Cplus Chigh Cbroad : Real}
    (hc : 0 <= c) (hplus : 0 <= Cplus)
    (hhigh : 0 <= Chigh) (hbroad : 0 <= Cbroad) :
    0 <= roughCanonicalFourFiveDeepCoreConstant
      W K0 c beta Cplus Chigh Cbroad := by
  unfold roughCanonicalFourFiveDeepCoreConstant
  have hK : (0 : Real) < ((K0 + 1 : Nat) : Real) := by positivity
  have hdensity : 0 < roughHeadDensity W := roughHeadDensity_pos W
  have halpha :
      0 <= roughBalancedAlphaConstant W K0 c beta := by
    unfold roughBalancedAlphaConstant
    positivity
  positivity

theorem roughCanonicalFourFiveCutoffCoreConstant_nonneg
    {W K0 : Nat} {c beta Cplus Chigh Cbroad : Real}
    (hc : 0 <= c) (hplus : 0 <= Cplus)
    (hhigh : 0 <= Chigh) (hbroad : 0 <= Cbroad) :
    0 <= roughCanonicalFourFiveCutoffCoreConstant
      W K0 c beta Cplus Chigh Cbroad := by
  unfold roughCanonicalFourFiveCutoffCoreConstant
  have hK : (0 : Real) < ((K0 + 1 : Nat) : Real) := by positivity
  have hdensity : 0 < roughHeadDensity W := roughHeadDensity_pos W
  have halpha :
      0 <= roughBalancedAlphaConstant W K0 c beta := by
    unfold roughBalancedAlphaConstant
    positivity
  positivity

/-- Three frozen ideal-length estimates give the deep signed-core error at
the exact rate required by the core-first chamber. -/
theorem
    abs_roughCanonicalFourFiveSignedExceptionalCoreError_le_paperRate
    {W K0 n b : Nat} {c deltaStar beta : Real}
    {Cplus Chigh Cbroad : Real}
    (hc : 0 < c) (hn : 2 <= n)
    (hWy : W <= yNat n)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hcutY :
      2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n)
    (hLone : 1 <= L n)
    (hCplus : 0 <= Cplus) (hChigh : 0 <= Chigh)
    (hCbroad : 0 <= Cbroad)
    (hestimate :
      RoughCanonicalSignedExceptionalDeepIntervalEstimate
        K0 n b c deltaStar Cplus Chigh Cbroad) :
    abs (roughCanonicalFourFiveSignedExceptionalCoreError
        W K0 n b c deltaStar beta) <=
      roughCanonicalFourFiveDeepCoreConstant
          W K0 c beta Cplus Chigh Cbroad *
        ((n : Real) / ((b : Real) * L n ^ 3) + 1) := by
  have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
  have hrateNonneg :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    exact_mod_cast (Nat.zero_le (3 * n / b + 1))
  have hmass :=
    roughCanonicalSignedExceptionalCoreMass_paper_K0_succ_eq_threePhysicalIntervals
      (W := W) (n := n) (K0 := K0) (b := b)
      (c := c) (deltaStar := deltaStar) (beta := beta)
      (by omega) hWy hb hcutY
  have hbalanced :=
    abs_balanced_three_interval_sub_periodic_frozen_le_paperRate
      (W := W) (K0 := K0) (n := n) (b := b)
      (c := c) (beta := beta)
      (kernelValue :=
        fourFiveContinuumMixtureKernel
          (roughCanonicalFourFiveFrozenCoordinate n b))
      (Nplus :=
        ((roughCanonicalExceptionalUpperPhysicalRoughInterval
          n (upperTailLength c n) deltaStar b).card : Real))
      (Nhigh :=
        ((roughCanonicalExceptionalHighPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real))
      (Nbroad :=
        ((roughCanonicalExceptionalBroadPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real))
      (Cplus := Cplus) (Chigh := Chigh) (Cbroad := Cbroad)
      (Z := roughCanonicalExceptionalPhysicalRateScale n b)
      hc hn hLone hrateNonneg
      hestimate.upper hestimate.high hestimate.broad
      hCplus hChigh hCbroad
  have hraw :
      abs (roughCanonicalFourFiveSignedExceptionalCoreError
          W K0 n b c deltaStar beta) <=
        (Cplus +
          roughBalancedAlphaConstant W K0 c beta * Chigh +
          abs beta * Cbroad) *
            (roughCanonicalExceptionalPhysicalRateScale n b /
              L n ^ 3 + 1) := by
    unfold roughCanonicalFourFiveSignedExceptionalCoreError
    rw [hmass, roughCanonicalFourFiveFrozenKernelWeight,
      if_neg (Nat.ne_of_gt hbPos)]
    by_cases hcop : Nat.Coprime b (roughHeadModulus W)
    · simp_rw [if_pos hcop] at hbalanced ⊢
      convert hbalanced using 1; ring
    · simp_rw [if_neg hcop] at hbalanced ⊢
      convert hbalanced using 1; ring
  have hcoefficient :
      0 <= Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        abs beta * Cbroad := by
    have halpha :=
      roughBalancedAlphaConstant_nonneg W K0
        (beta := beta) hc
    positivity
  have hscale :=
    roughCanonicalExceptionalPhysicalRateScale_div_L_cube_add_one_le
      hbPos hLone
  calc
    abs (roughCanonicalFourFiveSignedExceptionalCoreError
        W K0 n b c deltaStar beta) <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        abs beta * Cbroad) *
          (roughCanonicalExceptionalPhysicalRateScale n b /
            L n ^ 3 + 1) := hraw
    _ <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        abs beta * Cbroad) *
          (4 * ((n : Real) / ((b : Real) * L n ^ 3) + 1)) :=
      mul_le_mul_of_nonneg_left hscale hcoefficient
    _ =
      roughCanonicalFourFiveDeepCoreConstant
          W K0 c beta Cplus Chigh Cbroad *
        ((n : Real) / ((b : Real) * L n ^ 3) + 1) := by
      unfold roughCanonicalFourFiveDeepCoreConstant
      ring

/-- Three positive cutoff-band estimates give the cutoff clause required
by the core-first chamber. -/
theorem
    abs_roughCanonicalSignedExceptionalCoreMass_le_cutoffPaperRate
    {W K0 n b : Nat} {c deltaStar beta : Real}
    {Cplus Chigh Cbroad : Real}
    (hc : 0 < c) (hn : 2 <= n)
    (hWy : W <= yNat n)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hcutY :
      2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n)
    (hLone : 1 <= L n)
    (hCplus : 0 <= Cplus) (hChigh : 0 <= Chigh)
    (hCbroad : 0 <= Cbroad)
    (hestimate :
      RoughCanonicalSignedExceptionalCutoffIntervalEstimate
        K0 n b c deltaStar Cplus Chigh Cbroad) :
    abs (roughCanonicalSignedExceptionalCoreMass
        n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadCompatibleRawWeight
          W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha
            W n (upperTailLength c n) (K0 + 1) beta (L n))
          beta (L n)) b) <=
      roughCanonicalFourFiveCutoffCoreConstant
          W K0 c beta Cplus Chigh Cbroad *
        ((n : Real) / ((b : Real) * L n ^ 2) + 1) := by
  have hbPos : 0 < b := (Finset.mem_Icc.mp hb).1
  have hmass :=
    roughCanonicalSignedExceptionalCoreMass_paper_K0_succ_eq_threePhysicalIntervals
      (W := W) (n := n) (K0 := K0) (b := b)
      (c := c) (deltaStar := deltaStar) (beta := beta)
      (by omega) hWy hb hcutY
  have hbalanced :=
    abs_balanced_three_interval_cutoff_le_paperRate
      (W := W) (K0 := K0) (n := n) (b := b)
      (c := c) (beta := beta)
      (Nplus :=
        ((roughCanonicalExceptionalUpperPhysicalRoughInterval
          n (upperTailLength c n) deltaStar b).card : Real))
      (Nhigh :=
        ((roughCanonicalExceptionalHighPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real))
      (Nbroad :=
        ((roughCanonicalExceptionalBroadPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real))
      (Cplus := Cplus) (Chigh := Chigh) (Cbroad := Cbroad)
      (Z := roughCanonicalExceptionalPhysicalRateScale n b)
      hc hn hLone (by
        unfold roughCanonicalExceptionalPhysicalRateScale
        exact Nat.cast_nonneg _)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hestimate.upper hestimate.high hestimate.broad
      hCplus hChigh hCbroad
  have hraw :
      abs (roughCanonicalSignedExceptionalCoreMass
          n (upperTailLength c n) (K0 + 1) deltaStar
          (roughHeadCompatibleRawWeight
            W n (upperTailLength c n) (K0 + 1)
            (roughHeadBalancedAlpha
              W n (upperTailLength c n) (K0 + 1) beta (L n))
            beta (L n)) b) <=
        (Cplus +
          roughBalancedAlphaConstant W K0 c beta * Chigh +
          abs beta * Cbroad) *
            (roughCanonicalExceptionalPhysicalRateScale n b /
              L n ^ 2 + 1) := by
    rw [hmass]
    by_cases hcop : Nat.Coprime b (roughHeadModulus W)
    · simpa only [if_pos hcop, one_mul] using hbalanced
    · simpa only [if_neg hcop, zero_mul, add_zero, sub_zero] using hbalanced
  have hcoefficient :
      0 <= Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        abs beta * Cbroad := by
    have halpha :=
      roughBalancedAlphaConstant_nonneg W K0
        (beta := beta) hc
    positivity
  have hscale :=
    roughCanonicalExceptionalPhysicalRateScale_div_L_sq_add_one_le
      hbPos hLone
  calc
    _ <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        abs beta * Cbroad) *
          (roughCanonicalExceptionalPhysicalRateScale n b /
            L n ^ 2 + 1) := hraw
    _ <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        abs beta * Cbroad) *
          (4 * ((n : Real) / ((b : Real) * L n ^ 2) + 1)) :=
      mul_le_mul_of_nonneg_left hscale hcoefficient
    _ =
      roughCanonicalFourFiveCutoffCoreConstant
          W K0 c beta Cplus Chigh Cbroad *
        ((n : Real) / ((b : Real) * L n ^ 2) + 1) := by
      unfold roughCanonicalFourFiveCutoffCoreConstant
      ring

/-! ## Exact remaining chamber input -/

/-- The exact information not supplied by the present four/five library at
one value of `n`.

The deep and cutoff fields are the six interval consequences of the
displacement/clipping analysis.  The final field is the padded-coordinate
geometry needed by the already proved frozen-kernel variation theorem.
-/
structure RoughCanonicalSignedExceptionalFourFiveChamberInputAt
    (W K0 n : Nat) (c deltaStar : Real)
    (deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real) : Prop where
  n_two : 2 <= n
  head_le_yNat : W <= yNat n
  core_cutoff_le_yNat :
    2 * tangentPaperExceptionalCutoff deltaStar n <= yNat n
  log_scale_one : 1 <= L n
  log_yNat_one : 1 <= Real.log (yNat n : Real)
  deep_intervals :
    ∀ b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n,
      RoughCanonicalSignedExceptionalDeepIntervalEstimate
        K0 n b c deltaStar deepPlus deepHigh deepBroad
  cutoff_intervals :
    ∀ b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n,
      RoughCanonicalSignedExceptionalCutoffIntervalEstimate
        K0 n b c deltaStar cutoffPlus cutoffHigh cutoffBroad
  variation_coordinates :
    ∀ p : Nat, p.Prime -> W < p ->
      ∀ k ∈ positiveExponents
          (tangentPaperExceptionalCutoff deltaStar n / 2),
        ∀ m ∈ Finset.Icc 1
            ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k),
          roughCanonicalFourFiveFrozenCoordinate n (p ^ k * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)

/-- Eventual form of the exact remaining six interval estimates and the
prime-power coordinate geometry. -/
def RoughCanonicalSignedExceptionalFourFiveRemainingInputs
    (W K0 : Nat) (c deltaStar : Real)
    (deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real) : Prop :=
  ∀ᶠ n : Nat in atTop,
    RoughCanonicalSignedExceptionalFourFiveChamberInputAt
      W K0 n c deltaStar
      deepPlus deepHigh deepBroad cutoffPlus cutoffHigh cutoffBroad

/-! ## Chamber and final residual assembly -/

/-- One finite remaining-input certificate, together with the already
proved uniform kernel variation theorem, gives the complete isolated
core-first chamber. -/
theorem
    roughCanonicalSignedExceptionalCoreChamberEstimate_of_fourFiveInput
    {W K0 n : Nat} {c deltaStar beta : Real}
    {deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad Cvariation : Real}
    (hc : 0 < c)
    (hdeepPlus : 0 <= deepPlus) (hdeepHigh : 0 <= deepHigh)
    (hdeepBroad : 0 <= deepBroad)
    (hcutoffPlus : 0 <= cutoffPlus)
    (hcutoffHigh : 0 <= cutoffHigh)
    (hcutoffBroad : 0 <= cutoffBroad)
    (hinput :
      RoughCanonicalSignedExceptionalFourFiveChamberInputAt
        W K0 n c deltaStar
        deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad)
    (hvariation :
      ∀ n D B : Nat,
        0 < n ->
        0 < D ->
        1 <= Real.log (yNat n : Real) ->
        (∀ m ∈ Finset.Icc 1 B,
          roughCanonicalFourFiveFrozenCoordinate n (D * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ->
        roughCoreDiscreteVariation
            (fun m =>
              roughCanonicalFourFiveFrozenKernelWeight n (D * m)) B <=
          Cvariation / (D : Real)) :
    RoughCanonicalSignedExceptionalCoreChamberEstimate
      W n (upperTailLength c n) (K0 + 1) deltaStar
      (roughHeadCompatibleRawWeight
        W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha
          W n (upperTailLength c n) (K0 + 1) beta (L n))
        beta (L n))
      (roughCanonicalFourFiveFrozenKernelWeight n)
      (roughCanonicalFourFiveSignedExceptionalCoreError
        W K0 n · c deltaStar beta)
      (roughCanonicalFourFiveDeepCoreConstant
        W K0 c beta deepPlus deepHigh deepBroad)
      (roughCanonicalFourFiveCutoffCoreConstant
        W K0 c beta cutoffPlus cutoffHigh cutoffBroad)
      Cvariation := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    unfold roughCanonicalFourFiveSignedExceptionalCoreError
    ring
  · intro b hb
    have hbData :
        b ∈ Finset.Icc 1
          (tangentPaperExceptionalCutoff deltaStar n / 2) := by
      simpa only [roughCanonicalExceptionalDeepCoreSet] using hb
    have hbPrefix :
        b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n) := by
      exact Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp hbData).1, by
          have := (Finset.mem_Icc.mp hbData).2
          omega⟩
    exact
      abs_roughCanonicalFourFiveSignedExceptionalCoreError_le_paperRate
        hc hinput.n_two hinput.head_le_yNat hbPrefix
        hinput.core_cutoff_le_yNat hinput.log_scale_one
        hdeepPlus hdeepHigh hdeepBroad
        (hinput.deep_intervals b hb)
  · intro b hb
    have hbData :
        b ∈ Finset.Ioc
          (tangentPaperExceptionalCutoff deltaStar n / 2)
          (2 * tangentPaperExceptionalCutoff deltaStar n) := by
      simpa only [roughCanonicalExceptionalCutoffCoreSet] using hb
    have hbPrefix :
        b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n) := by
      exact Finset.mem_Icc.mpr
        ⟨by
          have := (Finset.mem_Ioc.mp hbData).1
          omega,
        (Finset.mem_Ioc.mp hbData).2⟩
    exact
      abs_roughCanonicalSignedExceptionalCoreMass_le_cutoffPaperRate
        hc hinput.n_two hinput.head_le_yNat hbPrefix
        hinput.core_cutoff_le_yNat hinput.log_scale_one
        hcutoffPlus hcutoffHigh hcutoffBroad
        (hinput.cutoff_intervals b hb)
  · intro p hp hWp k hk
    exact
      hvariation n (p ^ k)
        ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k)
        (lt_of_lt_of_le (by norm_num) hinput.n_two)
        (pow_pos hp.pos k) hinput.log_yNat_one
        (hinput.variation_coordinates p hp hWp k hk)

/-- The remaining interval input produces a fixed variation constant and an
eventual isolated chamber. -/
theorem
    exists_roughCanonicalSignedExceptionalCoreChamberEventually_of_fourFiveInputs
    {W K0 : Nat} {c deltaStar beta : Real}
    {deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real}
    (hc : 0 < c)
    (hdeepPlus : 0 <= deepPlus) (hdeepHigh : 0 <= deepHigh)
    (hdeepBroad : 0 <= deepBroad)
    (hcutoffPlus : 0 <= cutoffPlus)
    (hcutoffHigh : 0 <= cutoffHigh)
    (hcutoffBroad : 0 <= cutoffBroad)
    (hinputs :
      RoughCanonicalSignedExceptionalFourFiveRemainingInputs
        W K0 c deltaStar
        deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad) :
    ∃ Cvariation : Real, 0 < Cvariation ∧
      RoughCanonicalSignedExceptionalCoreChamberEventually
        W (K0 + 1) c deltaStar beta
        (roughCanonicalFourFiveDeepCoreConstant
          W K0 c beta deepPlus deepHigh deepBroad)
        (roughCanonicalFourFiveCutoffCoreConstant
          W K0 c beta cutoffPlus cutoffHigh cutoffBroad)
        Cvariation := by
  obtain ⟨Cvariation, hCvariation, hvariation⟩ :=
    exists_roughCanonicalFourFiveFrozenKernelVariationConstant
  refine ⟨Cvariation, hCvariation, ?_⟩
  unfold RoughCanonicalSignedExceptionalCoreChamberEventually
  unfold RoughCanonicalSignedExceptionalFourFiveRemainingInputs at hinputs
  filter_upwards [hinputs] with n hinput
  refine ⟨roughCanonicalFourFiveFrozenKernelWeight n,
    (roughCanonicalFourFiveSignedExceptionalCoreError
      W K0 n · c deltaStar beta), ?_⟩
  exact
    roughCanonicalSignedExceptionalCoreChamberEstimate_of_fourFiveInput
      hc hdeepPlus hdeepHigh hdeepBroad
      hcutoffPlus hcutoffHigh hcutoffBroad hinput hvariation

/-- Final conditional closure: once the explicitly named six interval
estimates and coordinate geometry are supplied, the existing core-first
ledger gives the strict signed exceptional residual bound. -/
theorem
    exists_eventually_roughCanonicalSignedExceptionalResidualBound_of_fourFiveInputs
    {W K0 : Nat} {c deltaStar beta : Real}
    {deepPlus deepHigh deepBroad
      cutoffPlus cutoffHigh cutoffBroad : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hdeepPlus : 0 <= deepPlus) (hdeepHigh : 0 <= deepHigh)
    (hdeepBroad : 0 <= deepBroad)
    (hcutoffPlus : 0 <= cutoffPlus)
    (hcutoffHigh : 0 <= cutoffHigh)
    (hcutoffBroad : 0 <= cutoffBroad)
    (hinputs :
      RoughCanonicalSignedExceptionalFourFiveRemainingInputs
        W K0 c deltaStar
        deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad) :
    ∃ Cvariation : Real, 0 < Cvariation ∧
      ∀ᶠ n : Nat in atTop, ∀ p : Nat,
        p.Prime -> W < p -> p <= yNat n ->
        RoughCanonicalSignedExceptionalResidualBound
          n (upperTailLength c n) (K0 + 1) deltaStar
          (roughHeadCompatibleRawWeight
            W n (upperTailLength c n) (K0 + 1)
            (roughHeadBalancedAlpha
              W n (upperTailLength c n) (K0 + 1) beta (L n))
            beta (L n))
          p
          (roughCanonicalSignedExceptionalCoreBoundConstant
            W c deltaStar
            (roughCanonicalFourFiveDeepCoreConstant
              W K0 c beta deepPlus deepHigh deepBroad)
            (roughCanonicalFourFiveCutoffCoreConstant
              W K0 c beta cutoffPlus cutoffHigh cutoffBroad)
            Cvariation *
              secondOrderScale n / ((p : Real) * L n)) := by
  obtain ⟨Cvariation, hCvariation, hchamber⟩ :=
    exists_roughCanonicalSignedExceptionalCoreChamberEventually_of_fourFiveInputs
      hc hdeepPlus hdeepHigh hdeepBroad
      hcutoffPlus hcutoffHigh hcutoffBroad hinputs
  refine ⟨Cvariation, hCvariation, ?_⟩
  exact
    eventually_roughCanonicalSignedExceptionalResidualBound_of_coreChamber
      hc hdelta hdeltaUpper
      (roughCanonicalFourFiveDeepCoreConstant_nonneg
        hc.le hdeepPlus hdeepHigh hdeepBroad)
      (roughCanonicalFourFiveCutoffCoreConstant_nonneg
        hc.le hcutoffPlus hcutoffHigh hcutoffBroad)
      hCvariation.le hchamber

end BankPaperRealization

end

end Erdos390.WholePaper
