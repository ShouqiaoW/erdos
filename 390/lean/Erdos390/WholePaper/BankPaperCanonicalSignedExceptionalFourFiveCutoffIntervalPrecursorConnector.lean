import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveChamberConnector

/-!
# Positive cutoff-interval precursor for the signed four/five chamber

The cutoff band does not need a frozen main term.  On every nonempty
geometry-certified interval we freeze at the fixed padded endpoint `4.1`,
choose ideal length zero, and charge the literal interval span as endpoint
error.  The choices

`u0 = 41/10`, `D = 3/5`, `idealLength = 0`

therefore turn the existing freezing adapter into a positive cardinality
bound.  Empty intervals contribute zero.

This file also proves the generic clipped-span estimate and scales the upper
and high spans to `Z/L^2`, and the broad span to `Z/L`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Generic clipped spans -/

/-- Clipping the lower quotient endpoint can only shorten an interval.
Consequently its natural span is bounded by the ideal physical length
divided by the core, plus the single quotient-rounding unit. -/
theorem roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
    {n b lo hi : Nat} {deltaStar : Real}
    (hb : 0 < b) (hlohi : lo <= hi) :
    ((roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo : Nat) : Real) <=
      ((hi - lo : Nat) : Real) / (b : Real) + 1 := by
  have hlower :
      lo / b <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo := by
    unfold roughCanonicalExceptionalPhysicalLowerEndpoint
    exact le_max_left _ _
  have hspanNat :
      roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b lo <=
        hi / b - lo / b := by
    unfold roughCanonicalExceptionalPhysicalUpperEndpoint
    omega
  calc
    ((roughCanonicalExceptionalPhysicalUpperEndpoint b hi -
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo : Nat) : Real) <=
        ((hi / b - lo / b : Nat) : Real) := by
      exact_mod_cast hspanNat
    _ <= ((hi - lo : Nat) : Real) / (b : Real) + 1 :=
      roughQuotientGap_cast_le hb hlohi

/-- The real core quotient is dominated by the paper-rate scale
`3*n/b+1`, including all natural quotient rounding. -/
theorem roughCanonicalExceptional_self_div_core_le_physicalRateScale
    {n b : Nat} (hb : 0 < b) :
    (n : Real) / (b : Real) <=
      roughCanonicalExceptionalPhysicalRateScale n b := by
  have hround :
      (n : Real) / (b : Real) <
        ((n / b : Nat) : Real) + 1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := n) hb
  have hmono : n / b <= (3 * n) / b :=
    Nat.div_le_div_right (by omega)
  have hcast :
      ((n / b : Nat) : Real) + 1 <=
        (((3 * n) / b : Nat) : Real) + 1 := by
    exact add_le_add (by exact_mod_cast hmono) le_rfl
  unfold roughCanonicalExceptionalPhysicalRateScale
  rw [Nat.cast_add, Nat.cast_one]
  exact (hround.trans_le hcast).le

/-! ## Freezing at the fixed padded endpoint -/

/-- A geometry-certified interval can be frozen at `4.1` with zero ideal
length.  The literal span pays its own endpoint error, while the padded
coordinate range gives displacement at most `0.6`. -/
theorem
    fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
    {n b A B : Nat} {deltaStar arithmeticError Ckernel : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        arithmeticError)
    (hCkernel : 0 <= Ckernel)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= Ckernel ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= Ckernel) :
    ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
      arithmeticError +
        (8 / 5 : Real) * Ckernel *
          (((B - A : Nat) : Real) /
            Real.log (yNat n : Real)) := by
  have hspanNonneg :
      0 <= ((B - A : Nat) : Real) := Nat.cast_nonneg _
  have hu0 :
      ((41 : Real) / 10) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
    norm_num
  have hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) -
          (41 : Real) / 10) <= (3 : Real) / 5 := by
    intro t ht
    have hz := hgeometry.padded_log_range t ht
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1)]
    linarith [hz.2]
  have hlength :
      abs (((B - A : Nat) : Real) - 0) <=
        ((B - A : Nat) : Real) := by
    have habs :
        abs (((B - A : Nat) : Real) - 0) =
          ((B - A : Nat) : Real) := by
      rw [sub_zero, abs_of_nonneg hspanNonneg]
    exact habs.le
  have hadapter :=
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
      (arithmeticError := arithmeticError)
      (Ckernel := Ckernel) (D := (3 : Real) / 5)
      (u0 := (41 : Real) / 10) (idealLength := 0)
      (endpointError := ((B - A : Nat) : Real))
      hy hgeometry harithmetic hCkernel (by norm_num)
      hspanNonneg hu0 hbound hdisplacement hlength
  have hcardNonneg :
      0 <= ((fourFiveRoughInterval (yNat n) A B).card : Real) :=
    Nat.cast_nonneg _
  calc
    ((fourFiveRoughInterval (yNat n) A B).card : Real) =
        abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          (fourFiveContinuumMixtureKernel ((41 : Real) / 10) /
            Real.log (yNat n : Real)) * 0) := by
      rw [mul_zero, sub_zero, abs_of_nonneg hcardNonneg]
    _ <= arithmeticError +
        (((((B - A : Nat) : Real)) /
          Real.log (yNat n : Real)) * Ckernel) * ((3 : Real) / 5) +
        (Ckernel / Real.log (yNat n : Real)) *
          ((B - A : Nat) : Real) := hadapter
    _ = arithmeticError +
        (8 / 5 : Real) * Ckernel *
          (((B - A : Nat) : Real) /
            Real.log (yNat n : Real)) := by ring

/-! ## Span scaling -/

/-- A short physical span `H` satisfying the paper tail bound gives the
cutoff `Z/L^2+1` scale after division by `log(yNat)`. -/
theorem roughCanonicalExceptional_shortClippedSpan_div_log_le
    {n b : Nat} {H span a : Real}
    (hb : 0 < b)
    (ha : 0 <= a) (_hspanNonneg : 0 <= span)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hH : 0 <= H)
    (hHupper : H <= 2 * a * (n : Real) / L n)
    (hspan : span <= H / (b : Real) + 1) :
    span / Real.log (yNat n : Real) <=
      (10 * a + 5) *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hcore :=
    roughCanonicalExceptional_self_div_core_le_physicalRateScale
      (n := n) hb
  have hHdiv :
      H / (b : Real) <=
        2 * a *
          roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    calc
      H / (b : Real) <=
          (2 * a * (n : Real) / L n) / (b : Real) :=
        div_le_div_of_nonneg_right hHupper hbReal.le
      _ = (2 * a / L n) * ((n : Real) / (b : Real)) := by
        field_simp [hL.ne', hbReal.ne']
      _ <= (2 * a / L n) *
          roughCanonicalExceptionalPhysicalRateScale n b :=
        mul_le_mul_of_nonneg_left hcore
          (div_nonneg (mul_nonneg (by norm_num) ha) hL.le)
      _ = 2 * a *
          roughCanonicalExceptionalPhysicalRateScale n b / L n := by ring
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hspanLog :
      span / Real.log (yNat n : Real) <=
        (2 * a *
            roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) *
          (5 / L n) := by
    calc
      span / Real.log (yNat n : Real) =
          span * (1 / Real.log (yNat n : Real)) := by ring
      _ <= (H / (b : Real) + 1) * (5 / L n) :=
        mul_le_mul hspan hinvLog
          (one_div_nonneg.mpr hlog.le)
          (add_nonneg (div_nonneg hH hbReal.le) (by norm_num))
      _ <=
          (2 * a *
              roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) *
            (5 / L n) :=
        mul_le_mul_of_nonneg_right
          (add_le_add hHdiv le_rfl) (div_nonneg (by norm_num) hL.le)
  have hInvL : 5 / L n <= 5 := by
    exact (div_le_iff₀ hL).2 (by nlinarith)
  let x :=
    roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2
  have hx : 0 <= x := by
    dsimp only [x]
    exact div_nonneg
      (by
        unfold roughCanonicalExceptionalPhysicalRateScale
        exact Nat.cast_nonneg _)
      (sq_nonneg (L n))
  calc
    span / Real.log (yNat n : Real) <=
        (2 * a *
            roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) *
          (5 / L n) := hspanLog
    _ =
        10 * a *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2) +
          5 / L n := by ring
    _ <= 10 * a * x + 5 := by
      dsimp only [x]
      exact add_le_add le_rfl hInvL
    _ <= (10 * a + 5) * x + (10 * a + 5) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) hx)
        (by linarith)
    _ = (10 * a + 5) *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
      dsimp only [x]
      ring

/-- A broad physical span at most `n/b+1` gives the cutoff `Z/L+1`
scale after division by `log(yNat)`. -/
theorem roughCanonicalExceptional_broadClippedSpan_div_log_le
    {n b : Nat} {span : Real}
    (hb : 0 < b) (_hspanNonneg : 0 <= span)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hspan : span <= (n : Real) / (b : Real) + 1) :
    span / Real.log (yNat n : Real) <=
      5 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hcore :=
    roughCanonicalExceptional_self_div_core_le_physicalRateScale
      (n := n) hb
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hspanLog :
      span / Real.log (yNat n : Real) <=
        (roughCanonicalExceptionalPhysicalRateScale n b + 1) *
          (5 / L n) := by
    calc
      span / Real.log (yNat n : Real) =
          span * (1 / Real.log (yNat n : Real)) := by ring
      _ <= ((n : Real) / (b : Real) + 1) * (5 / L n) :=
        mul_le_mul hspan hinvLog
          (one_div_nonneg.mpr hlog.le)
          (add_nonneg (div_nonneg (Nat.cast_nonneg n) hbReal.le)
            (by norm_num))
      _ <=
          (roughCanonicalExceptionalPhysicalRateScale n b + 1) *
            (5 / L n) :=
        mul_le_mul_of_nonneg_right
          (add_le_add hcore le_rfl) (div_nonneg (by norm_num) hL.le)
  have hInvL : 5 / L n <= 5 := by
    exact (div_le_iff₀ hL).2 (by nlinarith)
  calc
    span / Real.log (yNat n : Real) <=
        (roughCanonicalExceptionalPhysicalRateScale n b + 1) *
          (5 / L n) := hspanLog
    _ =
        5 * (roughCanonicalExceptionalPhysicalRateScale n b / L n) +
          5 / L n := by ring
    _ <=
        5 * (roughCanonicalExceptionalPhysicalRateScale n b / L n) +
          5 := add_le_add le_rfl hInvL
    _ = 5 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
      ring

/-- The arithmetic paper rate is stronger than the cutoff square-log rate. -/
theorem roughCanonicalExceptional_paperRate_le_cutoffSqRate
    {n b : Nat} {P : Real}
    (hP : 0 <= P) (hLone : 1 <= L n) :
    P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) <=
      P *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hLsqLeCube : L n ^ 2 <= L n ^ 3 := by
    calc
      L n ^ 2 = L n ^ 2 * 1 := by ring
      _ <= L n ^ 2 * L n :=
        mul_le_mul_of_nonneg_left hLone (sq_nonneg (L n))
      _ = L n ^ 3 := by ring
  have hrate :
      roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 := by
    exact
      div_le_div_of_nonneg_left
        (by
          unfold roughCanonicalExceptionalPhysicalRateScale
          exact Nat.cast_nonneg _)
        (sq_pos_of_pos hL) hLsqLeCube
  exact mul_le_mul_of_nonneg_left
    (hrate.trans (le_add_of_nonneg_right (by norm_num))) hP

/-- The arithmetic paper rate is also stronger than the broad cutoff rate. -/
theorem roughCanonicalExceptional_paperRate_le_cutoffBroadRate
    {n b : Nat} {P : Real}
    (hP : 0 <= P) (hLone : 1 <= L n) :
    P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) <=
      P *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hLLeCube : L n <= L n ^ 3 := by
    have hLsq : 1 <= L n ^ 2 :=
      one_le_pow₀ (n := 2) hLone
    calc
      L n = L n * 1 := by ring
      _ <= L n * L n ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq hL.le
      _ = L n ^ 3 := by ring
  have hrate :
      roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    exact
      div_le_div_of_nonneg_left
        (by
          unfold roughCanonicalExceptionalPhysicalRateScale
          exact Nat.cast_nonneg _)
        hL hLLeCube
  exact mul_le_mul_of_nonneg_left
    (hrate.trans (le_add_of_nonneg_right (by norm_num))) hP

/-! ## Three cutoff constants -/

def roughCanonicalFourFiveCutoffUpperEstimateConstant
    (P Ckernel c : Real) : Real :=
  P + (8 / 5 : Real) * Ckernel * (10 * c + 5)

def roughCanonicalFourFiveCutoffHighEstimateConstant
    (K0 : Nat) (P Ckernel c : Real) : Real :=
  P + (8 / 5 : Real) * Ckernel *
    (10 * (((K0 + 1 : Nat) : Real) * c) + 5)

def roughCanonicalFourFiveCutoffBroadEstimateConstant
    (P Ckernel : Real) : Real :=
  P + 8 * Ckernel

theorem roughCanonicalFourFiveCutoffUpperEstimateConstant_nonneg
    {P Ckernel c : Real}
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel) (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c := by
  unfold roughCanonicalFourFiveCutoffUpperEstimateConstant
  positivity

theorem roughCanonicalFourFiveCutoffHighEstimateConstant_nonneg
    (K0 : Nat) {P Ckernel c : Real}
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel) (hc : 0 <= c) :
    0 <=
      roughCanonicalFourFiveCutoffHighEstimateConstant K0 P Ckernel c := by
  unfold roughCanonicalFourFiveCutoffHighEstimateConstant
  positivity

theorem roughCanonicalFourFiveCutoffBroadEstimateConstant_nonneg
    {P Ckernel : Real}
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel) :
    0 <= roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel := by
  unfold roughCanonicalFourFiveCutoffBroadEstimateConstant
  positivity

/-! ## Finite geometry-or-empty cutoff assembly -/

theorem roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
    {K0 n b : Nat} {c deltaStar P Ckernel : Real}
    (hy : 2 <= yNat n) (hc : 0 <= c)
    (hP : 0 <= P) (hCkernel : 0 <= Ckernel)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (hb :
      b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= Ckernel ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= Ckernel)
    (harithmetic :
      ∀ A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
              fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
            P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hintervals :
      (RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n))
          (roughCanonicalExceptionalPhysicalUpperEndpoint
            b (2 * n + upperTailLength c n)) ∨
        roughCanonicalExceptionalUpperPhysicalRoughInterval
            n (upperTailLength c n) deltaStar b = ∅) ∧
      (RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b
          (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n))
          (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)) ∨
        roughCanonicalExceptionalHighPhysicalRoughInterval
            n (upperTailLength c n) (K0 + 1) deltaStar b = ∅) ∧
      (RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n)
          (roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n)) ∨
        roughCanonicalExceptionalBroadPhysicalRoughInterval
            n (upperTailLength c n) (K0 + 1) deltaStar b = ∅)) :
    RoughCanonicalSignedExceptionalCutoffIntervalEstimate
      K0 n b c deltaStar
      (roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c)
      (roughCanonicalFourFiveCutoffHighEstimateConstant
        K0 P Ckernel c)
      (roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel) := by
  have hbData := Finset.mem_Ioc.mp
    (by simpa only [roughCanonicalExceptionalCutoffCoreSet] using hb)
  have hbPos : 0 < b := by omega
  have hLPos : 0 < L n := zero_lt_one.trans_le hLone
  have hscaleNonneg :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    exact Nat.cast_nonneg _
  have hPupper :=
    roughCanonicalExceptional_paperRate_le_cutoffSqRate
      (n := n) (b := b) hP hLone
  have hPbroad :=
    roughCanonicalExceptional_paperRate_le_cutoffBroadRate
      (n := n) (b := b) hP hLone
  refine
    { upper := ?_
      high := ?_
      broad := ?_ }
  · rcases hintervals.1 with hgeometry | hempty
    · let A :=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n)
      let B :=
        roughCanonicalExceptionalPhysicalUpperEndpoint
          b (2 * n + upperTailLength c n)
      have hcard :=
        fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
          hy hgeometry (harithmetic A B hgeometry)
          hCkernel hbound
      have hlength : 2 * n + upperTailLength c n - 2 * n =
          upperTailLength c n := by omega
      have hspan :
          (((B - A : Nat) : Real)) <=
            (upperTailLength c n : Real) / (b : Real) + 1 := by
        simpa only [A, B, hlength] using
          (roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
            (n := n) (b := b) (lo := 2 * n)
            (hi := 2 * n + upperTailLength c n)
            (deltaStar := deltaStar) hbPos (by omega))
      have hspanRate :=
        roughCanonicalExceptional_shortClippedSpan_div_log_le
          (n := n) (b := b)
          (H := (upperTailLength c n : Real))
          (span := ((B - A : Nat) : Real)) (a := c)
          hbPos hc (Nat.cast_nonneg _)
          hLone hlogLower (Nat.cast_nonneg _) htail hspan
      have hfinal :
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
            roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 +
                1) := by
        calc
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 3) +
                (8 / 5 : Real) * Ckernel *
                  (((B - A : Nat) : Real) /
                    Real.log (yNat n : Real)) := hcard
          _ <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) +
                (8 / 5 : Real) * Ckernel *
                  ((10 * c + 5) *
                    (roughCanonicalExceptionalPhysicalRateScale n b /
                      L n ^ 2 + 1)) :=
            add_le_add hPupper
              (mul_le_mul_of_nonneg_left hspanRate
                (mul_nonneg (by norm_num) hCkernel))
          _ =
              roughCanonicalFourFiveCutoffUpperEstimateConstant
                  P Ckernel c *
                (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) := by
            unfold roughCanonicalFourFiveCutoffUpperEstimateConstant
            ring
      simpa only [A, B,
        roughCanonicalExceptionalUpperPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (roughCanonicalFourFiveCutoffUpperEstimateConstant_nonneg
          hP hCkernel hc)
        (add_nonneg (div_nonneg hscaleNonneg (sq_nonneg (L n)))
          (by norm_num : (0 : Real) <= 1))
  · rcases hintervals.2.1 with hgeometry | hempty
    · let A :=
        roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n)
      let B :=
        roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)
      have hcard :=
        fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
          hy hgeometry (harithmetic A B hgeometry)
          hCkernel hbound
      have hlength :
          2 * n -
              (2 * n - (K0 + 1) * upperTailLength c n) <=
            (K0 + 1) * upperTailLength c n := by
        omega
      have hspan0 :=
        roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
          (n := n) (b := b)
          (lo := 2 * n - (K0 + 1) * upperTailLength c n)
          (hi := 2 * n) (deltaStar := deltaStar)
          hbPos (Nat.sub_le _ _)
      have hspan :
          (((B - A : Nat) : Real)) <=
            (((K0 + 1) * upperTailLength c n : Nat) : Real) /
              (b : Real) + 1 := by
        calc
          (((B - A : Nat) : Real)) <=
              ((2 * n -
                (2 * n - (K0 + 1) * upperTailLength c n) : Nat) : Real) /
                  (b : Real) + 1 := by
            simpa only [A, B] using hspan0
          _ <=
              (((K0 + 1) * upperTailLength c n : Nat) : Real) /
                  (b : Real) + 1 :=
            add_le_add
              (div_le_div_of_nonneg_right
                (by exact_mod_cast hlength) (by positivity))
              le_rfl
      have htailDepth :
          (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
            2 * (((K0 + 1 : Nat) : Real) * c) *
              (n : Real) / L n := by
        norm_num only [Nat.cast_mul]
        calc
          ((K0 + 1 : Nat) : Real) *
              (upperTailLength c n : Real) <=
            ((K0 + 1 : Nat) : Real) *
              (2 * c * (n : Real) / L n) :=
            mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
          _ = 2 * (((K0 + 1 : Nat) : Real) * c) *
              (n : Real) / L n := by ring
      have hspanRate :=
        roughCanonicalExceptional_shortClippedSpan_div_log_le
          (n := n) (b := b)
          (H :=
            (((K0 + 1) * upperTailLength c n : Nat) : Real))
          (span := ((B - A : Nat) : Real))
          (a := ((K0 + 1 : Nat) : Real) * c)
          hbPos (mul_nonneg (Nat.cast_nonneg _) hc)
          (Nat.cast_nonneg _) hLone hlogLower (Nat.cast_nonneg _)
          htailDepth hspan
      have hfinal :
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
            roughCanonicalFourFiveCutoffHighEstimateConstant
                K0 P Ckernel c *
              (roughCanonicalExceptionalPhysicalRateScale n b /
                L n ^ 2 + 1) := by
        calc
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 3) +
                (8 / 5 : Real) * Ckernel *
                  (((B - A : Nat) : Real) /
                    Real.log (yNat n : Real)) := hcard
          _ <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) +
                (8 / 5 : Real) * Ckernel *
                  ((10 * (((K0 + 1 : Nat) : Real) * c) + 5) *
                    (roughCanonicalExceptionalPhysicalRateScale n b /
                      L n ^ 2 + 1)) :=
            add_le_add hPupper
              (mul_le_mul_of_nonneg_left hspanRate
                (mul_nonneg (by norm_num) hCkernel))
          _ =
              roughCanonicalFourFiveCutoffHighEstimateConstant
                  K0 P Ckernel c *
                (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 2 + 1) := by
            unfold roughCanonicalFourFiveCutoffHighEstimateConstant
            ring
      simpa only [A, B,
        roughCanonicalExceptionalHighPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (roughCanonicalFourFiveCutoffHighEstimateConstant_nonneg
          K0 hP hCkernel hc)
        (add_nonneg (div_nonneg hscaleNonneg (sq_nonneg (L n)))
          (by norm_num : (0 : Real) <= 1))
  · rcases hintervals.2.2 with hgeometry | hempty
    · let A :=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n
      let B :=
        roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n)
      have hcard :=
        fourFiveRoughInterval_card_le_arithmetic_add_fixedEndpointFreezing
          hy hgeometry (harithmetic A B hgeometry)
          hCkernel hbound
      have hupperNat :
          B <= roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) := by
        dsimp only [B, roughCanonicalExceptionalPhysicalUpperEndpoint]
        exact Nat.div_le_div_right (Nat.sub_le _ _)
      have hspanNat :
          B - A <=
            roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
              roughCanonicalExceptionalPhysicalLowerEndpoint
                n deltaStar b n := by
        omega
      have hspan0 :=
        roughCanonicalExceptional_clippedPhysicalEndpoint_span_le
          (n := n) (b := b) (lo := n) (hi := 2 * n)
          (deltaStar := deltaStar) hbPos (by omega)
      have htwoSub : 2 * n - n = n := by
        omega
      have hspan :
          (((B - A : Nat) : Real)) <=
            (n : Real) / (b : Real) + 1 := by
        calc
          (((B - A : Nat) : Real)) <=
              ((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
                roughCanonicalExceptionalPhysicalLowerEndpoint
                  n deltaStar b n : Nat) : Real) := by
            exact_mod_cast hspanNat
          _ <= ((2 * n - n : Nat) : Real) / (b : Real) + 1 :=
            hspan0
          _ = (n : Real) / (b : Real) + 1 := by
            simp only [htwoSub]
      have hspanRate :=
        roughCanonicalExceptional_broadClippedSpan_div_log_le
          (n := n) (b := b)
          (span := ((B - A : Nat) : Real))
          hbPos (Nat.cast_nonneg _) hLone hlogLower hspan
      have hfinal :
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
            roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
        calc
          ((fourFiveRoughInterval (yNat n) A B).card : Real) <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n ^ 3) +
                (8 / 5 : Real) * Ckernel *
                  (((B - A : Nat) : Real) /
                    Real.log (yNat n : Real)) := hcard
          _ <=
              P * (roughCanonicalExceptionalPhysicalRateScale n b /
                  L n + 1) +
                (8 / 5 : Real) * Ckernel *
                  (5 *
                    (roughCanonicalExceptionalPhysicalRateScale n b /
                      L n + 1)) :=
            add_le_add hPbroad
              (mul_le_mul_of_nonneg_left hspanRate
                (mul_nonneg (by norm_num) hCkernel))
          _ =
              roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel *
                (roughCanonicalExceptionalPhysicalRateScale n b / L n +
                  1) := by
            unfold roughCanonicalFourFiveCutoffBroadEstimateConstant
            ring
      simpa only [A, B,
        roughCanonicalExceptionalBroadPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · simp only [hempty, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg
        (roughCanonicalFourFiveCutoffBroadEstimateConstant_nonneg
          hP hCkernel)
        (add_nonneg (div_nonneg hscaleNonneg hLPos.le)
          (by norm_num : (0 : Real) <= 1))

/-! ## Eventual cutoff estimates -/

theorem
    exists_eventually_roughCanonicalSignedExceptionalCutoffIntervalEstimates
    (K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∃ Cplus Chigh Cbroad : Real,
      0 <= Cplus ∧ 0 <= Chigh ∧ 0 <= Cbroad ∧
      ∀ᶠ n : Nat in atTop, ∀ b : Nat,
        b ∈ roughCanonicalExceptionalCutoffCoreSet deltaStar n ->
          RoughCanonicalSignedExceptionalCutoffIntervalEstimate
            K0 n b c deltaStar Cplus Chigh Cbroad := by
  obtain ⟨Carithmetic, hCarithmetic, harithmeticEventually⟩ :=
    exists_eventually_roughCanonicalExceptionalPhysicalInterval_paperRate
      (deltaStar := deltaStar)
  obtain ⟨Ckernel, hCkernel, hbound⟩ :=
    exists_fourFiveContinuumMixtureKernel_uniform_C1_bound
  let P :=
    roughCanonicalFourFiveIntervalPaperRateConstant Carithmetic
  have hP : 0 <= P := by
    dsimp only [P]
    exact
      roughCanonicalFourFiveIntervalPaperRateConstant_nonneg
        hCarithmetic.le
  let Cplus :=
    roughCanonicalFourFiveCutoffUpperEstimateConstant P Ckernel c
  let Chigh :=
    roughCanonicalFourFiveCutoffHighEstimateConstant K0 P Ckernel c
  let Cbroad :=
    roughCanonicalFourFiveCutoffBroadEstimateConstant P Ckernel
  refine ⟨Cplus, Chigh, Cbroad, ?_, ?_, ?_, ?_⟩
  · dsimp only [Cplus]
    exact
      roughCanonicalFourFiveCutoffUpperEstimateConstant_nonneg
        hP hCkernel.le hc.le
  · dsimp only [Chigh]
    exact
      roughCanonicalFourFiveCutoffHighEstimateConstant_nonneg
        K0 hP hCkernel.le hc.le
  · dsimp only [Cbroad]
    exact
      roughCanonicalFourFiveCutoffBroadEstimateConstant_nonneg
        hP hCkernel.le
  · have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [
        harithmeticEventually,
        eventually_roughCanonicalExceptional_threePhysicalIntervals_geometry_or_empty
          (K0 := K0) hc hdelta hdeltaUpper,
        roughCanonicalExceptional_yNat_tendsto_atTop.eventually
          (eventually_ge_atTop (2 : Nat)),
        hLTop.eventually (eventually_ge_atTop (1 : Real)),
        Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
        eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc]
        with n harithmeticN hgeometryN hy hLone hlogLower htailScale
    intro b hb
    have hbData := Finset.mem_Ioc.mp
      (by simpa only [roughCanonicalExceptionalCutoffCoreSet] using hb)
    have hbPrefix :
        b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n) := by
      exact Finset.mem_Icc.mpr ⟨by omega, hbData.2⟩
    have htail :
        (upperTailLength c n : Real) <=
          2 * c * (n : Real) / L n := by
      calc
        (upperTailLength c n : Real) <=
            2 * c * secondOrderScale n := htailScale
        _ = 2 * c * (n : Real) / L n := by
          unfold secondOrderScale L
          ring
    have hestimate :=
      roughCanonicalSignedExceptionalCutoffIntervalEstimate_of_geometry_or_empty
        (K0 := K0) (n := n) (b := b)
        (c := c) (deltaStar := deltaStar)
        (P := P) (Ckernel := Ckernel)
        hy hc.le hP hCkernel.le hLone hlogLower htail hb
        hbound
        (fun A B hgeometry => by
          dsimp only [P]
          exact harithmeticN b A B hgeometry)
        (hgeometryN b hbPrefix)
    simpa only [Cplus, Chigh, Cbroad] using hestimate

end BankPaperRealization

end

end Erdos390.WholePaper
