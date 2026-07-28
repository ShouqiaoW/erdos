import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector
import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepEndpointErrorConnector
import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveGeometryPrecursorConnector

/-!
# Deep exceptional four/five interval estimates

This connector assembles the three inputs already isolated for a deep
smooth core:

* the uniform arithmetic `Z / L^3` estimate;
* freezing at the literal coordinate, using the uniform compact `C¹`
  kernel bound and the deep displacement package;
* the literal endpoint-length errors.

The upper and high intervals use their eventual no-clipping conclusions.
The broad interval continues to use its clipped lower endpoint.  If that
clipping passes the broad upper endpoint, the literal interval is empty and
the same endpoint budget controls the removed frozen main term.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Algebraic rate absorption -/

/-- The two non-arithmetic terms produced by the freezing adapter for a
short deep interval are absorbed at the `Z/L^3+1` rate. -/
theorem roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
    {Z ell logY literal C D a : Real}
    (hZ : 0 <= Z) (hLone : 1 <= ell)
    (hlogLower : (1 / 5 : Real) * ell <= logY)
    (hC : 0 <= C) (hD : 0 <= D) (ha : 0 <= a)
    (hliteral : literal <= 2 * a * Z / ell + 1)
    (hliteralNonneg : 0 <= literal) :
    (((literal / logY) * C) * (D / ell ^ 2) +
        (C / logY) * 1) <=
      (5 * C * D * (2 * a + 1) + 5 * C) *
        (Z / ell ^ 3 + 1) := by
  have hL : 0 < ell := zero_lt_one.trans_le hLone
  have hlog : 0 < logY :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hinvLog : 1 / logY <= 5 / ell := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hfiveL : 0 <= 5 / ell := div_nonneg (by norm_num) hL.le
  have hscaledCD :
      0 <= C * (D / ell ^ 2) :=
    mul_nonneg hC (div_nonneg hD (sq_nonneg ell))
  have hLcubeLeFour : ell ^ 3 <= ell ^ 4 := by
    calc
      ell ^ 3 = ell ^ 3 * 1 := by ring
      _ <= ell ^ 3 * ell :=
        mul_le_mul_of_nonneg_left hLone (pow_nonneg hL.le 3)
      _ = ell ^ 4 := by ring
  have hZfour : Z / ell ^ 4 <= Z / ell ^ 3 :=
    div_le_div_of_nonneg_left hZ (pow_pos hL 3) hLcubeLeFour
  have hInvCube : 1 / ell ^ 3 <= 1 :=
    (div_le_one (pow_pos hL 3)).2
      (one_le_pow₀ (n := 3) hLone)
  have hq : 0 <= Z / ell ^ 3 :=
    div_nonneg hZ (pow_nonneg hL.le 3)
  have hqOne : 1 <= Z / ell ^ 3 + 1 := by linarith
  have hcoeffMain : 0 <= 10 * a * C * D := by positivity
  have hcoeffUnit : 0 <= 5 * C * D := by positivity
  have hfreeze :
      ((literal / logY) * C) * (D / ell ^ 2) <=
        (5 * C * D * (2 * a + 1)) *
          (Z / ell ^ 3 + 1) := by
    calc
      ((literal / logY) * C) * (D / ell ^ 2) =
          (literal * (C * (D / ell ^ 2))) * (1 / logY) := by ring
      _ <=
          (literal * (C * (D / ell ^ 2))) * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog
          (mul_nonneg hliteralNonneg hscaledCD)
      _ <=
          ((2 * a * Z / ell + 1) * (C * (D / ell ^ 2))) *
            (5 / ell) := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hliteral hscaledCD)
            hfiveL
      _ =
          (10 * a * C * D) * (Z / ell ^ 4) +
            (5 * C * D) * (1 / ell ^ 3) := by ring
      _ <=
          (10 * a * C * D) * (Z / ell ^ 3) +
            (5 * C * D) * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hZfour hcoeffMain)
          (mul_le_mul_of_nonneg_left hInvCube hcoeffUnit)
      _ <=
          ((10 * a * C * D) + (5 * C * D)) *
            (Z / ell ^ 3 + 1) := by
        calc
          (10 * a * C * D) * (Z / ell ^ 3) +
              (5 * C * D) * 1 <=
              ((10 * a * C * D) * (Z / ell ^ 3) +
                (5 * C * D) * 1) +
                ((10 * a * C * D) +
                  (5 * C * D) * (Z / ell ^ 3)) :=
            le_add_of_nonneg_right
              (add_nonneg hcoeffMain (mul_nonneg hcoeffUnit hq))
          _ =
              ((10 * a * C * D) + (5 * C * D)) *
                (Z / ell ^ 3 + 1) := by ring
      _ =
          (5 * C * D * (2 * a + 1)) *
            (Z / ell ^ 3 + 1) := by ring
  have hInvL : 5 / ell <= 5 :=
    (div_le_iff₀ hL).2 (by nlinarith [hLone])
  have hendpoint :
      (C / logY) * 1 <=
        (5 * C) * (Z / ell ^ 3 + 1) := by
    calc
      (C / logY) * 1 = C * (1 / logY) := by ring
      _ <= C * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog hC
      _ <= C * 5 :=
        mul_le_mul_of_nonneg_left hInvL hC
      _ = (5 * C) * 1 := by ring
      _ <= (5 * C) * (Z / ell ^ 3 + 1) :=
        mul_le_mul_of_nonneg_left hqOne (by positivity)
  exact
    (add_le_add hfreeze hendpoint).trans_eq (by ring)

/-- The broad freezing and clipped-endpoint terms are absorbed at the
`Z/L^2+1` rate. -/
theorem roughCanonicalFourFiveDeep_broadFreezingEndpointRate_le
    {Z ell logY literal C D : Real}
    (hZ : 0 <= Z) (hLone : 1 <= ell)
    (hlogLower : (1 / 5 : Real) * ell <= logY)
    (hC : 0 <= C) (hD : 0 <= D)
    (hliteral : literal <= 3 * Z + 2)
    (hliteralNonneg : 0 <= literal) :
    (((literal / logY) * C) * (D / ell) +
        (C / logY) * (2 * (Z / ell + 1))) <=
      (25 * C * D + 10 * C) *
        (Z / ell ^ 2 + 1) := by
  have hL : 0 < ell := zero_lt_one.trans_le hLone
  have hlog : 0 < logY :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hinvLog : 1 / logY <= 5 / ell := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hfiveL : 0 <= 5 / ell := div_nonneg (by norm_num) hL.le
  have hscaledCD :
      0 <= C * (D / ell) :=
    mul_nonneg hC (div_nonneg hD hL.le)
  have hInvSq : 1 / ell ^ 2 <= 1 :=
    (div_le_one (sq_pos_of_pos hL)).2
      (one_le_pow₀ (n := 2) hLone)
  have hInvL : 1 / ell <= 1 :=
    (div_le_one hL).2 hLone
  have hq : 0 <= Z / ell ^ 2 :=
    div_nonneg hZ (sq_nonneg ell)
  have hqOne : 1 <= Z / ell ^ 2 + 1 := by linarith
  have hcoeffMain : 0 <= 15 * C * D := by positivity
  have hcoeffUnit : 0 <= 10 * C * D := by positivity
  have hfreeze :
      ((literal / logY) * C) * (D / ell) <=
        (25 * C * D) * (Z / ell ^ 2 + 1) := by
    calc
      ((literal / logY) * C) * (D / ell) =
          (literal * (C * (D / ell))) * (1 / logY) := by ring
      _ <=
          (literal * (C * (D / ell))) * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog
          (mul_nonneg hliteralNonneg hscaledCD)
      _ <=
          ((3 * Z + 2) * (C * (D / ell))) * (5 / ell) := by
        exact
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hliteral hscaledCD)
            hfiveL
      _ =
          (15 * C * D) * (Z / ell ^ 2) +
            (10 * C * D) * (1 / ell ^ 2) := by ring
      _ <=
          (15 * C * D) * (Z / ell ^ 2) +
            (10 * C * D) * 1 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hInvSq hcoeffUnit)
      _ <=
          ((15 * C * D) + (10 * C * D)) *
            (Z / ell ^ 2 + 1) := by
        calc
          (15 * C * D) * (Z / ell ^ 2) +
              (10 * C * D) * 1 <=
              ((15 * C * D) * (Z / ell ^ 2) +
                (10 * C * D) * 1) +
                ((15 * C * D) +
                  (10 * C * D) * (Z / ell ^ 2)) :=
            le_add_of_nonneg_right
              (add_nonneg hcoeffMain (mul_nonneg hcoeffUnit hq))
          _ =
              ((15 * C * D) + (10 * C * D)) *
                (Z / ell ^ 2 + 1) := by ring
      _ = (25 * C * D) * (Z / ell ^ 2 + 1) := by ring
  have hendpoint :
      (C / logY) * (2 * (Z / ell + 1)) <=
        (10 * C) * (Z / ell ^ 2 + 1) := by
    have hmult :
        0 <= C * (2 * (Z / ell + 1)) := by positivity
    calc
      (C / logY) * (2 * (Z / ell + 1)) =
          (C * (2 * (Z / ell + 1))) * (1 / logY) := by ring
      _ <=
          (C * (2 * (Z / ell + 1))) * (5 / ell) :=
        mul_le_mul_of_nonneg_left hinvLog hmult
      _ =
          (10 * C) * (Z / ell ^ 2 + 1 / ell) := by ring
      _ <=
          (10 * C) * (Z / ell ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left
          (by linarith [hInvL]) (mul_nonneg (by norm_num) hC)
  exact
    (add_le_add hfreeze hendpoint).trans_eq (by ring)

/-! ## Generic one-interval assemblers -/

def roughCanonicalFourFiveDeepShortEstimateConstant
    (P C D a : Real) : Real :=
  P + 5 * C * D * (2 * a + 1) + 5 * C

def roughCanonicalFourFiveDeepBroadEstimateConstant
    (P C D : Real) : Real :=
  P + 25 * C * D + 10 * C

theorem roughCanonicalFourFiveDeepShortEstimateConstant_nonneg
    {P C D a : Real}
    (hP : 0 <= P) (hC : 0 <= C) (hD : 0 <= D) (ha : 0 <= a) :
    0 <= roughCanonicalFourFiveDeepShortEstimateConstant P C D a := by
  unfold roughCanonicalFourFiveDeepShortEstimateConstant
  positivity

theorem roughCanonicalFourFiveDeepBroadEstimateConstant_nonneg
    {P C D : Real}
    (hP : 0 <= P) (hC : 0 <= C) (hD : 0 <= D) :
    0 <= roughCanonicalFourFiveDeepBroadEstimateConstant P C D := by
  unfold roughCanonicalFourFiveDeepBroadEstimateConstant
  positivity

/-- Generic upper/high assembler.  It is deliberately phrased for one
geometry-certified interval; the only interval-specific inputs are the
displacement numerator, the ideal-length scale, and the endpoint theorem. -/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
    {n b A B : Nat} {deltaStar : Real}
    {P C D a u0 idealLength : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (hP : 0 <= P) (hC : 0 <= C) (hD : 0 <= D) (ha : 0 <= a)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) - u0) <=
          D / L n ^ 2)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <= 1)
    (hidealRate :
      idealLength <=
        2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      roughCanonicalFourFiveDeepShortEstimateConstant P C D a *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hliteral :
      (((B - A : Nat) : Real)) <=
        2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n + 1 := by
    have hdiff :
        (((B - A : Nat) : Real)) - idealLength <= 1 :=
      (le_abs_self _).trans hlength
    linarith
  have hraw :=
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
      (arithmeticError :=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
      (Ckernel := C) (D := D / L n ^ 2)
      (u0 := u0) (idealLength := idealLength) (endpointError := 1)
      hy hgeometry harithmetic hC
      (div_nonneg hD (sq_nonneg (L n))) (by norm_num)
      hu0 hbound hdisplacement hlength
  have hfreezeEndpoint :=
    roughCanonicalFourFiveDeep_shortFreezingEndpointRate_le
      hZ hLone hlogLower hC hD ha hliteral (Nat.cast_nonneg _)
  have hq :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 :=
    div_nonneg hZ (pow_nonneg hL.le 3)
  calc
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) +
        (((((B - A : Nat) : Real)) /
            Real.log (yNat n : Real)) * C) * (D / L n ^ 2) +
          (C / Real.log (yNat n : Real)) * 1 := hraw
    _ <=
        P *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) +
          (5 * C * D * (2 * a + 1) + 5 * C) *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) :=
      by
        simpa only [add_assoc] using
          (add_le_add
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (by norm_num)) hP)
            hfreezeEndpoint)
    _ =
        roughCanonicalFourFiveDeepShortEstimateConstant P C D a *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 + 1) := by
      unfold roughCanonicalFourFiveDeepShortEstimateConstant
      ring

/-- Generic broad assembler.  The lower endpoint remains clipped, and its
complete endpoint budget is used both to bound the literal span and in the
freezing adapter. -/
theorem
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepBroadRate
    {n b A B : Nat} {deltaStar : Real}
    {P C D u0 idealLength : Real}
    (hy : 2 <= yNat n)
    (hgeometry :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B)
    (hP : 0 <= P) (hC : 0 <= C) (hD : 0 <= D)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (harithmetic :
      abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
          fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hdisplacement :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        abs (Real.log t / Real.log (yNat n : Real) - u0) <=
          D / L n)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1))
    (hidealRate :
      idealLength <= roughCanonicalExceptionalPhysicalRateScale n b) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      roughCanonicalFourFiveDeepBroadEstimateConstant P C D *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hZdiv :
      roughCanonicalExceptionalPhysicalRateScale n b / L n <=
        roughCanonicalExceptionalPhysicalRateScale n b := by
    exact div_le_self hZ hLone
  have hliteral :
      (((B - A : Nat) : Real)) <=
        3 * roughCanonicalExceptionalPhysicalRateScale n b + 2 := by
    have hdiff :
        (((B - A : Nat) : Real)) - idealLength <=
          2 *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) :=
      (le_abs_self _).trans hlength
    nlinarith
  have hraw :=
    abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le
      (arithmeticError :=
        P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
      (Ckernel := C) (D := D / L n)
      (u0 := u0) (idealLength := idealLength)
      (endpointError :=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1))
      hy hgeometry harithmetic hC (div_nonneg hD hL.le)
      (by positivity) hu0 hbound hdisplacement hlength
  have hfreezeEndpoint :=
    roughCanonicalFourFiveDeep_broadFreezingEndpointRate_le
      hZ hLone hlogLower hC hD hliteral (Nat.cast_nonneg _)
  have hLsqLeCube : L n ^ 2 <= L n ^ 3 := by
    calc
      L n ^ 2 = L n ^ 2 * 1 := by ring
      _ <= L n ^ 2 * L n :=
        mul_le_mul_of_nonneg_left hLone (sq_nonneg (L n))
      _ = L n ^ 3 := by ring
  have hq :
      roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3 <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 :=
    div_le_div_of_nonneg_left hZ (sq_pos_of_pos hL) hLsqLeCube
  calc
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      P * (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3) +
        (((((B - A : Nat) : Real)) /
            Real.log (yNat n : Real)) * C) * (D / L n) +
          (C / Real.log (yNat n : Real)) *
            (2 *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)) :=
      hraw
    _ <=
        P *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) +
          (25 * C * D + 10 * C) *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) :=
      by
        simpa only [add_assoc] using
          (add_le_add
            (mul_le_mul_of_nonneg_left
              (hq.trans (le_add_of_nonneg_right (by norm_num))) hP)
            hfreezeEndpoint)
    _ =
        roughCanonicalFourFiveDeepBroadEstimateConstant P C D *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
      unfold roughCanonicalFourFiveDeepBroadEstimateConstant
      ring

/-- The real core quotient is bounded by the physical paper-rate scale. -/
theorem roughCanonicalFourFiveDeep_self_div_core_le_rateScale
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

/-- A short ideal length inherits the deep `Z/L` scale from its undivided
physical length. -/
theorem roughCanonicalFourFiveDeep_shortIdealLength_le
    {n b : Nat} {H a : Real}
    (hb : 0 < b) (ha : 0 <= a) (hLone : 1 <= L n)
    (hH : H <= 2 * a * (n : Real) / L n) :
    H / (b : Real) <=
      2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n := by
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hb
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hcore :=
    roughCanonicalFourFiveDeep_self_div_core_le_rateScale
      (n := n) hb
  calc
    H / (b : Real) <=
        (2 * a * (n : Real) / L n) / (b : Real) :=
      div_le_div_of_nonneg_right hH hbReal.le
    _ = (2 * a / L n) * ((n : Real) / (b : Real)) := by
      field_simp [hL.ne', hbReal.ne']
    _ <=
        (2 * a / L n) *
          roughCanonicalExceptionalPhysicalRateScale n b :=
      mul_le_mul_of_nonneg_left hcore
        (div_nonneg (mul_nonneg (by norm_num) ha) hL.le)
    _ =
        2 * a * roughCanonicalExceptionalPhysicalRateScale n b / L n := by
      ring

/-- The broad endpoint term alone is absorbed by `10*C*(Z/L^2+1)`.
This is the estimate used when clipping makes the literal broad interval
empty. -/
theorem roughCanonicalFourFiveDeep_broadEndpointRate_le
    {Z ell logY C : Real}
    (hZ : 0 <= Z) (hLone : 1 <= ell)
    (hlogLower : (1 / 5 : Real) * ell <= logY)
    (hC : 0 <= C) :
    (C / logY) * (2 * (Z / ell + 1)) <=
      (10 * C) * (Z / ell ^ 2 + 1) := by
  have hL : 0 < ell := zero_lt_one.trans_le hLone
  have hlog : 0 < logY :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hinvLog : 1 / logY <= 5 / ell := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hInvL : 1 / ell <= 1 :=
    (div_le_one hL).2 hLone
  have hmult :
      0 <= C * (2 * (Z / ell + 1)) := by positivity
  calc
    (C / logY) * (2 * (Z / ell + 1)) =
        (C * (2 * (Z / ell + 1))) * (1 / logY) := by ring
    _ <= (C * (2 * (Z / ell + 1))) * (5 / ell) :=
      mul_le_mul_of_nonneg_left hinvLog hmult
    _ = (10 * C) * (Z / ell ^ 2 + 1 / ell) := by ring
    _ <= (10 * C) * (Z / ell ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left
        (by linarith [hInvL]) (mul_nonneg (by norm_num) hC)

/-- Empty-interval companion to the generic broad assembler.  The endpoint
error controls the entire ideal frozen main term. -/
theorem
    abs_fourFiveRoughInterval_card_sub_idealFrozen_le_deepBroadRate_of_empty
    {n b A B : Nat} {C u0 idealLength : Real}
    (hBA : B <= A)
    (hC : 0 <= C) (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hu0 :
      u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (hlength :
      abs ((((B - A : Nat) : Real)) - idealLength) <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)) :
    abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
        (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
      (10 * C) *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1) := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hidealAbs :
      abs idealLength <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
    simpa only [Nat.sub_eq_zero_of_le hBA, Nat.cast_zero, zero_sub,
      abs_neg] using hlength
  have hkernel :
      abs (fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) <=
        C / Real.log (yNat n : Real) := by
    rw [abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (hbound u0 hu0).1 hlog.le
  have hmain :
      abs ((fourFiveContinuumMixtureKernel u0 /
          Real.log (yNat n : Real)) * idealLength) <=
        (C / Real.log (yNat n : Real)) *
          (2 *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)) := by
    rw [abs_mul]
    exact mul_le_mul hkernel hidealAbs (abs_nonneg _)
      (div_nonneg hC hlog.le)
  rw [fourFiveRoughInterval_eq_empty_of_upper_le_lower hBA]
  simp only [Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
  exact hmain.trans
    (roughCanonicalFourFiveDeep_broadEndpointRate_le
      hZ hLone hlogLower hC)

/-! ## The three fixed deep constants -/

def roughCanonicalFourFiveDeepUpperEstimateConstant
    (P C c : Real) : Real :=
  roughCanonicalFourFiveDeepShortEstimateConstant P C
    (roughCanonicalFourFiveDeepUpperDisplacementConstant c) c

def roughCanonicalFourFiveDeepHighEstimateConstant
    (K0 : Nat) (P C c : Real) : Real :=
  roughCanonicalFourFiveDeepShortEstimateConstant P C
    (roughCanonicalFourFiveDeepHighDisplacementConstant K0 c)
    (((K0 + 1 : Nat) : Real) * c)

def roughCanonicalFourFiveDeepBroadFinalEstimateConstant
    (P C : Real) : Real :=
  roughCanonicalFourFiveDeepBroadEstimateConstant P C
    roughCanonicalFourFiveDeepBroadDisplacementConstant

theorem roughCanonicalFourFiveDeepUpperEstimateConstant_nonneg
    {P C c : Real}
    (hP : 0 <= P) (hC : 0 <= C) (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveDeepUpperEstimateConstant P C c := by
  unfold roughCanonicalFourFiveDeepUpperEstimateConstant
  exact
    roughCanonicalFourFiveDeepShortEstimateConstant_nonneg
      hP hC
      (roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg hc) hc

theorem roughCanonicalFourFiveDeepHighEstimateConstant_nonneg
    (K0 : Nat) {P C c : Real}
    (hP : 0 <= P) (hC : 0 <= C) (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveDeepHighEstimateConstant K0 P C c := by
  unfold roughCanonicalFourFiveDeepHighEstimateConstant
  exact
    roughCanonicalFourFiveDeepShortEstimateConstant_nonneg
      hP hC
      (roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg K0 hc)
      (mul_nonneg (Nat.cast_nonneg _) hc)

theorem roughCanonicalFourFiveDeepBroadFinalEstimateConstant_nonneg
    {P C : Real} (hP : 0 <= P) (hC : 0 <= C) :
    0 <= roughCanonicalFourFiveDeepBroadFinalEstimateConstant P C := by
  unfold roughCanonicalFourFiveDeepBroadFinalEstimateConstant
  exact
    roughCanonicalFourFiveDeepBroadEstimateConstant_nonneg
      hP hC roughCanonicalFourFiveDeepBroadDisplacementConstant_pos.le

/-! ## Finite three-interval assembly -/

/-- Assemble all three frozen deep estimates from the uniform arithmetic
bound, common geometry, displacement package, and endpoint package.  The
broad proof splits on the literal clipped endpoint order; no broad
no-clipping premise occurs. -/
theorem roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
    {K0 n b : Nat} {c deltaStar P C : Real}
    (hy : 2 <= yNat n)
    (hc : 0 <= c) (hP : 0 <= P) (hC : 0 <= C)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (htailNat : upperTailLength c n <= n)
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hu0 :
      roughCanonicalFourFiveFrozenCoordinate n b ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hb : b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n)
    (hbound :
      ∀ z ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        abs (fourFiveContinuumMixtureKernel z) <= C ∧
        abs (fourFiveContinuumMixtureKernelDerivative z) <= C)
    (harithmetic :
      ∀ A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          abs (((fourFiveRoughInterval (yNat n) A B).card : Real) -
              fourFiveContinuumMixtureIntegralMain (yNat n) A B) <=
            P *
              (roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 3))
    (hdisplacement :
      RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
        K0 n b c deltaStar)
    (hendpoint :
      RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
        K0 n b c deltaStar) :
    RoughCanonicalSignedExceptionalDeepIntervalEstimate
      K0 n b c deltaStar
      (roughCanonicalFourFiveDeepUpperEstimateConstant P C c)
      (roughCanonicalFourFiveDeepHighEstimateConstant K0 P C c)
      (roughCanonicalFourFiveDeepBroadFinalEstimateConstant P C) := by
  have hbDeep :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2) := by
    simpa only [roughCanonicalExceptionalDeepCoreSet] using hb
  have hbData := Finset.mem_Icc.mp hbDeep
  have hbPos : 0 < b := by omega
  have hbReal : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPos
  have hbPrefix :
      b ∈ Finset.Icc 1
        (2 * tangentPaperExceptionalCutoff deltaStar n) := by
    exact Finset.mem_Icc.mpr ⟨hbData.1, by omega⟩
  have hZ :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
    unfold roughCanonicalExceptionalPhysicalRateScale
    positivity
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hcore :=
    roughCanonicalFourFiveDeep_self_div_core_le_rateScale
      (n := n) hbPos
  refine ⟨?_, ?_, ?_⟩
  · let A :=
      roughCanonicalExceptionalPhysicalLowerEndpoint
        n deltaStar b (2 * n)
    let B :=
      roughCanonicalExceptionalPhysicalUpperEndpoint
        b (2 * n + upperTailLength c n)
    have hAB : A <= B := by
      dsimp only [A, B, roughCanonicalExceptionalPhysicalLowerEndpoint,
        roughCanonicalExceptionalPhysicalUpperEndpoint]
      rw [max_eq_left hendpoint.upper_noClipping]
      exact Nat.div_le_div_right (by omega)
    have hgeometry :
        RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b A B := by
      simpa only [A, B] using
        (roughCanonicalExceptionalClippedInterval_geometry
          (lo := 2 * n)
          (hi := 2 * n + upperTailLength c n)
          hcommon hbPrefix hAB (by omega))
    have hidealRate :
        (upperTailLength c n : Real) / (b : Real) <=
          2 * c * roughCanonicalExceptionalPhysicalRateScale n b / L n :=
      roughCanonicalFourFiveDeep_shortIdealLength_le
        hbPos hc hLone htail
    have hfinal :=
      abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
        (P := P) (C := C)
        (D := roughCanonicalFourFiveDeepUpperDisplacementConstant c)
        (a := c)
        (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
        (idealLength :=
          (upperTailLength c n : Real) / (b : Real))
        hy hgeometry hP hC
        (roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg hc)
        hc hLone hlogLower hu0 hbound
        (harithmetic A B hgeometry)
        (by
          simpa only [A, B] using hdisplacement.upper_displacement)
        (by
          simpa only [A, B] using hendpoint.upper_length_error)
        hidealRate
    simpa only [A, B,
      roughCanonicalFourFiveDeepUpperEstimateConstant,
      roughCanonicalExceptionalUpperPhysicalRoughInterval,
      roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
        hfinal
  · let A :=
      roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
        (2 * n - (K0 + 1) * upperTailLength c n)
    let B :=
      roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)
    have hAB : A <= B := by
      dsimp only [A, B, roughCanonicalExceptionalPhysicalLowerEndpoint,
        roughCanonicalExceptionalPhysicalUpperEndpoint]
      rw [max_eq_left hendpoint.high_noClipping]
      exact Nat.div_le_div_right (Nat.sub_le _ _)
    have hgeometry :
        RoughCanonicalExceptionalPhysicalIntervalGeometry
          n deltaStar b A B := by
      simpa only [A, B] using
        (roughCanonicalExceptionalClippedInterval_geometry
          (lo := 2 * n -
            (K0 + 1) * upperTailLength c n)
          (hi := 2 * n)
          hcommon hbPrefix hAB (by omega))
    have htailDepth :
        (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
          2 * (((K0 + 1 : Nat) : Real) * c) *
            (n : Real) / L n := by
      rw [Nat.cast_mul]
      calc
        ((K0 + 1 : Nat) : Real) *
            (upperTailLength c n : Real) <=
          ((K0 + 1 : Nat) : Real) *
            (2 * c * (n : Real) / L n) :=
          mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
        _ =
            2 * (((K0 + 1 : Nat) : Real) * c) *
              (n : Real) / L n := by ring
    have hidealRate :
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) <=
          2 * (((K0 + 1 : Nat) : Real) * c) *
            roughCanonicalExceptionalPhysicalRateScale n b / L n :=
      roughCanonicalFourFiveDeep_shortIdealLength_le
        hbPos (mul_nonneg (Nat.cast_nonneg _) hc) hLone htailDepth
    have hfinal :=
      abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepShortRate
        (P := P) (C := C)
        (D :=
          roughCanonicalFourFiveDeepHighDisplacementConstant K0 c)
        (a := ((K0 + 1 : Nat) : Real) * c)
        (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
        (idealLength :=
          (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real))
        hy hgeometry hP hC
        (roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg K0 hc)
        (mul_nonneg (Nat.cast_nonneg _) hc)
        hLone hlogLower hu0 hbound
        (harithmetic A B hgeometry)
        (by
          simpa only [A, B] using hdisplacement.high_displacement)
        (by
          simpa only [A, B] using hendpoint.high_length_error)
        hidealRate
    simpa only [A, B,
      roughCanonicalFourFiveDeepHighEstimateConstant,
      roughCanonicalExceptionalHighPhysicalRoughInterval,
      roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
        hfinal
  · let A :=
      roughCanonicalExceptionalPhysicalLowerEndpoint
        n deltaStar b n
    let B :=
      roughCanonicalExceptionalPhysicalUpperEndpoint b
        (2 * n - (K0 + 1) * upperTailLength c n)
    let idealLength : Real :=
      ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
        (b : Real)
    have hidealRate :
        idealLength <= roughCanonicalExceptionalPhysicalRateScale n b := by
      calc
        idealLength <= (n : Real) / (b : Real) := by
          dsimp only [idealLength]
          exact
            div_le_div_of_nonneg_right
              (by
                exact_mod_cast
                  (Nat.sub_le n
                    ((K0 + 1) * upperTailLength c n)))
              hbReal.le
        _ <= roughCanonicalExceptionalPhysicalRateScale n b := hcore
    have hlength :
        abs ((((B - A : Nat) : Real)) - idealLength) <=
          2 *
            (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
      simpa only [A, B, idealLength] using hendpoint.broad_length_error
    by_cases hAB : A <= B
    · have hgeometry :
          RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B := by
        simpa only [A, B] using
          (roughCanonicalExceptionalClippedInterval_geometry
            (lo := n)
            (hi := 2 * n -
              (K0 + 1) * upperTailLength c n)
            hcommon hbPrefix hAB (by omega))
      have hfinal :=
        abs_roughCanonicalExceptionalPhysicalInterval_card_sub_idealFrozen_le_deepBroadRate
          (P := P) (C := C)
          (D := roughCanonicalFourFiveDeepBroadDisplacementConstant)
          (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
          (idealLength := idealLength)
          hy hgeometry hP hC
          roughCanonicalFourFiveDeepBroadDisplacementConstant_pos.le
          hLone hlogLower hu0 hbound
          (harithmetic A B hgeometry)
          (by
            simpa only [A, B] using hdisplacement.broad_displacement)
          hlength hidealRate
      simpa only [A, B, idealLength,
        roughCanonicalFourFiveDeepBroadFinalEstimateConstant,
        roughCanonicalExceptionalBroadPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal
    · have hBA : B <= A := by omega
      have hempty :=
        abs_fourFiveRoughInterval_card_sub_idealFrozen_le_deepBroadRate_of_empty
          (n := n) (b := b) (A := A) (B := B)
          (C := C) (u0 := roughCanonicalFourFiveFrozenCoordinate n b)
          (idealLength := idealLength)
          hBA hC hLone hlogLower hu0 hbound hlength
      have hconstant :
          10 * C <=
            roughCanonicalFourFiveDeepBroadFinalEstimateConstant P C := by
        unfold roughCanonicalFourFiveDeepBroadFinalEstimateConstant
          roughCanonicalFourFiveDeepBroadEstimateConstant
        have hCD :
            0 <=
              C * roughCanonicalFourFiveDeepBroadDisplacementConstant :=
          mul_nonneg hC
            roughCanonicalFourFiveDeepBroadDisplacementConstant_pos.le
        nlinarith
      have hscale :
          0 <=
            roughCanonicalExceptionalPhysicalRateScale n b / L n ^ 2 + 1 :=
        add_nonneg (div_nonneg hZ (sq_nonneg (L n))) (by norm_num)
      have hfinal :=
        hempty.trans
          (mul_le_mul_of_nonneg_right hconstant hscale)
      simpa only [A, B, idealLength,
        roughCanonicalExceptionalBroadPhysicalRoughInterval,
        roughCanonicalExceptionalClippedRoughInterval_eq_endpoints] using
          hfinal

/-! ## Eventual three-interval package -/

/-- Uniform eventual upper, high, and clipped-broad estimates on every
deep smooth core.  The three constants are fixed before `n` and are
explicitly nonnegative. -/
theorem
    exists_eventually_roughCanonicalSignedExceptionalDeepIntervalEstimates
    (K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∃ Cplus Chigh Cbroad : Real,
      0 <= Cplus ∧ 0 <= Chigh ∧ 0 <= Cbroad ∧
      ∀ᶠ n : Nat in atTop, ∀ b : Nat,
        b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n ->
          RoughCanonicalSignedExceptionalDeepIntervalEstimate
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
    roughCanonicalFourFiveDeepUpperEstimateConstant P Ckernel c
  let Chigh :=
    roughCanonicalFourFiveDeepHighEstimateConstant
      K0 P Ckernel c
  let Cbroad :=
    roughCanonicalFourFiveDeepBroadFinalEstimateConstant P Ckernel
  refine ⟨Cplus, Chigh, Cbroad, ?_, ?_, ?_, ?_⟩
  · dsimp only [Cplus]
    exact
      roughCanonicalFourFiveDeepUpperEstimateConstant_nonneg
        hP hCkernel.le hc.le
  · dsimp only [Chigh]
    exact
      roughCanonicalFourFiveDeepHighEstimateConstant_nonneg
        K0 hP hCkernel.le hc.le
  · dsimp only [Cbroad]
    exact
      roughCanonicalFourFiveDeepBroadFinalEstimateConstant_nonneg
        hP hCkernel.le
  · have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [
        harithmeticEventually,
        eventually_roughCanonicalExceptionalCommonEndpointGeometry
          hdelta.le hdeltaUpper,
        eventually_roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
          hdelta.le hdeltaUpper,
        eventually_roughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
          K0 hc hdeltaUpper,
        eventually_roughCanonicalFourFiveDeepEndpointLengthErrorsAt
          K0 hc hdelta,
        roughCanonicalExceptional_yNat_tendsto_atTop.eventually
          (eventually_ge_atTop (2 : Nat)),
        hLTop.eventually (eventually_ge_atTop (1 : Real)),
        Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
        eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
        eventually_upperTailLength_le hc]
        with n harithmeticN hcommonN hcoordinateN hdisplacementN
          hendpointN hy hLone hlogLower htailScale htailNat
    intro b hb
    have hbDeep :
        b ∈ Finset.Icc 1
          (tangentPaperExceptionalCutoff deltaStar n / 2) := by
      simpa only [roughCanonicalExceptionalDeepCoreSet] using hb
    have htail :
        (upperTailLength c n : Real) <=
          2 * c * (n : Real) / L n := by
      calc
        (upperTailLength c n : Real) <=
            2 * c * secondOrderScale n := htailScale
        _ = 2 * c * (n : Real) / L n := by
          unfold secondOrderScale L
          ring
    exact
      roughCanonicalSignedExceptionalDeepIntervalEstimate_of_inputs
        hy hc.le hP hCkernel.le hLone hlogLower htail htailNat
        hcommonN (hcoordinateN b hbDeep) hb hbound
        (harithmeticN b)
        (hdisplacementN b hb) (hendpointN b hb)

end BankPaperRealization

end

end Erdos390.WholePaper
