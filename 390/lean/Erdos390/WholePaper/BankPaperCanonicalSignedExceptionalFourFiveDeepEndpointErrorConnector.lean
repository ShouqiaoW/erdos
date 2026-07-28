import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveDeepDisplacementConnector

/-!
# Endpoint-length errors on the deep exceptional core

The three physical intervals use natural quotient endpoints.  Their lower
endpoints are additionally clipped by the literal real exceptional floor.
This file separates the two effects at a deep smooth core.

* The upper and high lower endpoints are eventually not moved by clipping.
  Their literal lengths therefore differ from the ideal quotient lengths by
  at most one.
* The broad lower endpoint remains clipped.  Its clipping excess is bounded
  directly, and its complete endpoint-length error is
  `O(Z / L + 1)`, where
  `Z = roughCanonicalExceptionalPhysicalRateScale n b`.

The broad statement deliberately retains the `max` in the literal endpoint.
No eventual broad no-clipping assertion is made.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A generic clipping triangle -/

/-- Replacing the lower endpoint `q` of a natural interval by `max q r`
changes its length by at most the clipping excess `max q r - q`.

This form remains valid when clipping moves the lower endpoint past the
upper endpoint, because natural subtraction then makes the clipped length
zero. -/
theorem abs_clippedNatIntervalLength_sub_ideal_le
    {q r u : Nat} {ideal endpointError : Real}
    (hqu : q <= u)
    (hquotient :
      abs ((((u - q : Nat) : Real)) - ideal) <= endpointError) :
    abs ((((u - max q r : Nat) : Real)) - ideal) <=
      endpointError + ((max q r - q : Nat) : Real) := by
  have hqmax : q <= max q r := le_max_left q r
  have hclip :
      abs ((((u - max q r : Nat) : Real)) -
          ((u - q : Nat) : Real)) <=
        ((max q r - q : Nat) : Real) := by
    by_cases hmaxu : max q r <= u
    · rw [Nat.cast_sub hmaxu, Nat.cast_sub hqmax, Nat.cast_sub hqu]
      have hnonpos :
          (q : Real) - ((max q r : Nat) : Real) <= 0 := by
        exact sub_nonpos.mpr (by exact_mod_cast hqmax)
      rw [show
          (u : Real) - ((max q r : Nat) : Real) -
              ((u : Real) - (q : Real)) =
            (q : Real) - ((max q r : Nat) : Real) by ring,
        abs_of_nonpos hnonpos, neg_sub]
    · have huMax : u <= max q r := by omega
      have hsub :
          u - q <= max q r - q :=
        Nat.sub_le_sub_right huMax q
      rw [Nat.sub_eq_zero_of_le huMax, Nat.cast_zero, zero_sub, abs_neg,
        abs_of_nonneg (Nat.cast_nonneg (u - q))]
      exact_mod_cast hsub
  calc
    abs ((((u - max q r : Nat) : Real)) - ideal) =
        abs (((((u - max q r : Nat) : Real)) -
            ((u - q : Nat) : Real)) +
          ((((u - q : Nat) : Real)) - ideal)) := by ring
    _ <=
        abs ((((u - max q r : Nat) : Real)) -
            ((u - q : Nat) : Real)) +
          abs ((((u - q : Nat) : Real)) - ideal) :=
      abs_add_le _ _
    _ <= ((max q r - q : Nat) : Real) + endpointError :=
      add_le_add hclip hquotient
    _ = endpointError + ((max q r - q : Nat) : Real) := by ring

/-! ## Deep upper/high no-clipping -/

/-- A real comparison between the literal exceptional threshold and a
quotient descends to the corresponding natural floors. -/
theorem roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
    {n N b : Nat} {deltaStar : Real}
    (hreal :
      2 * (n : Real) / (n : Real) ^ deltaStar <=
        (N : Real) / (b : Real)) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <= N / b := by
  unfold roughCanonicalRealExceptionalRoughCutoff
  rw [← Nat.floor_div_eq_div (K := Real)]
  exact Nat.floor_mono hreal

/-- On a deep core, once `n^deltaStar >= 2` and the high displacement has
length at most `n/2`, clipping moves neither the upper nor the high lower
quotient endpoint. -/
theorem roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n)
    (hpowerTwo : 2 <= (n : Real) ^ deltaStar)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n) / b ∧
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n - (K0 + 1) * upperTailLength c n) / b := by
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hpowerPos : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      (2 : Real) * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  have hcutUpper :=
    tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n
  have hbPower :
      2 * (b : Real) <= (n : Real) ^ deltaStar + 1 :=
    hbTwo.trans hcutUpper.le
  have hbLePower :
      (b : Real) <= (n : Real) ^ deltaStar := by
    nlinarith
  have hupperReal :
      2 * (n : Real) / (n : Real) ^ deltaStar <=
        ((2 * n : Nat) : Real) / (b : Real) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    exact
      div_le_div_of_nonneg_left
        (by positivity) hbPos hbLePower
  have hdepthTwo :
      (K0 + 1) * upperTailLength c n <= 2 * n := by
    omega
  have hdepthReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
        (n : Real) / 2 := by
    calc
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
          ((n / 2 : Nat) : Real) := by exact_mod_cast hdepth
      _ <= (n : Real) / 2 := Nat.cast_div_le (α := Real)
  have hleft :
      2 * (n : Real) * (b : Real) <=
        (n : Real) * ((n : Real) ^ deltaStar + 1) := by
    calc
      2 * (n : Real) * (b : Real) =
          (n : Real) * (2 * (b : Real)) := by ring
      _ <= (n : Real) * ((n : Real) ^ deltaStar + 1) :=
        mul_le_mul_of_nonneg_left hbPower hnReal.le
  have hpowerThreeHalves :
      (n : Real) ^ deltaStar + 1 <=
        (3 / 2 : Real) * (n : Real) ^ deltaStar := by
    nlinarith
  have hmiddle :
      (n : Real) * ((n : Real) ^ deltaStar + 1) <=
        (n : Real) * ((3 / 2 : Real) * (n : Real) ^ deltaStar) :=
    mul_le_mul_of_nonneg_left hpowerThreeHalves hnReal.le
  have hremaining :
      (3 / 2 : Real) * (n : Real) <=
        (2 * n - (K0 + 1) * upperTailLength c n : Nat) := by
    rw [Nat.cast_sub hdepthTwo]
    rw [show ((2 * n : Nat) : Real) =
        2 * (n : Real) by norm_num]
    linarith
  have hright :
      (n : Real) * ((3 / 2 : Real) * (n : Real) ^ deltaStar) <=
        (n : Real) ^ deltaStar *
          (2 * n - (K0 + 1) * upperTailLength c n : Nat) := by
    calc
      (n : Real) * ((3 / 2 : Real) * (n : Real) ^ deltaStar) =
          (n : Real) ^ deltaStar * ((3 / 2 : Real) * (n : Real)) := by
        ring
      _ <=
          (n : Real) ^ deltaStar *
            (2 * n - (K0 + 1) * upperTailLength c n : Nat) :=
        mul_le_mul_of_nonneg_left hremaining hpowerPos.le
  have hhighCross :
      2 * (n : Real) * (b : Real) <=
        (n : Real) ^ deltaStar *
          (2 * n - (K0 + 1) * upperTailLength c n : Nat) :=
    hleft.trans (hmiddle.trans hright)
  have hhighReal :
      2 * (n : Real) / (n : Real) ^ deltaStar <=
        ((2 * n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) := by
    apply (div_le_div_iff₀ hpowerPos hbPos).2
    simpa only [mul_comm] using hhighCross
  exact
    ⟨roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
        hupperReal,
      roughCanonicalRealExceptionalRoughCutoff_le_natQuotient_of_real_le
        hhighReal⟩

/-- The deep upper physical interval has the literal quotient-length error
`<= 1` whenever its lower endpoint is not clipped. -/
theorem roughCanonicalFourFiveDeepUpperEndpointLengthError_le_one
    {n b : Nat} {c deltaStar : Real}
    (hb : 0 < b)
    (hclip :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n) / b) :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n + upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Nat) : Real) -
        (upperTailLength c n : Real) / (b : Real)) <= 1 := by
  simpa only [show
      2 * n + upperTailLength c n - 2 * n =
        upperTailLength c n by omega] using
    (abs_roughCanonicalExceptionalPhysicalEndpoint_length_sub_ideal_le_one
      (n := n) (b := b) (lo := 2 * n)
      (hi := 2 * n + upperTailLength c n)
      (deltaStar := deltaStar) hb (by omega) hclip)

/-- The deep high physical interval has the literal quotient-length error
`<= 1` whenever its lower endpoint is not clipped. -/
theorem roughCanonicalFourFiveDeepHighEndpointLengthError_le_one
    {K0 n b : Nat} {c deltaStar : Real}
    (hb : 0 < b)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n)
    (hclip :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
        (2 * n - (K0 + 1) * upperTailLength c n) / b) :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n) : Nat) : Real) -
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <= 1 := by
  have hdepthTwo :
      (K0 + 1) * upperTailLength c n <= 2 * n := by omega
  have hlength :
      2 * n - (2 * n - (K0 + 1) * upperTailLength c n) =
        (K0 + 1) * upperTailLength c n := by
    omega
  simpa only [hlength] using
    (abs_roughCanonicalExceptionalPhysicalEndpoint_length_sub_ideal_le_one
      (n := n) (b := b)
      (lo := 2 * n - (K0 + 1) * upperTailLength c n)
      (hi := 2 * n) (deltaStar := deltaStar)
      hb (by omega) hclip)

/-! ## The clipped broad endpoint -/

/-- On a deep core, the amount by which the exceptional floor moves the
broad lower quotient endpoint is `O(Z/L+1)`.

The hypothesis `L n <= n^deltaStar` is the only asymptotic comparison used
here.  The `max` is retained in the conclusion. -/
theorem roughCanonicalFourFiveDeepBroadClippingExcess_le
    {n b : Nat} {deltaStar : Real}
    (hn : 0 < n)
    (hLone : 1 <= L n)
    (hLpower : L n <= (n : Real) ^ deltaStar)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    ((max (n / b)
          (roughCanonicalRealExceptionalRoughCutoff n deltaStar) -
        n / b : Nat) : Real) <=
      roughCanonicalExceptionalPhysicalRateScale n b / L n + 1 := by
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hpowerPos : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      2 * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  have hcutCeil :=
    tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n
  have hbPower :
      2 * (b : Real) <= (n : Real) ^ deltaStar + 1 :=
    hbTwo.trans hcutCeil.le
  have hcutFloor :
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real) <=
        2 * (n : Real) / (n : Real) ^ deltaStar := by
    unfold roughCanonicalRealExceptionalRoughCutoff
    exact
      Nat.floor_le
        (div_nonneg (by positivity) hpowerPos.le)
  have hquotientRound :
      (n : Real) / (b : Real) <
        ((n / b : Nat) : Real) + 1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := n) hbPosNat
  have hquotientLower :
      (n : Real) / (b : Real) - 1 <=
        ((n / b : Nat) : Real) := by
    linarith
  have hproduct :
      (2 * (b : Real)) * L n <=
        ((n : Real) ^ deltaStar + 1) *
          (n : Real) ^ deltaStar :=
    mul_le_mul hbPower hLpower hL.le (by positivity)
  have hsmall :
      2 * (n : Real) /
            ((n : Real) ^ deltaStar *
              ((n : Real) ^ deltaStar + 1)) <=
        (n : Real) / ((b : Real) * L n) := by
    apply
      (div_le_div_iff₀
        (mul_pos hpowerPos (by positivity))
        (mul_pos hbPos hL)).2
    calc
      (2 * (n : Real)) * ((b : Real) * L n) =
          (n : Real) * ((2 * (b : Real)) * L n) := by ring
      _ <=
          (n : Real) *
            (((n : Real) ^ deltaStar + 1) *
              (n : Real) ^ deltaStar) :=
        mul_le_mul_of_nonneg_left hproduct hnReal.le
      _ =
          (n : Real) *
            ((n : Real) ^ deltaStar *
              ((n : Real) ^ deltaStar + 1)) := by ring
  have hbDenominator :
      (b : Real) <= ((n : Real) ^ deltaStar + 1) / 2 := by
    linarith
  have hpowerAddOneNe :
      (n : Real) ^ deltaStar + 1 ≠ 0 := by
    positivity
  have hquotientModelLower :
      2 * (n : Real) / ((n : Real) ^ deltaStar + 1) <=
        (n : Real) / (b : Real) := by
    calc
      2 * (n : Real) / ((n : Real) ^ deltaStar + 1) =
          (n : Real) /
            (((n : Real) ^ deltaStar + 1) / 2) := by
        field_simp [hpowerAddOneNe]
      _ <= (n : Real) / (b : Real) :=
        div_le_div_of_nonneg_left hnReal.le hbPos hbDenominator
  have hdifference :
      2 * (n : Real) / (n : Real) ^ deltaStar -
          (n : Real) / (b : Real) <=
        (n : Real) / ((b : Real) * L n) := by
    calc
      2 * (n : Real) / (n : Real) ^ deltaStar -
          (n : Real) / (b : Real) <=
        2 * (n : Real) / (n : Real) ^ deltaStar -
          2 * (n : Real) / ((n : Real) ^ deltaStar + 1) :=
        sub_le_sub_left hquotientModelLower _
      _ =
          2 * (n : Real) /
            ((n : Real) ^ deltaStar *
              ((n : Real) ^ deltaStar + 1)) := by
        field_simp [hpowerPos.ne', hpowerAddOneNe]
        ; ring
      _ <= (n : Real) / ((b : Real) * L n) := hsmall
  have hquotientRate :
      (n : Real) / (b : Real) <=
        roughCanonicalExceptionalPhysicalRateScale n b := by
    have hrateNat :
        n / b + 1 <= 3 * n / b + 1 := by
      exact
        Nat.add_le_add_right
          (Nat.div_le_div_right (by omega : n <= 3 * n)) 1
    calc
      (n : Real) / (b : Real) <=
          ((n / b : Nat) : Real) + 1 :=
        hquotientRound.le
      _ = ((n / b + 1 : Nat) : Real) := by norm_num
      _ <= ((3 * n / b + 1 : Nat) : Real) := by
        exact_mod_cast hrateNat
      _ = roughCanonicalExceptionalPhysicalRateScale n b := by
        rfl
  have hquotientRateDiv :
      (n : Real) / ((b : Real) * L n) <=
        roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    calc
      (n : Real) / ((b : Real) * L n) =
          ((n : Real) / (b : Real)) / L n := by ring
      _ <= roughCanonicalExceptionalPhysicalRateScale n b / L n :=
        div_le_div_of_nonneg_right hquotientRate hL.le
  by_cases hclip :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <= n / b
  · rw [max_eq_left hclip, Nat.sub_self, Nat.cast_zero]
    have hrateNonneg :
        0 <= roughCanonicalExceptionalPhysicalRateScale n b := by
      unfold roughCanonicalExceptionalPhysicalRateScale
      exact_mod_cast (Nat.zero_le (3 * n / b + 1))
    exact add_nonneg
      (div_nonneg hrateNonneg hL.le) (by norm_num)
  · have hquotientCutoff :
        n / b <=
          roughCanonicalRealExceptionalRoughCutoff n deltaStar := by
      omega
    rw [max_eq_right hquotientCutoff,
      Nat.cast_sub hquotientCutoff]
    calc
      (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real) -
          (n / b : Nat) <=
        2 * (n : Real) / (n : Real) ^ deltaStar -
          ((n : Real) / (b : Real) - 1) :=
        sub_le_sub hcutFloor hquotientLower
      _ =
          (2 * (n : Real) / (n : Real) ^ deltaStar -
            (n : Real) / (b : Real)) + 1 := by ring
      _ <= (n : Real) / ((b : Real) * L n) + 1 :=
        by linarith
      _ <=
          roughCanonicalExceptionalPhysicalRateScale n b / L n + 1 :=
        by linarith

/-- The complete clipped broad endpoint-length error is
`O(Z/L+1)`.  In particular, the statement does not replace its lower
endpoint by `n/b`. -/
theorem roughCanonicalFourFiveDeepBroadEndpointLengthError_le
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n)
    (hLone : 1 <= L n)
    (hLpower : L n <= (n : Real) ^ deltaStar)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Nat) : Real) -
        ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <=
      2 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
  have hbData := Finset.mem_Icc.mp hb
  have hbPos : 0 < b := by omega
  have hhighLower :
      n <= 2 * n - (K0 + 1) * upperTailLength c n := by
    omega
  have hquotient :=
    abs_natQuotientIntervalLength_sub_realLength_le_one
      (lo := n)
      (hi := 2 * n - (K0 + 1) * upperTailLength c n)
      (b := b) hbPos hhighLower
  have hphysicalLength :
      (2 * n - (K0 + 1) * upperTailLength c n) - n =
        n - (K0 + 1) * upperTailLength c n := by
    omega
  have hquotient' :
      abs (((((2 * n - (K0 + 1) * upperTailLength c n) / b -
            n / b : Nat) : Real)) -
          ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real)) <= 1 := by
    simpa only [hphysicalLength] using hquotient
  have htriangle :=
    abs_clippedNatIntervalLength_sub_ideal_le
      (q := n / b)
      (r := roughCanonicalRealExceptionalRoughCutoff n deltaStar)
      (u := (2 * n - (K0 + 1) * upperTailLength c n) / b)
      (ideal :=
        ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real))
      (endpointError := 1)
      (Nat.div_le_div_right hhighLower) hquotient'
  have hexcess :=
    roughCanonicalFourFiveDeepBroadClippingExcess_le
      hn hLone hLpower hb
  have hrateNonneg :
      0 <= roughCanonicalExceptionalPhysicalRateScale n b / L n := by
    exact
      div_nonneg
        (by
          unfold roughCanonicalExceptionalPhysicalRateScale
          exact_mod_cast
            (Nat.zero_le (3 * n / b + 1)))
        (zero_lt_one.trans_le hLone).le
  calc
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Nat) : Real) -
        ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <=
      1 +
        ((max (n / b)
              (roughCanonicalRealExceptionalRoughCutoff n deltaStar) -
            n / b : Nat) : Real) := by
      simpa only [roughCanonicalExceptionalPhysicalUpperEndpoint,
        roughCanonicalExceptionalPhysicalLowerEndpoint] using htriangle
    _ <=
        1 +
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) :=
      by linarith
    _ <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) := by
      nlinarith

/-! ## Adapter-facing package -/

/-- The three endpoint-length inputs on one deep smooth core.  Only the two
short intervals record no-clipping; the broad field retains its clipped
lower endpoint. -/
structure RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
    (K0 n b : Nat) (c deltaStar : Real) : Prop where
  upper_noClipping :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
      (2 * n) / b
  high_noClipping :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
      (2 * n - (K0 + 1) * upperTailLength c n) / b
  upper_length_error :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n + upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Nat) : Real) -
        (upperTailLength c n : Real) / (b : Real)) <= 1
  high_length_error :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n) : Nat) : Real) -
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <= 1
  broad_length_error :
    abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n) -
          roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Nat) : Real) -
        ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real)) <=
      2 *
        (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1)

/-- Finite construction of all three endpoint-length inputs from the scale
comparisons used on the deep core. -/
theorem roughCanonicalFourFiveDeepEndpointLengthErrorsAt_of_scale
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n)
    (hLone : 1 <= L n)
    (hLpower : L n <= (n : Real) ^ deltaStar)
    (hpowerTwo : 2 <= (n : Real) ^ deltaStar)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
      K0 n b c deltaStar := by
  have hbPos : 0 < b := by
    have := (Finset.mem_Icc.mp hb).1
    omega
  obtain ⟨hupperClip, hhighClip⟩ :=
    roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
      hn hpowerTwo hdepth hb
  exact
    { upper_noClipping := hupperClip
      high_noClipping := hhighClip
      upper_length_error :=
        roughCanonicalFourFiveDeepUpperEndpointLengthError_le_one
          hbPos hupperClip
      high_length_error :=
        roughCanonicalFourFiveDeepHighEndpointLengthError_le_one
          hbPos (by omega) hhighClip
      broad_length_error :=
        roughCanonicalFourFiveDeepBroadEndpointLengthError_le
          hn hLone hLpower (by omega) hb }

theorem
    RoughCanonicalFourFiveDeepEndpointLengthErrorsAt.upper_adapter_inputs
    {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
        K0 n b c deltaStar) :
    0 <= (1 : Real) ∧
      abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
              (2 * n + upperTailLength c n) -
            roughCanonicalExceptionalPhysicalLowerEndpoint
              n deltaStar b (2 * n) : Nat) : Real) -
          (upperTailLength c n : Real) / (b : Real)) <= 1 :=
  ⟨by norm_num, h.upper_length_error⟩

theorem
    RoughCanonicalFourFiveDeepEndpointLengthErrorsAt.high_adapter_inputs
    {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
        K0 n b c deltaStar) :
    0 <= (1 : Real) ∧
      abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) -
            roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
              (2 * n - (K0 + 1) * upperTailLength c n) : Nat) : Real) -
          (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real)) <= 1 :=
  ⟨by norm_num, h.high_length_error⟩

theorem
    RoughCanonicalFourFiveDeepEndpointLengthErrorsAt.broad_adapter_inputs
    {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
        K0 n b c deltaStar) :
    0 <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) ∧
      abs (((roughCanonicalExceptionalPhysicalUpperEndpoint b
              (2 * n - (K0 + 1) * upperTailLength c n) -
            roughCanonicalExceptionalPhysicalLowerEndpoint
              n deltaStar b n : Nat) : Real) -
          ((n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real)) <=
        2 *
          (roughCanonicalExceptionalPhysicalRateScale n b / L n + 1) :=
  ⟨(abs_nonneg _).trans h.broad_length_error, h.broad_length_error⟩

/-! ## Eventual deep-core form -/

/-- A fixed positive exceptional exponent eventually dominates the one
logarithm needed by the broad clipping estimate. -/
theorem eventually_deepEndpointError_L_le_rpow
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      L n <= (n : Real) ^ deltaStar := by
  have hreal :
      Tendsto
        (fun x : Real =>
          Real.log x ^ (1 : Real) / x ^ deltaStar)
        atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop
      (1 : Real) hdelta).tendsto_div_nhds_zero
  have hratio :
      Tendsto
        (fun n : Nat => L n / (n : Real) ^ deltaStar)
        atTop (nhds 0) := by
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    apply hnat.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    simp only [Function.comp_apply, L, Real.rpow_one]
  have hratioOne :=
    hratio.eventually
      (eventually_le_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratioOne, eventually_gt_atTop 0] with n hratioOne hn
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hpowerPos : 0 < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  exact (div_le_one hpowerPos).mp hratioOne

/-- The upper and high deep endpoints are eventually simultaneously
unclipped.  No broad no-clipping conclusion is included. -/
theorem eventually_roughCanonicalFourFiveDeepUpperHigh_noClipping
    (K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop, ∀ b : Nat,
      b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n ->
        roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
            (2 * n) / b ∧
          roughCanonicalRealExceptionalRoughCutoff n deltaStar <=
            (2 * n - (K0 + 1) * upperTailLength c n) / b := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_gt_atTop (0 : Nat),
      hLTop.eventually (eventually_ge_atTop (2 : Real)),
      eventually_deepEndpointError_L_le_rpow hdelta,
      eventually_deepFrozenDisplacement_depth_le_half K0 hc]
      with n hn hLtwo hLpower hdepth
  intro b hb
  have hbDeep :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2) := by
    simpa only [roughCanonicalExceptionalDeepCoreSet] using hb
  exact
    roughCanonicalFourFiveDeepUpperHigh_noClipping_of_scale
      hn (hLtwo.trans hLpower) hdepth hbDeep

/-- All three deep endpoint-length inputs hold simultaneously eventually.
The broad conclusion remains the clipped `O(Z/L+1)` statement. -/
theorem eventually_roughCanonicalFourFiveDeepEndpointLengthErrorsAt
    (K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop, ∀ b : Nat,
      b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n ->
        RoughCanonicalFourFiveDeepEndpointLengthErrorsAt
          K0 n b c deltaStar := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_gt_atTop (0 : Nat),
      hLTop.eventually (eventually_ge_atTop (2 : Real)),
      eventually_deepEndpointError_L_le_rpow hdelta,
      eventually_deepFrozenDisplacement_depth_le_half K0 hc]
      with n hn hLtwo hLpower hdepth
  intro b hb
  have hbDeep :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2) := by
    simpa only [roughCanonicalExceptionalDeepCoreSet] using hb
  exact
    roughCanonicalFourFiveDeepEndpointLengthErrorsAt_of_scale
      hn (by linarith) hLpower (hLtwo.trans hLpower) hdepth hbDeep

end BankPaperRealization

end

end Erdos390.WholePaper
