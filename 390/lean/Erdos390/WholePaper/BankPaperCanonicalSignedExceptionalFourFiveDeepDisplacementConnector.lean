import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveChamberConnector

/-!
# Frozen-coordinate displacement on the deep exceptional core

This file isolates the displacement input used when the continuum mixture
kernel is frozen at

`log((2n)/b) / log(yNat n)`.

Natural quotient rounding contributes one unit at each lower endpoint.
On the deep prefix, the existing bound
`tangentPaperExceptionalCutoff <= n / L^2` absorbs that unit.  The upper and
high intervals then have displacement `O(1/L^2)`, while the broad interval
has displacement `O(1/L)`.

Only endpoint arithmetic and previously proved scale bounds occur here.
No interval count and no clipping-length estimate is asserted.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A normalized logarithmic displacement lemma -/

/-- If `t` is at least `s/R` and differs from `s` by at most `E`, then the
normalized logarithmic coordinates differ by at most
`R*E/(s*log y)`. -/
theorem abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
    {y : Nat} {s t R E : Real}
    (hlog : 0 < Real.log (y : Real))
    (hs : 0 < s) (hR : 1 <= R) (hE : 0 <= E)
    (htLower : s / R <= t)
    (hdistance : abs (t - s) <= E) :
    abs (Real.log t / Real.log (y : Real) -
        Real.log s / Real.log (y : Real)) <=
      R * E / (s * Real.log (y : Real)) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have htPos : 0 < t :=
    (div_pos hs hRpos).trans_le htLower
  have hlogAbs :
      abs (Real.log t - Real.log s) <= R * E / s := by
    by_cases hts : t <= s
    · have hlogTS : Real.log t <= Real.log s :=
        Real.log_le_log htPos hts
      have hgap : s - t <= E := by
        calc
          s - t <= abs (s - t) := le_abs_self _
          _ = abs (t - s) := abs_sub_comm _ _
          _ <= E := hdistance
      have hsRt : s <= t * R :=
        (div_le_iff₀ hRpos).mp htLower
      have hgapRatio :
          (s - t) / t <= R * E / s := by
        apply (div_le_div_iff₀ htPos hs).2
        calc
          (s - t) * s <= E * s :=
            mul_le_mul_of_nonneg_right hgap hs.le
          _ <= E * (t * R) :=
            mul_le_mul_of_nonneg_left hsRt hE
          _ = (R * E) * t := by ring
      rw [abs_of_nonpos (sub_nonpos.mpr hlogTS), neg_sub]
      calc
        Real.log s - Real.log t = Real.log (s / t) :=
          (Real.log_div hs.ne' htPos.ne').symm
        _ <= s / t - 1 :=
          Real.log_le_sub_one_of_pos (div_pos hs htPos)
        _ = (s - t) / t := by
          field_simp [htPos.ne']
        _ <= R * E / s := hgapRatio
    · have hst : s <= t := le_of_not_ge hts
      have hlogST : Real.log s <= Real.log t :=
        Real.log_le_log hs hst
      have hgap : t - s <= E := by
        exact (le_abs_self (t - s)).trans hdistance
      have hscaleE : E <= R * E := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hR) hE]
      rw [abs_of_nonneg (sub_nonneg.mpr hlogST)]
      calc
        Real.log t - Real.log s = Real.log (t / s) :=
          (Real.log_div htPos.ne' hs.ne').symm
        _ <= t / s - 1 :=
          Real.log_le_sub_one_of_pos (div_pos htPos hs)
        _ = (t - s) / s := by
          field_simp [hs.ne']
        _ <= E / s :=
          div_le_div_of_nonneg_right hgap hs.le
        _ <= (R * E) / s :=
          div_le_div_of_nonneg_right hscaleE hs.le
  rw [← sub_div, abs_div, abs_of_pos hlog]
  calc
    abs (Real.log t - Real.log s) / Real.log (y : Real) <=
        (R * E / s) / Real.log (y : Real) :=
      div_le_div_of_nonneg_right hlogAbs hlog.le
    _ = R * E / (s * Real.log (y : Real)) := by ring

/-! ## Fixed rate constants -/

def roughCanonicalFourFiveDeepUpperDisplacementConstant
    (c : Real) : Real :=
  15 * (c + 1)

def roughCanonicalFourFiveDeepHighDisplacementConstant
    (K0 : Nat) (c : Real) : Real :=
  15 * (((K0 + 1 : Nat) : Real) * c + 1)

def roughCanonicalFourFiveDeepBroadDisplacementConstant : Real :=
  15

theorem roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg
    {c : Real} (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveDeepUpperDisplacementConstant c := by
  unfold roughCanonicalFourFiveDeepUpperDisplacementConstant
  positivity

theorem roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg
    (K0 : Nat) {c : Real} (hc : 0 <= c) :
    0 <= roughCanonicalFourFiveDeepHighDisplacementConstant K0 c := by
  unfold roughCanonicalFourFiveDeepHighDisplacementConstant
  positivity

theorem roughCanonicalFourFiveDeepBroadDisplacementConstant_pos :
    0 < roughCanonicalFourFiveDeepBroadDisplacementConstant := by
  unfold roughCanonicalFourFiveDeepBroadDisplacementConstant
  norm_num

/-! ## Elementary deep-prefix scale reductions -/

private theorem deepCore_cast_le_self_div_two_L_sq
    {n b : Nat} {deltaStar : Real}
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2))
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2) :
    (b : Real) <= (n : Real) / (2 * L n ^ 2) := by
  have hbData := Finset.mem_Icc.mp hb
  have hbTwoNat :
      2 * b <= tangentPaperExceptionalCutoff deltaStar n := by
    omega
  have hbTwo :
      (2 : Real) * (b : Real) <=
        (tangentPaperExceptionalCutoff deltaStar n : Real) := by
    exact_mod_cast hbTwoNat
  calc
    (b : Real) = (2 * (b : Real)) / 2 := by ring
    _ <= (tangentPaperExceptionalCutoff deltaStar n : Real) / 2 :=
      div_le_div_of_nonneg_right hbTwo (by norm_num)
    _ <= ((n : Real) / L n ^ 2) / 2 :=
      div_le_div_of_nonneg_right hcutoff (by norm_num)
    _ = (n : Real) / (2 * L n ^ 2) := by ring

private theorem deepCore_cast_le_self_div_two
    {n b : Nat} {deltaStar : Real}
    (hLone : 1 <= L n)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2))
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2) :
    (b : Real) <= (n : Real) / 2 := by
  have hbScale :=
    deepCore_cast_le_self_div_two_L_sq hb hcutoff
  have hLsq : 1 <= L n ^ 2 :=
    one_le_pow₀ (n := 2) hLone
  calc
    (b : Real) <= (n : Real) / (2 * L n ^ 2) := hbScale
    _ <= (n : Real) / 2 := by
      exact
        div_le_div_of_nonneg_left
          (Nat.cast_nonneg n) (by norm_num)
          (by nlinarith : (2 : Real) <= 2 * L n ^ 2)

private theorem short_displacement_scale
    {n : Nat} {H B a : Real}
    (hn : 0 < n) (ha : 0 <= a)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (_hH : 0 <= H)
    (hHupper : H <= 2 * a * (n : Real) / L n)
    (_hB : 0 <= B)
    (hBupper : B <= (n : Real) / (2 * L n ^ 2)) :
    ((H + B) / (n : Real)) *
        (1 / Real.log (yNat n : Real)) <=
      15 * (a + 1) / L n ^ 2 := by
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hHratio :
      H / (n : Real) <= 2 * a / L n := by
    calc
      H / (n : Real) <=
          (2 * a * (n : Real) / L n) / (n : Real) :=
        div_le_div_of_nonneg_right hHupper hnReal.le
      _ = 2 * a / L n := by
        field_simp [hnReal.ne', hL.ne']
  have hBratio :
      B / (n : Real) <= 1 / (2 * L n ^ 2) := by
    calc
      B / (n : Real) <=
          ((n : Real) / (2 * L n ^ 2)) / (n : Real) :=
        div_le_div_of_nonneg_right hBupper hnReal.le
      _ = 1 / (2 * L n ^ 2) := by
        field_simp [hnReal.ne', hL.ne']
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hproduct :
      (H / (n : Real) + B / (n : Real)) *
          (1 / Real.log (yNat n : Real)) <=
        (2 * a / L n + 1 / (2 * L n ^ 2)) *
          (5 / L n) := by
    exact
      mul_le_mul (add_le_add hHratio hBratio) hinvLog
        (one_div_nonneg.mpr hlog.le)
        (add_nonneg (div_nonneg (by positivity) hL.le)
          (div_nonneg (by norm_num)
            (mul_nonneg (by norm_num) (sq_nonneg (L n)))))
  have hLsqPos : 0 < L n ^ 2 := sq_pos_of_pos hL
  have hLsqLeCube : L n ^ 2 <= L n ^ 3 := by
    calc
      L n ^ 2 = L n ^ 2 * 1 := by ring
      _ <= L n ^ 2 * L n :=
        mul_le_mul_of_nonneg_left hLone (sq_nonneg (L n))
      _ = L n ^ 3 := by ring
  have hround :
      5 / (2 * L n ^ 3) <= 5 / (2 * L n ^ 2) := by
    exact
      div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (by norm_num) hLsqPos)
        (mul_le_mul_of_nonneg_left hLsqLeCube (by norm_num))
  calc
    ((H + B) / (n : Real)) *
        (1 / Real.log (yNat n : Real)) =
        (H / (n : Real) + B / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := by ring
    _ <= (2 * a / L n + 1 / (2 * L n ^ 2)) *
          (5 / L n) := hproduct
    _ = 10 * a / L n ^ 2 + 5 / (2 * L n ^ 3) := by ring
    _ <= 10 * a / L n ^ 2 + 5 / (2 * L n ^ 2) :=
      add_le_add le_rfl hround
    _ = (10 * a + 5 / 2) / L n ^ 2 := by ring
    _ <= 15 * (a + 1) / L n ^ 2 := by
      exact
        div_le_div_of_nonneg_right
          (by nlinarith : 10 * a + 5 / 2 <= 15 * (a + 1))
          hLsqPos.le

/-! ## Finite displacement bounds in adapter form -/

theorem
    roughCanonicalFourFiveDeepUpperFrozenDisplacement_le
    {n b : Nat} {c deltaStar : Real}
    (hn : 0 < n) (hc : 0 < c)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint
          b (2 * n + upperTailLength c n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepUpperDisplacementConstant c /
          L n ^ 2 := by
  intro t ht
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hbScale :=
    deepCore_cast_le_self_div_two_L_sq hb hcutoff
  have hbHalf :=
    deepCore_cast_le_self_div_two hLone hb hcutoff
  have hsPos :
      0 < 2 * (n : Real) / (b : Real) :=
    div_pos (by positivity) hbPos
  have hsFour :
      4 <= 2 * (n : Real) / (b : Real) := by
    apply (le_div_iff₀ hbPos).2
    nlinarith
  have hqLeLower :
      (2 * n) / b <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n) := by
    unfold roughCanonicalExceptionalPhysicalLowerEndpoint
    exact le_max_left _ _
  have htLowerQuotient :
      (((2 * n) / b : Nat) : Real) <= t := by
    have hcast :
        (((2 * n) / b : Nat) : Real) <=
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Real) := by
      exact_mod_cast hqLeLower
    exact hcast.trans ht.1
  have hqRound :
      2 * (n : Real) / (b : Real) <
        (((2 * n) / b : Nat) : Real) + 1 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (roughRealQuotient_lt_natQuotient_add_one
        (N := 2 * n) hbPosNat)
  have hlowerError :
      2 * (n : Real) / (b : Real) - t < 1 := by
    linarith
  have htUpper :
      t <= ((2 * n + upperTailLength c n : Nat) : Real) /
          (b : Real) := by
    calc
      t <=
          (roughCanonicalExceptionalPhysicalUpperEndpoint
            b (2 * n + upperTailLength c n) : Real) := ht.2
      _ = (((2 * n + upperTailLength c n) / b : Nat) : Real) := rfl
      _ <= ((2 * n + upperTailLength c n : Nat) : Real) /
          (b : Real) := Nat.cast_div_le (α := Real)
  have hupperModel :
      ((2 * n + upperTailLength c n : Nat) : Real) / (b : Real) =
        2 * (n : Real) / (b : Real) +
          (upperTailLength c n : Real) / (b : Real) := by
    push_cast
    ring
  have hupperError :
      t - 2 * (n : Real) / (b : Real) <=
        (upperTailLength c n : Real) / (b : Real) := by
    rw [hupperModel] at htUpper
    linarith
  have hE :
      0 <= (upperTailLength c n : Real) / (b : Real) + 1 := by
    positivity
  have hdistance :
      abs (t - 2 * (n : Real) / (b : Real)) <=
        (upperTailLength c n : Real) / (b : Real) + 1 := by
    rw [abs_le]
    constructor
    · have htailDivNonneg :
          0 <= (upperTailLength c n : Real) / (b : Real) :=
        div_nonneg (Nat.cast_nonneg _) hbPos.le
      have hlower' :
          -(1 : Real) < t - 2 * (n : Real) / (b : Real) := by
        calc
          -(1 : Real) <
              -(2 * (n : Real) / (b : Real) - t) :=
            neg_lt_neg hlowerError
          _ = t - 2 * (n : Real) / (b : Real) := by ring
      linarith
    · linarith [hupperError]
  have hhalf :
      (2 * (n : Real) / (b : Real)) / 2 <= t := by
    nlinarith
  have hraw :=
    abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
      (y := yNat n) (s := 2 * (n : Real) / (b : Real))
      (t := t) (R := 2)
      (E := (upperTailLength c n : Real) / (b : Real) + 1)
      hlog hsPos (by norm_num) hE hhalf hdistance
  have hrawEq :
      2 * ((upperTailLength c n : Real) / (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) =
        (((upperTailLength c n : Real) + (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := by
    field_simp [hbPos.ne', hnReal.ne', hlog.ne']
  have hscale :=
    short_displacement_scale
      (n := n) (H := (upperTailLength c n : Real))
      (B := (b : Real)) (a := c)
      hn hc.le hLone hlogLower (Nat.cast_nonneg _) htail
      (Nat.cast_nonneg _) hbScale
  calc
    abs (Real.log t / Real.log (yNat n : Real) -
        roughCanonicalFourFiveFrozenCoordinate n b) <=
        2 * ((upperTailLength c n : Real) / (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) := by
      simpa only [roughCanonicalFourFiveFrozenCoordinate] using hraw
    _ = (((upperTailLength c n : Real) + (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := hrawEq
    _ <= roughCanonicalFourFiveDeepUpperDisplacementConstant c /
          L n ^ 2 := by
      exact hscale

theorem
    roughCanonicalFourFiveDeepHighFrozenDisplacement_le
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n) (hc : 0 < c)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c /
          L n ^ 2 := by
  intro t ht
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hbScale :=
    deepCore_cast_le_self_div_two_L_sq hb hcutoff
  have hbHalf :=
    deepCore_cast_le_self_div_two hLone hb hcutoff
  have hsPos :
      0 < 2 * (n : Real) / (b : Real) :=
    div_pos (by positivity) hbPos
  have hsFour :
      4 <= 2 * (n : Real) / (b : Real) := by
    apply (le_div_iff₀ hbPos).2
    nlinarith
  have hdepthTwo :
      (K0 + 1) * upperTailLength c n <= 2 * n := by
    omega
  have hqLeLower :
      (2 * n - (K0 + 1) * upperTailLength c n) / b <=
        roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n) := by
    unfold roughCanonicalExceptionalPhysicalLowerEndpoint
    exact le_max_left _ _
  have htLowerQuotient :
      (((2 * n - (K0 + 1) * upperTailLength c n) / b : Nat) : Real) <=
        t := by
    have hcast :
        (((2 * n - (K0 + 1) * upperTailLength c n) / b : Nat) : Real) <=
          (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n) : Real) := by
      exact_mod_cast hqLeLower
    exact hcast.trans ht.1
  have hqRound :
      ((2 * n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) <
        (((2 * n - (K0 + 1) * upperTailLength c n) / b : Nat) : Real) +
          1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := 2 * n - (K0 + 1) * upperTailLength c n) hbPosNat
  have hlowModel :
      ((2 * n - (K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) =
        2 * (n : Real) / (b : Real) -
          (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) := by
    rw [Nat.cast_sub hdepthTwo]
    push_cast
    ring
  have hlowerError :
      2 * (n : Real) / (b : Real) - t <
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 := by
    rw [hlowModel] at hqRound
    linarith
  have htUpperQuotient :
      t <= (((2 * n) / b : Nat) : Real) := by
    simpa only [roughCanonicalExceptionalPhysicalUpperEndpoint] using ht.2
  have htUpper :
      t <= 2 * (n : Real) / (b : Real) := by
    exact htUpperQuotient.trans
      (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (Nat.cast_div_le :
            (((2 * n) / b : Nat) : Real) <=
              ((2 * n : Nat) : Real) / (b : Real)))
  have hE :
      0 <=
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 := by
    positivity
  have hdistance :
      abs (t - 2 * (n : Real) / (b : Real)) <=
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 := by
    rw [abs_le]
    constructor <;> linarith
  have hdepthReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
        (n : Real) / 2 := by
    calc
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
          ((n / 2 : Nat) : Real) := by exact_mod_cast hdepth
      _ <= (n : Real) / 2 := Nat.cast_div_le (α := Real)
  have hsum :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) +
          (b : Real) <= (n : Real) := by
    linarith
  have hEHalf :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 <=
        (2 * (n : Real) / (b : Real)) / 2 := by
    calc
      (((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1 =
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) +
            (b : Real)) / (b : Real) := by
        field_simp [hbPos.ne']
      _ <= (n : Real) / (b : Real) :=
        div_le_div_of_nonneg_right hsum hbPos.le
      _ = (2 * (n : Real) / (b : Real)) / 2 := by ring
  have hhalf :
      (2 * (n : Real) / (b : Real)) / 2 <= t := by
    linarith
  have hraw :=
    abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
      (y := yNat n) (s := 2 * (n : Real) / (b : Real))
      (t := t) (R := 2)
      (E :=
        (((K0 + 1) * upperTailLength c n : Nat) : Real) /
          (b : Real) + 1)
      hlog hsPos (by norm_num) hE hhalf hdistance
  have hrawEq :
      2 *
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) =
        (((((K0 + 1) * upperTailLength c n : Nat) : Real) +
            (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := by
    field_simp [hbPos.ne', hnReal.ne', hlog.ne']
  have htailDepth :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <=
        2 * (((K0 + 1 : Nat) : Real) * c) *
          (n : Real) / L n := by
    norm_num only [Nat.cast_mul]
    calc
      ((K0 + 1 : Nat) : Real) * (upperTailLength c n : Real) <=
          ((K0 + 1 : Nat) : Real) *
            (2 * c * (n : Real) / L n) :=
        mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _)
      _ = 2 * (((K0 + 1 : Nat) : Real) * c) *
          (n : Real) / L n := by ring
  have hscale :=
    short_displacement_scale
      (n := n)
      (H := (((K0 + 1) * upperTailLength c n : Nat) : Real))
      (B := (b : Real)) (a := ((K0 + 1 : Nat) : Real) * c)
      hn (mul_nonneg (Nat.cast_nonneg _) hc.le)
      hLone hlogLower (Nat.cast_nonneg _) htailDepth
      (Nat.cast_nonneg _) hbScale
  calc
    abs (Real.log t / Real.log (yNat n : Real) -
        roughCanonicalFourFiveFrozenCoordinate n b) <=
        2 *
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) := by
      simpa only [roughCanonicalFourFiveFrozenCoordinate] using hraw
    _ =
        (((((K0 + 1) * upperTailLength c n : Nat) : Real) +
            (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := hrawEq
    _ <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c /
          L n ^ 2 := by
      exact hscale

theorem
    roughCanonicalFourFiveDeepBroadFrozenDisplacement_le
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2)
    (_hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepBroadDisplacementConstant / L n := by
  intro t ht
  have hbData := Finset.mem_Icc.mp hb
  have hbPosNat : 0 < b := by omega
  have hbPos : (0 : Real) < (b : Real) := by
    exact_mod_cast hbPosNat
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hlog : 0 < Real.log (yNat n : Real) :=
    (mul_pos (by norm_num) hL).trans_le hlogLower
  have hbHalf :=
    deepCore_cast_le_self_div_two hLone hb hcutoff
  have hsPos :
      0 < 2 * (n : Real) / (b : Real) :=
    div_pos (by positivity) hbPos
  have hsFour :
      4 <= 2 * (n : Real) / (b : Real) := by
    apply (le_div_iff₀ hbPos).2
    nlinarith
  have hqLeLower :
      n / b <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n := by
    unfold roughCanonicalExceptionalPhysicalLowerEndpoint
    exact le_max_left _ _
  have htLowerQuotient :
      ((n / b : Nat) : Real) <= t := by
    have hcast :
        ((n / b : Nat) : Real) <=
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Real) := by
      exact_mod_cast hqLeLower
    exact hcast.trans ht.1
  have hqRound :
      (n : Real) / (b : Real) <
        ((n / b : Nat) : Real) + 1 :=
    roughRealQuotient_lt_natQuotient_add_one
      (N := n) hbPosNat
  have hlowerError :
      (n : Real) / (b : Real) - t < 1 := by
    linarith
  have hupperNat :
      roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n) <=
        (2 * n) / b := by
    unfold roughCanonicalExceptionalPhysicalUpperEndpoint
    exact Nat.div_le_div_right (Nat.sub_le _ _)
  have htUpperQuotient :
      t <= (((2 * n) / b : Nat) : Real) := by
    have hcast :
        (roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real) <=
          (((2 * n) / b : Nat) : Real) := by
      exact_mod_cast hupperNat
    exact ht.2.trans hcast
  have htUpper :
      t <= 2 * (n : Real) / (b : Real) := by
    exact htUpperQuotient.trans
      (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          (Nat.cast_div_le :
            (((2 * n) / b : Nat) : Real) <=
              ((2 * n : Nat) : Real) / (b : Real)))
  have hlowerFrozenError :
      2 * (n : Real) / (b : Real) - t <
        (n : Real) / (b : Real) + 1 := by
    calc
      2 * (n : Real) / (b : Real) - t =
          ((n : Real) / (b : Real) - t) +
            (n : Real) / (b : Real) := by ring
      _ < 1 + (n : Real) / (b : Real) := by
        linarith
      _ = (n : Real) / (b : Real) + 1 := by ring
  have hE :
      0 <= (n : Real) / (b : Real) + 1 := by
    positivity
  have hdistance :
      abs (t - 2 * (n : Real) / (b : Real)) <=
        (n : Real) / (b : Real) + 1 := by
    rw [abs_le]
    constructor
    · have hlower' :
          -((n : Real) / (b : Real) + 1) <
            t - 2 * (n : Real) / (b : Real) := by
        calc
          -((n : Real) / (b : Real) + 1) <
              -(2 * (n : Real) / (b : Real) - t) :=
            neg_lt_neg hlowerFrozenError
          _ = t - 2 * (n : Real) / (b : Real) := by ring
      exact hlower'.le
    · exact (sub_nonpos.mpr htUpper).trans hE
  have hquarter :
      (2 * (n : Real) / (b : Real)) / 4 <= t := by
    nlinarith
  have hraw :=
    abs_normalizedLog_sub_le_of_div_le_and_abs_sub_le
      (y := yNat n) (s := 2 * (n : Real) / (b : Real))
      (t := t) (R := 4)
      (E := (n : Real) / (b : Real) + 1)
      hlog hsPos (by norm_num) hE hquarter hdistance
  have hrawEq :
      4 * ((n : Real) / (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) =
        (2 * ((n : Real) + (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := by
    field_simp [hbPos.ne', hnReal.ne', hlog.ne']; ring
  have hfirst :
      2 * ((n : Real) + (b : Real)) / (n : Real) <= 3 := by
    apply (div_le_iff₀ hnReal).2
    nlinarith
  have hinvLog :
      1 / Real.log (yNat n : Real) <= 5 / L n := by
    apply (div_le_div_iff₀ hlog hL).2
    nlinarith [hlogLower]
  have hscale :
      (2 * ((n : Real) + (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) <=
        15 / L n := by
    calc
      (2 * ((n : Real) + (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) <=
          3 * (5 / L n) :=
        mul_le_mul hfirst hinvLog
          (one_div_nonneg.mpr hlog.le) (by norm_num)
      _ = 15 / L n := by ring
  calc
    abs (Real.log t / Real.log (yNat n : Real) -
        roughCanonicalFourFiveFrozenCoordinate n b) <=
        4 * ((n : Real) / (b : Real) + 1) /
          ((2 * (n : Real) / (b : Real)) *
            Real.log (yNat n : Real)) := by
      simpa only [roughCanonicalFourFiveFrozenCoordinate] using hraw
    _ = (2 * ((n : Real) + (b : Real)) / (n : Real)) *
          (1 / Real.log (yNat n : Real)) := hrawEq
    _ <= roughCanonicalFourFiveDeepBroadDisplacementConstant / L n := by
      exact hscale

/-! ## Simultaneous adapter-facing packaging -/

structure RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
    (K0 n b : Nat) (c deltaStar : Real) : Prop where
  upper_D_nonneg :
    0 <= roughCanonicalFourFiveDeepUpperDisplacementConstant c / L n ^ 2
  upper_displacement :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint
          b (2 * n + upperTailLength c n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepUpperDisplacementConstant c / L n ^ 2
  high_D_nonneg :
    0 <=
      roughCanonicalFourFiveDeepHighDisplacementConstant K0 c / L n ^ 2
  high_displacement :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c / L n ^ 2
  broad_D_nonneg :
    0 <= roughCanonicalFourFiveDeepBroadDisplacementConstant / L n
  broad_displacement :
    ∀ t ∈ Set.Icc
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n : Real)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n) : Real),
      abs (Real.log t / Real.log (yNat n : Real) -
          roughCanonicalFourFiveFrozenCoordinate n b) <=
        roughCanonicalFourFiveDeepBroadDisplacementConstant / L n

theorem
    roughCanonicalFourFiveDeepFrozenDisplacementBoundsAt_of_scale
    {K0 n b : Nat} {c deltaStar : Real}
    (hn : 0 < n) (hc : 0 < c)
    (hLone : 1 <= L n)
    (hlogLower :
      (1 / 5 : Real) * L n <= Real.log (yNat n : Real))
    (htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n)
    (hcutoff :
      (tangentPaperExceptionalCutoff deltaStar n : Real) <=
        (n : Real) / L n ^ 2)
    (hdepth :
      (K0 + 1) * upperTailLength c n <= n / 2)
    (hb :
      b ∈ Finset.Icc 1
        (tangentPaperExceptionalCutoff deltaStar n / 2)) :
    RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
      K0 n b c deltaStar := by
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  exact
    { upper_D_nonneg :=
        div_nonneg
          (roughCanonicalFourFiveDeepUpperDisplacementConstant_nonneg hc.le)
          (sq_nonneg (L n))
      upper_displacement :=
        roughCanonicalFourFiveDeepUpperFrozenDisplacement_le
          hn hc hLone hlogLower htail hcutoff hb
      high_D_nonneg :=
        div_nonneg
          (roughCanonicalFourFiveDeepHighDisplacementConstant_nonneg
            K0 hc.le)
          (sq_nonneg (L n))
      high_displacement :=
        roughCanonicalFourFiveDeepHighFrozenDisplacement_le
          hn hc hLone hlogLower htail hcutoff hdepth hb
      broad_D_nonneg :=
        div_nonneg
          roughCanonicalFourFiveDeepBroadDisplacementConstant_pos.le hL.le
      broad_displacement :=
        roughCanonicalFourFiveDeepBroadFrozenDisplacement_le
          hn hLone hlogLower hcutoff hdepth hb }

theorem
    RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt.upper_adapter_inputs
    {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
        K0 n b c deltaStar) :
    0 <= roughCanonicalFourFiveDeepUpperDisplacementConstant c / L n ^ 2 ∧
      (∀ t ∈ Set.Icc
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b (2 * n) : Real)
          (roughCanonicalExceptionalPhysicalUpperEndpoint
            b (2 * n + upperTailLength c n) : Real),
        abs (Real.log t / Real.log (yNat n : Real) -
            roughCanonicalFourFiveFrozenCoordinate n b) <=
          roughCanonicalFourFiveDeepUpperDisplacementConstant c /
            L n ^ 2) :=
  ⟨h.upper_D_nonneg, h.upper_displacement⟩

theorem
    RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt.high_adapter_inputs
    {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
        K0 n b c deltaStar) :
    0 <=
        roughCanonicalFourFiveDeepHighDisplacementConstant K0 c / L n ^ 2 ∧
      (∀ t ∈ Set.Icc
          (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
            (2 * n - (K0 + 1) * upperTailLength c n) : Real)
          (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n) : Real),
        abs (Real.log t / Real.log (yNat n : Real) -
            roughCanonicalFourFiveFrozenCoordinate n b) <=
          roughCanonicalFourFiveDeepHighDisplacementConstant K0 c /
            L n ^ 2) :=
  ⟨h.high_D_nonneg, h.high_displacement⟩

theorem
    RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt.broad_adapter_inputs
    {K0 n b : Nat} {c deltaStar : Real}
    (h :
      RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
        K0 n b c deltaStar) :
    0 <= roughCanonicalFourFiveDeepBroadDisplacementConstant / L n ∧
      (∀ t ∈ Set.Icc
          (roughCanonicalExceptionalPhysicalLowerEndpoint
            n deltaStar b n : Real)
          (roughCanonicalExceptionalPhysicalUpperEndpoint b
            (2 * n - (K0 + 1) * upperTailLength c n) : Real),
        abs (Real.log t / Real.log (yNat n : Real) -
            roughCanonicalFourFiveFrozenCoordinate n b) <=
          roughCanonicalFourFiveDeepBroadDisplacementConstant / L n) :=
  ⟨h.broad_D_nonneg, h.broad_displacement⟩

/-! ## Eventual simultaneous form -/

theorem eventually_deepFrozenDisplacement_depth_le_half
    (K0 : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      (K0 + 1) * upperTailLength c n <= n / 2 := by
  have hKpos : (0 : Real) < ((K0 + 1 : Nat) : Real) := by positivity
  have hthreshold :
      0 < 1 / (2 * ((K0 + 1 : Nat) : Real)) := by positivity
  have hsmall :=
    (upperTailLength_ratio_tendsto_zero hc).eventually
      (eventually_lt_nhds hthreshold)
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have htail :
      (upperTailLength c n : Real) <
        (n : Real) / (2 * ((K0 + 1 : Nat) : Real)) := by
    have hcross := (div_lt_iff₀ hnReal).mp hratio
    calc
      (upperTailLength c n : Real) <
          (1 / (2 * ((K0 + 1 : Nat) : Real))) * (n : Real) :=
        hcross
      _ = (n : Real) / (2 * ((K0 + 1 : Nat) : Real)) := by ring
  have hcross :
      2 * ((K0 + 1 : Nat) : Real) *
          (upperTailLength c n : Real) < (n : Real) := by
    have := (lt_div_iff₀ (mul_pos (by norm_num) hKpos)).mp htail
    nlinarith
  have hnat :
      (2 * (K0 + 1)) * upperTailLength c n < n := by
    exact_mod_cast hcross
  have hnat' :
      2 * ((K0 + 1) * upperTailLength c n) < n := by
    simpa only [mul_assoc] using hnat
  omega

theorem
    eventually_roughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
    (K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop, ∀ b : Nat,
      b ∈ roughCanonicalExceptionalDeepCoreSet deltaStar n ->
        RoughCanonicalFourFiveDeepFrozenDisplacementBoundsAt
          K0 n b c deltaStar := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdeltaOne : deltaStar < 1 :=
    hdeltaUpper.trans (by norm_num)
  filter_upwards [
      eventually_gt_atTop (0 : Nat),
      hLTop.eventually (eventually_ge_atTop (1 : Real)),
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_tangentPaperExceptionalCutoff_le_self_div_L_sq hdeltaOne,
      eventually_deepFrozenDisplacement_depth_le_half K0 hc]
      with n hn hLone hlogLower htailScale hcutoff hdepth
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
    roughCanonicalFourFiveDeepFrozenDisplacementBoundsAt_of_scale
      hn hc hLone hlogLower htail hcutoff hdepth hbDeep

end BankPaperRealization

end

end Erdos390.WholePaper
