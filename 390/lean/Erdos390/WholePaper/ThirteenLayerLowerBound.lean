import Erdos390.WholePaper.TailValuationCapacity

/-!
# The thirteen-layer lower bound

This module completes the lower-bound half of the paper's main asymptotic
argument.  The new arithmetic input is the fixed-small-prime capacity of the
tail `(2n,2n+h]`; it is proved from the binomial decomposition of the tail,
not assumed as an external estimate.  The final statements use the literal
real difference `f(n)-2n`, avoiding truncated natural subtraction.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The paper's natural cutoff `floor (n / log n)`. -/
def logarithmicShiftBound (n : ℕ) : ℕ :=
  ⌊secondOrderScale n⌋₊

/-- The natural endpoint displacement, used only internally after proving
that the endpoint is strictly above `2n`. -/
def endpointShift (n : ℕ) : ℕ :=
  f n - 2 * n

/-- Truncate the actual endpoint shift to the range where it is `o(n)`.
Outside that range zero is used; the discarded case already gives a stronger
lower bound than the desired constant because `C0 < 1`. -/
def shortEndpointShift (n : ℕ) : ℕ :=
  if endpointShift n ≤ logarithmicShiftBound n then endpointShift n else 0

/-- The deterministic logarithmic error used after summing the nine
small-prime capacities. -/
def smallPrimeCapacityError (n : ℕ) : ℝ :=
  (centralSmallPrimeValuationSum n : ℝ) +
    9 * (Nat.log2 (3 * n) : ℝ)

private theorem tendsto_inv_log_natCast :
    Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ)) atTop (nhds 0) := by
  simpa only [one_div] using
    (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop

/-- The natural logarithmic cutoff is sublinear. -/
theorem logarithmicShiftBound_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (logarithmicShiftBound n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_inv_log_natCast
  · exact Eventually.of_forall fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hnPos : 0 < (n : ℝ) := by positivity
    have hlogPos : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    have hscaleNonneg : 0 ≤ secondOrderScale n :=
      (div_pos hnPos hlogPos).le
    have hfloor : (logarithmicShiftBound n : ℝ) ≤ secondOrderScale n := by
      exact Nat.floor_le hscaleNonneg
    calc
      (logarithmicShiftBound n : ℝ) / (n : ℝ) ≤
          secondOrderScale n / (n : ℝ) :=
        div_le_div_of_nonneg_right hfloor hnPos.le
      _ = 1 / Real.log (n : ℝ) := by
        rw [secondOrderScale]
        field_simp

/-- The truncated actual displacement is sublinear, independently of how
large the untruncated extremal endpoint might be. -/
theorem shortEndpointShift_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ (shortEndpointShift n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    logarithmicShiftBound_ratio_tendsto_zero
  · exact Eventually.of_forall fun n ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · exact Eventually.of_forall fun n ↦ by
      have hshort : shortEndpointShift n ≤ logarithmicShiftBound n := by
        rw [shortEndpointShift]
        split_ifs with h
        · exact h
        · exact Nat.zero_le _
      exact div_le_div_of_nonneg_right (by exact_mod_cast hshort) (Nat.cast_nonneg _)

/-- Eventually the natural cutoff is at most `n`. -/
theorem eventually_logarithmicShiftBound_le :
    ∀ᶠ n : ℕ in atTop, logarithmicShiftBound n ≤ n := by
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnPos : 0 < (n : ℝ) := by positivity
  have hexp : Real.exp 1 < (n : ℝ) := by
    have hdecimal : (2.7182818286 : ℝ) < 3 := by norm_num
    have hnCast : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact Real.exp_one_lt_d9.trans (hdecimal.trans_le hnCast)
  have hlog : 1 < Real.log (n : ℝ) :=
    (Real.lt_log_iff_exp_lt hnPos).2 hexp
  have hscale : secondOrderScale n ≤ (n : ℝ) := by
    rw [secondOrderScale]
    have hlogPos : 0 < Real.log (n : ℝ) := by linarith
    exact (div_le_iff₀ hlogPos).2 (by nlinarith)
  exact_mod_cast (Nat.floor_le_of_le hscale)

/-- The moving union associated with the truncated actual shift has the
full thirteen-row mass. -/
theorem shortEndpointMovingUnion_card_normalized_tendsto :
    Tendsto
      (fun n : ℕ ↦
        ((movingPrimeUnion13 n (2 * n + shortEndpointShift n)).card : ℝ) /
          secondOrderScale n)
      atTop (nhds (A13 : ℝ)) := by
  simpa only [secondOrderScale] using
    movingPrimeUnion13_card_normalized_tendsto
      shortEndpointShift_ratio_tendsto_zero

private theorem tendsto_log_natCast_div_natCast :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem tendsto_log_sq_natCast_div_natCast :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem tendsto_log_three_mul_natCast_mul_log_div_natCast :
    Tendsto
      (fun n : ℕ ↦
        Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hconstant :
      Tendsto (fun _n : ℕ ↦ Real.log 3) atTop (nhds (Real.log 3)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 3 * (Real.log (n : ℝ) / (n : ℝ)) +
            Real.log (n : ℝ) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hconstant.mul tendsto_log_natCast_div_natCast).add
        tendsto_log_sq_natCast_div_natCast
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnReal]
  ring

private theorem tendsto_nine_mul_logb_two_three_mul_normalized :
    Tendsto
      (fun n : ℕ ↦
        (9 * Real.logb 2 (3 * (n : ℝ))) / secondOrderScale n)
      atTop (nhds 0) := by
  have hscaled :
      Tendsto
        (fun n : ℕ ↦
          (9 / Real.log 2) *
            (Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_log_three_mul_natCast_mul_log_div_natCast.const_mul
        (9 / Real.log 2)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos one_lt_two).ne'
  rw [Real.logb, secondOrderScale]
  field_simp

/-- The central and tail logarithmic remainders are negligible on the
second-order scale. -/
theorem smallPrimeCapacityError_normalized_tendsto :
    Tendsto
      (fun n : ℕ ↦ smallPrimeCapacityError n / secondOrderScale n)
      atTop (nhds 0) := by
  have htail :
      Tendsto
        (fun n : ℕ ↦
          (9 * (Nat.log2 (3 * n) : ℝ)) / secondOrderScale n)
        atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      tendsto_nine_mul_logb_two_three_mul_normalized
    · filter_upwards [eventually_gt_atTop 1] with n hn
      have hscale : 0 < secondOrderScale n := by
        exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
      exact div_nonneg (by positivity) hscale.le
    · filter_upwards [eventually_gt_atTop 1] with n hn
      have hscale : 0 < secondOrderScale n := by
        exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
      have hlogBound :
          (Nat.log2 (3 * n) : ℝ) ≤ Real.logb 2 (3 * (n : ℝ)) := by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using
          Real.log2_le_logb (3 * n)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogBound (by norm_num)) hscale.le
  have hsum := centralSmallPrimeValuationSum_normalized_tendsto.add htail
  simpa only [smallPrimeCapacityError, secondOrderScale, add_div,
    add_zero] using hsum

private theorem S23_cast_pos : 0 < (S23 : ℝ) := by
  rw [S23_eq]
  positivity

private theorem A13_cast_eq_C0_mul_S23 :
    (A13 : ℝ) = C0 * (S23 : ℝ) := by
  rw [A13_eq, S23_eq]
  norm_num [C0]

/-- The paper's eventually quantified lower bound for the extremal endpoint.
Both `f n` and `2n` are cast before subtraction in its normalized
consequences; no truncated natural subtraction occurs in the public claim. -/
theorem eventually_f_ge_two_mul_add_C0_sub_eps_mul_secondOrderScale
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) + (C0 - ε) * secondOrderScale n ≤ (f n : ℝ) := by
  let δ : ℝ := ε * (S23 : ℝ) / 4
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact div_pos (mul_pos hε S23_cast_pos) (by norm_num)
  have hunionLower :
      ∀ᶠ n : ℕ in atTop,
        (A13 : ℝ) - δ <
          ((movingPrimeUnion13 n
            (2 * n + shortEndpointShift n)).card : ℝ) /
              secondOrderScale n :=
    shortEndpointMovingUnion_card_normalized_tendsto.eventually
      (Ioi_mem_nhds (sub_lt_self _ hδ))
  have herrorUpper :
      ∀ᶠ n : ℕ in atTop,
        smallPrimeCapacityError n / secondOrderScale n < δ :=
    smallPrimeCapacityError_normalized_tendsto.eventually
      (Iio_mem_nhds hδ)
  filter_upwards [eventually_no_admissibleEndpoint_le_two_mul,
    eventually_ge_atTop 392, eventually_logarithmicShiftBound_le,
    eventually_gt_atTop 1, hunionLower, herrorUpper]
      with n hno hn hbound hnOne hunion herror
  have hnThree : 3 ≤ n := by omega
  have hfAdmissible : IsAdmissibleEndpoint n (f n) := f_spec hnThree
  have hfGt : 2 * n < f n := by
    by_contra hnot
    exact hno (f n) (Nat.le_of_not_gt hnot) hfAdmissible
  have hshiftEq : 2 * n + endpointShift n = f n := by
    rw [endpointShift, Nat.add_sub_of_le hfGt.le]
  have hshiftCast :
      (endpointShift n : ℝ) = (f n : ℝ) - 2 * (n : ℝ) := by
    rw [← hshiftEq]
    push_cast
    ring
  have hnPos : 0 < (n : ℝ) := by positivity
  have hlogPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hnOne)
  have hscalePos : 0 < secondOrderScale n :=
    div_pos hnPos hlogPos
  by_cases hshort : endpointShift n ≤ logarithmicShiftBound n
  · have hshortEq : shortEndpointShift n = endpointShift n := by
      simp [shortEndpointShift, hshort]
    have hhLe : endpointShift n ≤ n := hshort.trans hbound
    have hmovingIncidence :
        (movingPrimeUnion13 n (2 * n + endpointShift n)).card ≤
          ∑ ℓ ∈ smallPrimes,
            ((2 * n + endpointShift n).factorial.factorization ℓ -
              2 * n.factorial.factorization ℓ) := by
      apply movingPrimeUnion13_card_le_factorialValuationSub_of_admissible hn
      rwa [hshiftEq]
    have hcapacity :=
      smallPrimeFactorialValuationSum_cast_le (n := n)
        (h := endpointShift n) hhLe
    have hcardCapacity :
        ((movingPrimeUnion13 n
          (2 * n + endpointShift n)).card : ℝ) ≤
            (endpointShift n : ℝ) * (S23 : ℝ) +
              smallPrimeCapacityError n := by
      exact (by exact_mod_cast hmovingIncidence :
        ((movingPrimeUnion13 n
          (2 * n + endpointShift n)).card : ℝ) ≤
            ((∑ ℓ ∈ smallPrimes,
              ((2 * n + endpointShift n).factorial.factorization ℓ -
                2 * n.factorial.factorization ℓ) : ℕ) : ℝ)).trans
          (by simpa only [smallPrimeCapacityError, add_assoc] using hcapacity)
    have hnormalizedCapacity :
        ((movingPrimeUnion13 n
          (2 * n + endpointShift n)).card : ℝ) / secondOrderScale n ≤
            ((endpointShift n : ℝ) / secondOrderScale n) * (S23 : ℝ) +
              smallPrimeCapacityError n / secondOrderScale n := by
      have hdiv := div_le_div_of_nonneg_right hcardCapacity hscalePos.le
      convert hdiv using 1
      field_simp
    rw [hshortEq] at hunion
    have hratio :
        C0 - ε < (endpointShift n : ℝ) / secondOrderScale n := by
      rw [A13_cast_eq_C0_mul_S23] at hunion
      dsimp only [δ] at hunion herror
      nlinarith [S23_cast_pos]
    have hmul :
        (C0 - ε) * secondOrderScale n <
          ((endpointShift n : ℝ) / secondOrderScale n) *
            secondOrderScale n :=
      mul_lt_mul_of_pos_right hratio hscalePos
    have hshiftLower :
        (C0 - ε) * secondOrderScale n < (endpointShift n : ℝ) := by
      convert hmul using 1
      field_simp
    rw [hshiftCast] at hshiftLower
    linarith
  · have hboundLt : logarithmicShiftBound n < endpointShift n :=
      Nat.lt_of_not_ge hshort
    have hscaleLt : secondOrderScale n < (endpointShift n : ℝ) := by
      have hfloorLt :
          secondOrderScale n < (logarithmicShiftBound n : ℝ) + 1 := by
        exact Nat.lt_floor_add_one _
      have hsuccLe : logarithmicShiftBound n + 1 ≤ endpointShift n := by
        omega
      exact hfloorLt.trans_le (by exact_mod_cast hsuccLe)
    have hcoefficient : C0 - ε < 1 := by
      linarith [C0_lt_one]
    have hshiftLower :
        (C0 - ε) * secondOrderScale n < (endpointShift n : ℝ) :=
      (mul_lt_of_lt_one_left hscalePos hcoefficient).trans hscaleLt
    rw [hshiftCast] at hshiftLower
    linarith

/-- Equivalent normalized eventual lower bound, with the literal real
difference from the paper. -/
theorem eventually_C0_sub_eps_le_normalized_f_sub_two_mul
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      C0 - ε ≤
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
          (n : ℝ) := by
  filter_upwards
    [eventually_f_ge_two_mul_add_C0_sub_eps_mul_secondOrderScale hε,
      eventually_gt_atTop 1]
      with n hnLower hnOne
  have hnPos : 0 < (n : ℝ) := by positivity
  have hlogPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hnOne)
  have hscalePos : 0 < secondOrderScale n :=
    div_pos hnPos hlogPos
  have hdiff :
      (C0 - ε) * secondOrderScale n ≤
        (f n : ℝ) - 2 * (n : ℝ) := by
    linarith
  have hdiv := (le_div_iff₀ hscalePos).2 hdiff
  convert hdiv using 1
  rw [secondOrderScale]
  field_simp

/-- Unconditional liminf form of the thirteen-layer lower bound.  `EReal`
is used only as the codomain of `liminf`, so divergence to `+∞` is handled
correctly; the normalized values themselves are the exact real expression
from the paper. -/
theorem C0_le_liminf_normalized_f_sub_two_mul :
    (C0 : EReal) ≤
      liminf
        (fun n : ℕ ↦
          ((((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
            (n : ℝ) : EReal))
        atTop := by
  rw [le_liminf_iff']
  intro y hy
  obtain ⟨z, hyz, hzC0⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hzC0Real : z < C0 := EReal.coe_lt_coe_iff.mp hzC0
  have heventual :=
    eventually_C0_sub_eps_le_normalized_f_sub_two_mul
      (sub_pos.mpr hzC0Real)
  filter_upwards [heventual] with n hn
  have hzEq : C0 - (C0 - z) = z := by ring
  rw [hzEq] at hn
  exact hyz.le.trans (EReal.coe_le_coe_iff.mpr hn)

end

end Erdos390.WholePaper
