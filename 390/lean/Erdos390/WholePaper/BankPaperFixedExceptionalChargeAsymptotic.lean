import Erdos390.WholePaper.BankPaperFixedExceptionalBacking
import Erdos390.WholePaper.BankPaperFixedExceptionalValuationFibers
import Erdos390.WholePaper.ExceptionalValuationSums
import Erdos390.WholePaper.TangentPaperCleanListAbsorption

/-!
# Asymptotic package for the fixed exceptional low-prime charge

This file records the constants and scale arithmetic used after the finite
weighted Selberg decomposition of `G_fix` has been proved.  In the notation
of the paper,

* `paperExceptionalSelbergMainConstant` is `C_S`;
* `paperExceptionalSelbergRemainderConstant` is `C_R`;
* `paperExceptionalChargeConstant c` is `A_exc(c)`;
* `paperExceptionalChargeEpsilon deltaStar n` is the normalized
  endpoint/remainder coefficient.

The finite majorant below is obtained by composing the separate finite
rough/smooth-fibre argument with the elementary valuation-prefix estimates.
Nothing in this file assumes that the actual exceptional charge satisfies
that majorant.  We prove the finite charge bound and its analytic packaging,
together with the independent arithmetic support fact that, under the
displayed paper-range hypotheses, the actual low-prime charge is exactly
zero above twice the paper's literal real exceptional cutoff.  The
corresponding safe integral-cutoff statement is retained as a corollary.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Auditable paper constants -/

/-- The fixed smoothness exponent `theta=2/9`. -/
def paperExceptionalTheta : ℝ :=
  2 / 9

/-- `C_S`, the already verified canonical Selberg main-term constant. -/
def paperExceptionalSelbergMainConstant : ℝ :=
  tangentSelbergCanonicalMainConstant

/-- `C_R`, enlarged once so that it pays both the Lambda-squared endpoint
remainder and a copy of the main-term constant. -/
def paperExceptionalSelbergRemainderConstant : ℝ :=
  tangentSelbergCanonicalLambdaConstant ^ 2 +
    paperExceptionalSelbergMainConstant

/-- The paper's exceptional-charge coefficient
`A_exc(c)=16*c*C_S`; it is positive (and hence nonnegative) when `c>0`. -/
def paperExceptionalChargeConstant (c : ℝ) : ℝ :=
  16 * c * paperExceptionalSelbergMainConstant

theorem paperExceptionalTheta_pos :
    0 < paperExceptionalTheta := by
  norm_num [paperExceptionalTheta]

theorem paperExceptionalSelbergMainConstant_pos :
    0 < paperExceptionalSelbergMainConstant := by
  exact tangentSelbergCanonicalMainConstant_pos

theorem paperExceptionalSelbergRemainderConstant_pos :
    0 < paperExceptionalSelbergRemainderConstant := by
  unfold paperExceptionalSelbergRemainderConstant
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    paperExceptionalSelbergMainConstant_pos

theorem paperExceptionalChargeConstant_pos
    {c : ℝ} (hc : 0 < c) :
    0 < paperExceptionalChargeConstant c := by
  unfold paperExceptionalChargeConstant
  exact mul_pos (mul_pos (by norm_num) hc)
    paperExceptionalSelbergMainConstant_pos

/-! ## The finite Selberg output and its normalized remainder -/

/-- The exact canonical finite upper bound which the finite
rough/smooth-fibre theorem must supply.  Its two summands are respectively

`4*C_S*deltaStar*L*h/(p*log Y)` and
`4*C_R*X*Y^4/(p*(log Y)^2)`,

with `h=ceil(c*n/log n)`, `X=ceil(n^deltaStar)`, and
`Y=floor(n^(2/9))`. -/
def paperExceptionalFiniteChargeMajorant
    (c deltaStar : ℝ) (n p : ℕ) : ℝ :=
  4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
        (upperTailLength c n : ℝ) /
      ((p : ℝ) * Real.log (yNat n : ℝ)) +
    4 * paperExceptionalSelbergRemainderConstant *
        (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
        (yNat n : ℝ) ^ 4 /
      ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2)

/-- The normalized endpoint/remainder coefficient.  In the paper range
`0 ≤ deltaStar < 1/18` it is `o(1)`, and in the eventual regime where the
displayed denominators are nonzero, multiplication by `N/(pL)`, where
`N=n/L`, recovers the second summand of
`paperExceptionalFiniteChargeMajorant`. -/
def paperExceptionalChargeEpsilon
    (deltaStar : ℝ) (n : ℕ) : ℝ :=
  4 * paperExceptionalSelbergRemainderConstant *
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
      (yNat n : ℝ) ^ 4 * L n ^ 2 /
    ((n : ℝ) * Real.log (yNat n : ℝ) ^ 2)

theorem paperExceptionalChargeEpsilon_nonneg
    (deltaStar : ℝ) (n : ℕ) :
    0 ≤ paperExceptionalChargeEpsilon deltaStar n := by
  unfold paperExceptionalChargeEpsilon
  have hC : 0 ≤ paperExceptionalSelbergRemainderConstant :=
    paperExceptionalSelbergRemainderConstant_pos.le
  positivity

/-- The integer quotient length of the upper physical interval costs at
most its real length plus one. -/
theorem paperExceptionalQuotientLength_cast_le
    {n h b : ℕ} (hb : 0 < b) :
    ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ)) ≤
      (h : ℝ) / (b : ℝ) + 1 := by
  have habs := quotientIocLength_sub_realLengthDiv_abs_lt_one
    (D := b) (lo := 2 * n) (hi := 2 * n + h) hb (by omega)
  have hright := (abs_lt.mp habs).2
  have hsub : 2 * n + h - 2 * n = h := by omega
  rw [hsub] at hright
  linarith

/-- The literal remainder term is exactly `epsilon(n) N/(pL)`. -/
theorem paperExceptionalFiniteRemainder_eq_epsilon_mul_scale
    {deltaStar : ℝ} {n p : ℕ}
    (hn : 1 < n) (hp : 0 < p)
    (hlogY : 0 < Real.log (yNat n : ℝ)) :
    4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) =
      paperExceptionalChargeEpsilon deltaStar n *
        secondOrderScale n / ((p : ℝ) * L n) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < L n := L_pos hn
  unfold paperExceptionalChargeEpsilon secondOrderScale
  rw [show Real.log (n : ℝ) = L n by rfl]
  field_simp [hnR.ne', hpR.ne', hL.ne', hlogY.ne']

/-! ## The endpoint remainder tends to zero -/

/-- Pointwise power majorant for the normalized endpoint remainder. -/
theorem eventually_paperExceptionalChargeEpsilon_le_power
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      paperExceptionalChargeEpsilon deltaStar n ≤
        200 * paperExceptionalSelbergRemainderConstant *
          (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hn hlogY
  have hnR : (0 : ℝ) < n := by positivity
  have hL : 0 < L n := L_pos (by omega)
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      hdeltaNonneg
  have hcut :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        2 * (n : ℝ) ^ deltaStar := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
          (n : ℝ) ^ deltaStar + 1 :=
        (tangentPaperExceptionalCutoff_cast_lt_add_one
          deltaStar n).le
      _ ≤ 2 * (n : ℝ) ^ deltaStar := by linarith
  have hyFour := tangentExceptional_yNat_pow_four_le n
  have hpowerIdentity :
      (n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ) /
          (n : ℝ) =
        (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
    rw [← Real.rpow_add hnR]
    calc
      (n : ℝ) ^ (deltaStar + 8 / 9) / (n : ℝ) =
          (n : ℝ) ^ (deltaStar + 8 / 9) /
            (n : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (n : ℝ) ^ (deltaStar + 8 / 9 - 1) :=
        (Real.rpow_sub hnR (deltaStar + 8 / 9) 1).symm
  have hproduct :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ) ≤
        2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ) ≤
        (2 * (n : ℝ) ^ deltaStar *
          (n : ℝ) ^ (8 / 9 : ℝ)) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul hcut hyFour (by positivity) (by positivity)) hnR.le
      _ = 2 * ((n : ℝ) ^ deltaStar *
          (n : ℝ) ^ (8 / 9 : ℝ) / (n : ℝ)) := by ring
      _ = 2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
        rw [hpowerIdentity]
  have hLLe : L n ≤ 5 * Real.log (yNat n : ℝ) := by
    nlinarith [hlogY]
  have hLSq : L n ^ 2 ≤
      (5 * Real.log (yNat n : ℝ)) ^ 2 :=
    (sq_le_sq₀ hL.le (by positivity)).2 hLLe
  have hratio :
      L n ^ 2 / Real.log (yNat n : ℝ) ^ 2 ≤ 25 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogYPos)).2
    calc
      L n ^ 2 ≤ (5 * Real.log (yNat n : ℝ)) ^ 2 := hLSq
      _ = 25 * Real.log (yNat n : ℝ) ^ 2 := by ring
  have hcoefficient :
      0 ≤ 4 * paperExceptionalSelbergRemainderConstant := by
    exact mul_nonneg (by norm_num)
      paperExceptionalSelbergRemainderConstant_pos.le
  have hpowerNonneg : 0 ≤
      2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by positivity
  rw [paperExceptionalChargeEpsilon]
  calc
    4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 * L n ^ 2 /
        ((n : ℝ) * Real.log (yNat n : ℝ) ^ 2) =
      (4 * paperExceptionalSelbergRemainderConstant) *
        ((tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ)) *
      (L n ^ 2 / Real.log (yNat n : ℝ) ^ 2) := by
      field_simp [hnR.ne', hlogYPos.ne']
    _ ≤ (4 * paperExceptionalSelbergRemainderConstant) *
        (2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1)) *
        (L n ^ 2 / Real.log (yNat n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hproduct hcoefficient)
        (div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ ≤ (4 * paperExceptionalSelbergRemainderConstant) *
        (2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1)) * 25 :=
      mul_le_mul_of_nonneg_left hratio
        (mul_nonneg hcoefficient hpowerNonneg)
    _ = 200 * paperExceptionalSelbergRemainderConstant *
        (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by ring

/-- The endpoint/remainder coefficient is genuinely `o(1)` when
`0 ≤ deltaStar < 1/18`. -/
theorem paperExceptionalChargeEpsilon_tendsto_zero
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    Tendsto (paperExceptionalChargeEpsilon deltaStar)
      atTop (nhds 0) := by
  apply squeeze_zero'
  · exact Eventually.of_forall
      (paperExceptionalChargeEpsilon_nonneg deltaStar)
  · exact eventually_paperExceptionalChargeEpsilon_le_power
      hdeltaNonneg
  · simpa only [mul_zero] using
      (tangentExceptional_remainderPower_tendsto_zero
        hdeltaUpper).const_mul
          (200 * paperExceptionalSelbergRemainderConstant)

/-! ## Uniform packaging of the finite majorant -/

/-- Eventually the literal tail ceiling is at most `2cN`. -/
theorem eventually_upperTailLength_cast_le_two_mul_secondOrderScale
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) / secondOrderScale n ≤
        2 * c :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_le_nhds (by linarith : c < 2 * c))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n hn hscale
  exact (div_le_iff₀ hscale).mp hn

/-- The harmless `1+log(2X)` in the finite harmonic sum is eventually
absorbed by a second copy of `deltaStar*L`. -/
theorem eventually_one_add_log_two_mul_exceptionalCutoff_le
    {deltaStar : ℝ} (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      1 + Real.log
          ((2 * tangentPaperExceptionalCutoff deltaStar n : ℕ) : ℝ) ≤
        2 * deltaStar * L n := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := hLTop.eventually
    (eventually_ge_atTop
      ((1 + 2 * Real.log 2) / deltaStar))
  filter_upwards [eventually_ge_atTop 1, hlarge] with n hn hLn
  have hcutPosNat :
      0 < tangentPaperExceptionalCutoff deltaStar n :=
    tangentPaperExceptionalCutoff_pos hdelta.le hn
  have hcutPos :
      (0 : ℝ) < tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast hcutPosNat
  have hcutLog := tangentPaperExceptionalCutoff_log_le
    hdelta.le hn
  have hdeltaDominates :
      1 + 2 * Real.log 2 ≤ deltaStar * L n := by
    have h := (div_le_iff₀ hdelta).mp hLn
    simpa only [mul_comm] using h
  have hlogProduct :
      Real.log
          ((2 * tangentPaperExceptionalCutoff deltaStar n : ℕ) : ℝ) =
        Real.log 2 +
          Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hcutPos.ne']
  rw [hlogProduct]
  nlinarith

/-- The finite Selberg main term fits inside the paper's displayed
`A_exc*(deltaStar/theta)*N/p` reserve.  The constants deliberately retain
the paper's slack: the finite calculation gives `40*c*C_S`, whereas
`A_exc/theta=72*c*C_S`. -/
theorem paperExceptionalFiniteChargeMain_le_paperReserve
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar)
    {n p : ℕ} (hn : 1 < n) (hp : 0 < p)
    (hlogY : (1 / 5 : ℝ) * L n ≤
      Real.log (yNat n : ℝ))
    (htail : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n) :
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) ≤
      paperExceptionalChargeConstant c *
        (deltaStar / paperExceptionalTheta) *
        secondOrderScale n / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hL : 0 < L n := L_pos hn
  have hscale : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have htailDiv :
      (upperTailLength c n : ℝ) / (p : ℝ) ≤
        (2 * c * secondOrderScale n) / (p : ℝ) :=
    div_le_div_of_nonneg_right htail hpR.le
  have hLlog :
      L n / Real.log (yNat n : ℝ) ≤ 5 := by
    apply (div_le_iff₀ hlogYPos).2
    nlinarith [hlogY]
  have hcoefficient :
      0 ≤ 4 * paperExceptionalSelbergMainConstant * deltaStar := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) paperExceptionalSelbergMainConstant_pos.le)
      hdelta.le
  have hLlogNonneg :
      0 ≤ L n / Real.log (yNat n : ℝ) := by positivity
  have hbase : 0 ≤
      c * paperExceptionalSelbergMainConstant * deltaStar *
        secondOrderScale n / (p : ℝ) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hc.le paperExceptionalSelbergMainConstant_pos.le)
          hdelta.le)
        hscale.le)
      hpR.le
  calc
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) =
      (4 * paperExceptionalSelbergMainConstant * deltaStar) *
        ((upperTailLength c n : ℝ) / (p : ℝ)) *
        (L n / Real.log (yNat n : ℝ)) := by
      field_simp [hpR.ne', hlogYPos.ne']
    _ ≤ (4 * paperExceptionalSelbergMainConstant * deltaStar) *
        ((2 * c * secondOrderScale n) / (p : ℝ)) *
        (L n / Real.log (yNat n : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htailDiv hcoefficient)
        hLlogNonneg
    _ ≤ (4 * paperExceptionalSelbergMainConstant * deltaStar) *
        ((2 * c * secondOrderScale n) / (p : ℝ)) * 5 :=
      mul_le_mul_of_nonneg_left hLlog
        (mul_nonneg hcoefficient
          (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc.le)
            hscale.le) hpR.le))
    _ = 40 *
        (c * paperExceptionalSelbergMainConstant * deltaStar *
          secondOrderScale n / (p : ℝ)) := by ring
    _ ≤ 72 *
        (c * paperExceptionalSelbergMainConstant * deltaStar *
          secondOrderScale n / (p : ℝ)) :=
      mul_le_mul_of_nonneg_right (by norm_num) hbase
    _ = paperExceptionalChargeConstant c *
        (deltaStar / paperExceptionalTheta) *
        secondOrderScale n / (p : ℝ) := by
      norm_num [paperExceptionalChargeConstant, paperExceptionalTheta]
      ring

/-- Uniform asymptotic packaging of the canonical finite majorant.  This is
the theorem to compose with the finite weighted-fibre estimate; it does not
postulate that estimate. -/
theorem eventually_paperExceptionalFiniteChargeMajorant_le
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      paperExceptionalFiniteChargeMajorant c deltaStar n p ≤
        paperExceptionalChargeConstant c *
            (deltaStar / paperExceptionalTheta) *
            secondOrderScale n / (p : ℝ) +
          paperExceptionalChargeEpsilon deltaStar n *
            secondOrderScale n / ((p : ℝ) * L n) := by
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc]
      with n hn hlogY htail
  intro p hp
  have hlogYPos : 0 < Real.log (yNat n : ℝ) := by
    have hL : 0 < L n := L_pos (by omega)
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have hmain := paperExceptionalFiniteChargeMain_le_paperReserve
    hc hdelta (n := n) (p := p) (by omega) hp hlogY htail
  have hremainder := paperExceptionalFiniteRemainder_eq_epsilon_mul_scale
    (deltaStar := deltaStar) (n := n) (p := p) (by omega) hp hlogYPos
  unfold paperExceptionalFiniteChargeMajorant
  calc
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) +
        4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) ≤
      paperExceptionalChargeConstant c *
          (deltaStar / paperExceptionalTheta) *
          secondOrderScale n / (p : ℝ) +
        4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) :=
      add_le_add_left hmain _
    _ = paperExceptionalChargeConstant c *
          (deltaStar / paperExceptionalTheta) *
          secondOrderScale n / (p : ℝ) +
        paperExceptionalChargeEpsilon deltaStar n *
          secondOrderScale n / ((p : ℝ) * L n) := by
      rw [hremainder]

/-! ## Exact support cutoff for the actual fixed charge -/

/-- A literal exceptional upper factor has smooth part strictly below twice
the paper's real cutoff `n^deltaStar`, once the paper tail lies below `n`.
This is the exact support statement used in the paper's assertion that the
exceptional charge vanishes for `p > 2*n^deltaStar`. -/
theorem completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    (completeSmoothPart (yNat n) a : ℝ) <
      2 * (n : ℝ) ^ deltaStar := by
  have haData := mem_paperExceptionalUpperFactors.mp ha
  have haBounds : 2 * n < a ∧ a ≤ 2 * n + h := by
    simpa only [roughUpperBlock, Finset.mem_Ioc] using haData.1
  have haUpper : a ≤ 3 * n := by omega
  let rough := completeRoughLabel (yNat n) a
  let smooth := completeSmoothPart (yNat n) a
  have hroughPos : 0 < rough := completeRoughLabel_pos (yNat n) a
  have hroughR : (0 : ℝ) < rough := by exact_mod_cast hroughPos
  have hsmoothLe : (smooth : ℝ) ≤ (a : ℝ) / (rough : ℝ) := by
    exact Nat.cast_div_le
  have haUpperR : (a : ℝ) ≤ 3 * (n : ℝ) := by
    exact_mod_cast haUpper
  have haDiv : (a : ℝ) / (rough : ℝ) ≤
      3 * (n : ℝ) / (rough : ℝ) :=
    div_le_div_of_nonneg_right haUpperR hroughR.le
  have hexceptional :
      2 * (n : ℝ) / (rough : ℝ) <
        (n : ℝ) ^ deltaStar := by
    simpa only [rough] using haData.2
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdeltaNonneg
  have hthree :
      3 * (n : ℝ) / (rough : ℝ) =
        (3 / 2 : ℝ) *
          (2 * (n : ℝ) / (rough : ℝ)) := by ring
  have hthreePower :
      3 * (n : ℝ) / (rough : ℝ) <
        2 * (n : ℝ) ^ deltaStar := by
    rw [hthree]
    nlinarith
  exact hsmoothLe.trans_lt (haDiv.trans_lt hthreePower)

/-- Safe integral-cutoff corollary of the literal real support bound. -/
theorem completeSmoothPart_lt_two_mul_exceptionalCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    completeSmoothPart (yNat n) a <
      2 * tangentPaperExceptionalCutoff deltaStar n := by
  have hsmoothReal :=
    completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
      hdeltaNonneg hn hh ha
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hsmoothCast : (completeSmoothPart (yNat n) a : ℝ) <
      2 * (tangentPaperExceptionalCutoff deltaStar n : ℝ) :=
    hsmoothReal.trans_le
      (mul_le_mul_of_nonneg_left hcut (by norm_num))
  exact_mod_cast hsmoothCast

/-- Every smooth part which actually occurs is contained in the positive
prefix used by the valuation-sum lemmas. -/
theorem paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h : ℕ} (hn : 1 ≤ n) (hh : h ≤ n) :
    paperExceptionalSmoothParts n h deltaStar ⊆
      Finset.Icc 1 (2 * tangentPaperExceptionalCutoff deltaStar n) := by
  intro b hb
  obtain ⟨a, haExceptional, hab⟩ :=
    mem_paperExceptionalSmoothParts.mp hb
  have haPos : 0 < a := paperExceptionalUpperFactors_pos haExceptional
  have hbPos : 0 < b := by
    simpa only [hab] using completeSmoothPart_pos
      (y := yNat n) (a := a) haPos
  have hbLt : b < 2 * tangentPaperExceptionalCutoff deltaStar n := by
    simpa only [hab] using
      completeSmoothPart_lt_two_mul_exceptionalCutoff
        hdeltaNonneg hn hh haExceptional
  exact Finset.mem_Icc.mpr ⟨hbPos, hbLt.le⟩

/-! ## Closing the finite weighted Selberg estimate -/

/-- The actual low-prime valuation of `G_fix` is eventually bounded by the
canonical finite majorant.  This theorem is the composition of the literal
smooth-fibre decomposition, the canonical Lambda-squared interval sieve,
and the elementary valuation prefix estimates; it has no charge-bound
premise. -/
theorem eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
            ℝ) ≤
          paperExceptionalFiniteChargeMajorant c deltaStar n p := by
  filter_upwards
    [eventually_ge_atTop 3,
      eventually_upperTailLength_le hc,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_one_add_log_two_mul_exceptionalCutoff_le hdelta,
      eventually_paperExceptionalSmoothFiber_card_le_canonicalLambdaSquare]
      with n hn htail hlogY hcutLog hfiber
  intro R p hpPrime hpLow
  let h := upperTailLength c n
  let X := tangentPaperExceptionalCutoff deltaStar n
  let Y := yNat n
  let smoothParts := paperExceptionalSmoothParts n h deltaStar
  have hnOne : 1 ≤ n := by omega
  have hpPos : 0 < p := hpPrime.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have hL : 0 < L n := L_pos (by omega)
  have hlogYPos : 0 < Real.log (Y : ℝ) := by
    exact (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le
      (by simpa only [Y] using hlogY)
  have hYOne : (1 : ℝ) ≤ Y := by
    have hYgt : (1 : ℝ) < Y :=
      (Real.log_pos_iff (Nat.cast_nonneg Y)).mp hlogYPos
    exact hYgt.le
  have hlogYLeY : Real.log (Y : ℝ) ≤ (Y : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Y)
    linarith
  have hYLeFour : (Y : ℝ) ≤ (Y : ℝ) ^ 4 := by
    have hcube : (1 : ℝ) ≤ (Y : ℝ) ^ 3 :=
      one_le_pow₀ hYOne
    calc
      (Y : ℝ) = (Y : ℝ) * 1 := by ring
      _ ≤ (Y : ℝ) * (Y : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (Nat.cast_nonneg Y)
      _ = (Y : ℝ) ^ 4 := by ring
  have hlogYLeFour :
      Real.log (Y : ℝ) ≤ (Y : ℝ) ^ 4 :=
    hlogYLeY.trans hYLeFour
  have hXPos : 0 < X := by
    exact tangentPaperExceptionalCutoff_pos hdelta.le hnOne
  have hBOne : 1 ≤ 2 * X := by omega
  have hsmoothSubset : smoothParts ⊆ Finset.Icc 1 (2 * X) := by
    simpa only [smoothParts, h, X] using
      paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
        hdelta.le hnOne htail
  have hchargeNat :=
    R.paperFixedExceptionalFactors_prod_factorization_le_smoothFiberSum
      (deltaStar := deltaStar) hpLow
  have hchargeCast :
      (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
          ℝ) ≤
        ((∑ b ∈ smoothParts,
            b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card : ℕ) :
          ℝ) := by
    dsimp only [smoothParts, h]
    exact_mod_cast hchargeNat
  have hcharge :
      (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
          ℝ) ≤
        ∑ b ∈ smoothParts,
          (b.factorization p : ℝ) *
            ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) := by
    calc
      (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
          ℝ) ≤
        ((∑ b ∈ smoothParts,
            b.factorization p *
              (paperExceptionalSmoothFiber n h deltaStar b).card : ℕ) :
          ℝ) := hchargeCast
      _ = ∑ b ∈ smoothParts,
          (b.factorization p : ℝ) *
            ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) := by
        push_cast
        rfl
  have hrest :
      paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 ≤
        paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2 := by
    have hmainRest :
        paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) ≤
          paperExceptionalSelbergMainConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 := by
      calc
        paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) =
            paperExceptionalSelbergMainConstant * Real.log (Y : ℝ) /
              Real.log (Y : ℝ) ^ 2 := by
          field_simp [hlogYPos.ne']
        _ ≤ paperExceptionalSelbergMainConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hlogYLeFour
              paperExceptionalSelbergMainConstant_pos.le)
            (sq_nonneg _)
    calc
      paperExceptionalSelbergMainConstant / Real.log (Y : ℝ) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 ≤
        paperExceptionalSelbergMainConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2 :=
      add_le_add_left hmainRest _
      _ = paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2 := by
        unfold paperExceptionalSelbergRemainderConstant
        unfold paperExceptionalSelbergMainConstant
        ring
  have hpointwise : ∀ b ∈ smoothParts,
      (b.factorization p : ℝ) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        ((h : ℝ) * paperExceptionalSelbergMainConstant /
            Real.log (Y : ℝ)) *
            ((b.factorization p : ℝ) / (b : ℝ)) +
          (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2) *
            (b.factorization p : ℝ) := by
    intro b hb
    have hbIcc := Finset.mem_Icc.mp (hsmoothSubset hb)
    have hbPos : 0 < b := by omega
    have hbR : (0 : ℝ) < b := by exact_mod_cast hbPos
    have hfiberB := hfiber h b deltaStar
    have hlength := paperExceptionalQuotientLength_cast_le
      (n := n) (h := h) hbPos
    have hcard :
        ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
          (h : ℝ) * paperExceptionalSelbergMainConstant /
              (Real.log (Y : ℝ) * (b : ℝ)) +
            paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2 := by
      calc
        ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
            ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ) *
                (tangentSelbergCanonicalMainConstant /
                  Real.log (Y : ℝ)) +
              tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (Y : ℝ) ^ 4 / Real.log (Y : ℝ) ^ 2) := by
          simpa only [Y] using hfiberB
        _ ≤ ((h : ℝ) / (b : ℝ) + 1) *
                (paperExceptionalSelbergMainConstant /
                  Real.log (Y : ℝ)) +
              tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (Y : ℝ) ^ 4 / Real.log (Y : ℝ) ^ 2 := by
          apply add_le_add_left
          exact mul_le_mul_of_nonneg_right hlength
            (div_nonneg paperExceptionalSelbergMainConstant_pos.le
              hlogYPos.le)
        _ = (h : ℝ) * paperExceptionalSelbergMainConstant /
                (Real.log (Y : ℝ) * (b : ℝ)) +
              (paperExceptionalSelbergMainConstant /
                  Real.log (Y : ℝ) +
                tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (Y : ℝ) ^ 4 / Real.log (Y : ℝ) ^ 2) := by
          field_simp [hbR.ne', hlogYPos.ne']
          ; ring
        _ ≤ (h : ℝ) * paperExceptionalSelbergMainConstant /
                (Real.log (Y : ℝ) * (b : ℝ)) +
              paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
                Real.log (Y : ℝ) ^ 2 := add_le_add_right hrest _
    have hmul := mul_le_mul_of_nonneg_left hcard
      (Nat.cast_nonneg (b.factorization p))
    calc
      (b.factorization p : ℝ) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) ≤
        (b.factorization p : ℝ) *
          ((h : ℝ) * paperExceptionalSelbergMainConstant /
              (Real.log (Y : ℝ) * (b : ℝ)) +
            paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2) := hmul
      _ = ((h : ℝ) * paperExceptionalSelbergMainConstant /
              Real.log (Y : ℝ)) *
            ((b.factorization p : ℝ) / (b : ℝ)) +
          (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
              Real.log (Y : ℝ) ^ 2) *
            (b.factorization p : ℝ) := by
        field_simp [hbR.ne', hlogYPos.ne']
  have hweightedSubset :
      (∑ b ∈ smoothParts,
          (b.factorization p : ℝ) / (b : ℝ)) ≤
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (b.factorization p : ℝ) / (b : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmoothSubset
      (fun _b _hbIcc _hbSmooth ↦ by positivity)
  have hunweightedSubset :
      (∑ b ∈ smoothParts, (b.factorization p : ℝ)) ≤
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (b.factorization p : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsmoothSubset
      (fun _b _hbIcc _hbSmooth ↦ Nat.cast_nonneg _)
  have hweightedFull :=
    weightedFactorizationSum_le_two_mul_one_add_log_div_prime
      (p := p) (B := 2 * X) hpPrime hBOne
  have hunweightedFull :=
    sum_factorization_Icc_cast_le_two_mul_div_prime
      (p := p) (B := 2 * X) hpPrime
  have hweighted :
      (∑ b ∈ smoothParts,
          (b.factorization p : ℝ) / (b : ℝ)) ≤
        4 * deltaStar * L n / (p : ℝ) := by
    calc
      (∑ b ∈ smoothParts,
          (b.factorization p : ℝ) / (b : ℝ)) ≤
        ∑ b ∈ Finset.Icc 1 (2 * X),
          (b.factorization p : ℝ) / (b : ℝ) := hweightedSubset
      _ ≤ 2 * (1 + Real.log ((2 * X : ℕ) : ℝ)) /
          (p : ℝ) := hweightedFull
      _ ≤ 4 * deltaStar * L n / (p : ℝ) := by
        apply div_le_div_of_nonneg_right _ hpR.le
        have hcutLog' :
            1 + Real.log ((2 * X : ℕ) : ℝ) ≤
              2 * deltaStar * L n := by
          simpa only [X] using hcutLog
        nlinarith
  have hunweighted :
      (∑ b ∈ smoothParts, (b.factorization p : ℝ)) ≤
        4 * (X : ℝ) / (p : ℝ) := by
    calc
      (∑ b ∈ smoothParts, (b.factorization p : ℝ)) ≤
          ∑ b ∈ Finset.Icc 1 (2 * X),
            (b.factorization p : ℝ) := hunweightedSubset
      _ ≤ 2 * ((2 * X : ℕ) : ℝ) / (p : ℝ) :=
        hunweightedFull
      _ = 4 * (X : ℝ) / (p : ℝ) := by push_cast; ring
  have hmainCoefficient : 0 ≤
      (h : ℝ) * paperExceptionalSelbergMainConstant /
        Real.log (Y : ℝ) := by
    exact div_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        paperExceptionalSelbergMainConstant_pos.le)
      hlogYPos.le
  have hrestCoefficient : 0 ≤
      paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
        Real.log (Y : ℝ) ^ 2 := by
    exact div_nonneg
      (mul_nonneg paperExceptionalSelbergRemainderConstant_pos.le
        (by positivity))
      (sq_nonneg _)
  calc
    (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
        ℝ) ≤
      ∑ b ∈ smoothParts,
        (b.factorization p : ℝ) *
          ((paperExceptionalSmoothFiber n h deltaStar b).card : ℝ) := hcharge
    _ ≤ ∑ b ∈ smoothParts,
        (((h : ℝ) * paperExceptionalSelbergMainConstant /
            Real.log (Y : ℝ)) *
            ((b.factorization p : ℝ) / (b : ℝ)) +
          (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
            Real.log (Y : ℝ) ^ 2) *
            (b.factorization p : ℝ)) :=
      Finset.sum_le_sum hpointwise
    _ = ((h : ℝ) * paperExceptionalSelbergMainConstant /
          Real.log (Y : ℝ)) *
          (∑ b ∈ smoothParts,
            (b.factorization p : ℝ) / (b : ℝ)) +
        (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2) *
          (∑ b ∈ smoothParts, (b.factorization p : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ ((h : ℝ) * paperExceptionalSelbergMainConstant /
          Real.log (Y : ℝ)) *
          (4 * deltaStar * L n / (p : ℝ)) +
        (paperExceptionalSelbergRemainderConstant * (Y : ℝ) ^ 4 /
          Real.log (Y : ℝ) ^ 2) *
          (4 * (X : ℝ) / (p : ℝ)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted hmainCoefficient)
        (mul_le_mul_of_nonneg_left hunweighted hrestCoefficient)
    _ = paperExceptionalFiniteChargeMajorant c deltaStar n p := by
      unfold paperExceptionalFiniteChargeMajorant
      simp only [h, X, Y, paperExceptionalSelbergMainConstant]
      ring

/-- Canonical paper-facing low-prime charge package.  The error coefficient
tends to zero under `deltaStar<1/18`, and the displayed valuation inequality
is simultaneous for every realized bank and every prime `p≤yNat n`. -/
theorem paperFixedExceptionalCharge_asymptoticPackage
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    Tendsto (paperExceptionalChargeEpsilon deltaStar) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n))) (p : ℕ),
          p.Prime → p ≤ yNat n →
          (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
              ℝ) ≤
            paperExceptionalChargeConstant c *
                (deltaStar / paperExceptionalTheta) *
                secondOrderScale n / (p : ℝ) +
              paperExceptionalChargeEpsilon deltaStar n *
                secondOrderScale n / ((p : ℝ) * L n) := by
  refine ⟨paperExceptionalChargeEpsilon_tendsto_zero
    hdelta.le hdeltaUpper, ?_⟩
  filter_upwards
    [eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
      hc hdelta,
      eventually_paperExceptionalFiniteChargeMajorant_le hc hdelta]
      with n hfinite hmajorant
  intro R p hpPrime hpLow
  exact (hfinite R p hpPrime hpLow).trans (hmajorant p hpPrime.pos)

/-- For a low prime above the paper's literal real cutoff
`2*n^deltaStar`, the actual product of all fixed exceptional factors has
exactly zero valuation.  This conclusion is independent of the Selberg
estimate. -/
theorem BankPaperRealization.paperFixedExceptionalFactors_prod_factorization_eq_zero_of_realCutoff
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (hn : 1 ≤ n) (hh : h ≤ n) (_hp : p.Prime)
    (hpLow : p ≤ yNat n)
    (hpCut : 2 * (n : ℝ) ^ deltaStar < (p : ℝ)) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
      0 := by
  have hfactorization :
      ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
        ∑ a ∈ R.paperFixedExceptionalFactors deltaStar,
          a.factorization p :=
    Nat.factorization_prod_apply (fun a ha ↦ by
      have htail := R.paperFixedExceptionalFactors_subset_tail
        deltaStar ha
      exact (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1).ne')
  rw [hfactorization]
  apply Finset.sum_eq_zero
  intro a ha
  have haExceptional : a ∈ paperExceptionalUpperFactors n h deltaStar :=
    (Finset.mem_sdiff.mp ha).1
  have haBounds := mem_paperExceptionalUpperFactors.mp haExceptional
  have haPos : 0 < a := by
    have hinterval : 2 * n < a := by
      have hintervalData : 2 * n < a ∧ a ≤ 2 * n + h := by
        simpa only [roughUpperBlock, Finset.mem_Ioc] using haBounds.1
      exact hintervalData.1
    omega
  have hsmoothPos : 0 < completeSmoothPart (yNat n) a :=
    completeSmoothPart_pos haPos
  have hsmoothLtReal :
      (completeSmoothPart (yNat n) a : ℝ) < (p : ℝ) :=
    (completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
      hdeltaNonneg hn hh haExceptional).trans hpCut
  have hsmoothLt : completeSmoothPart (yNat n) a < p := by
    exact_mod_cast hsmoothLtReal
  have hsmoothZero :
      (completeSmoothPart (yNat n) a).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpLe : p ≤ completeSmoothPart (yNat n) a :=
      Nat.le_of_dvd hsmoothPos hpDvd
    omega
  have hsmoothEq := completeSmoothPart_factorization_apply
    (yNat n) a p
  rw [if_pos hpLow] at hsmoothEq
  exact hsmoothEq.symm.trans hsmoothZero

/-- Safe integral-cutoff corollary of the literal real zero theorem. -/
theorem BankPaperRealization.paperFixedExceptionalFactors_prod_factorization_eq_zero
    {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (hn : 1 ≤ n) (hh : h ≤ n) (hp : p.Prime)
    (hpLow : p ≤ yNat n)
    (hpCut : 2 * tangentPaperExceptionalCutoff deltaStar n < p) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
      0 := by
  apply R.paperFixedExceptionalFactors_prod_factorization_eq_zero_of_realCutoff
    hdeltaNonneg hn hh hp hpLow
  have hcut := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hpCutReal :
      2 * (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
        (p : ℝ) := by
    exact_mod_cast hpCut
  exact (mul_le_mul_of_nonneg_left hcut (by norm_num)).trans_lt hpCutReal

/-- Canonical eventual form of the exact literal real support cutoff. -/
theorem eventually_paperFixedExceptionalFactors_prod_factorization_eq_zero_of_realCutoff
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        2 * (n : ℝ) ^ deltaStar < (p : ℝ) →
        ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
          0 := by
  filter_upwards [eventually_ge_atTop 1, eventually_upperTailLength_le hc]
    with n hn htail
  intro R p hpPrime hpLow hpCut
  exact R.paperFixedExceptionalFactors_prod_factorization_eq_zero_of_realCutoff
    hdelta.le hn htail hpPrime hpLow hpCut

/-- Canonical eventual safe integral-cutoff corollary. -/
theorem eventually_paperFixedExceptionalFactors_prod_factorization_eq_zero
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        2 * tangentPaperExceptionalCutoff deltaStar n < p →
        ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
          0 := by
  filter_upwards [eventually_ge_atTop 1, eventually_upperTailLength_le hc]
    with n hn htail
  intro R p hpPrime hpLow hpCut
  exact R.paperFixedExceptionalFactors_prod_factorization_eq_zero
    hdelta.le hn htail hpPrime hpLow hpCut

end

end Erdos390.WholePaper
