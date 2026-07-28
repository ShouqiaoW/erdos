import Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual
import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure

/-!
# Paper-rate closure for the raw nonsmooth row correction

The signed residual ledger isolates a uniform bound for the literal raw
row-correction density.  That bound is not an additional analytic input.
The sharp row theorem gives a numerator

`O_W((n / label) / L^2 + 1)`,

while the raw broad-pool theorem gives a denominator bounded below by a
fixed positive multiple of `n / label`.  On active nonexceptional rows the
same real cutoff in the definition of the row implies, uniformly,
`L^2 <= n / label`; hence the endpoint `+1` is absorbed.

This file records that conversion and then invokes the global valuation
census already proved in `BankPaperCanonicalSignedGuardResidual`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- A fixed constant paying the sharp numerator and the reciprocal of the
linear raw broad-pool density.  The factor `24` is chosen so that dividing
by `4 L^2` leaves the pointwise density bound `6 C/(d L^2)`. -/
def roughCanonicalUniformRawRowCorrectionDensityConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  24 * roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta /
    roughCanonicalRawBroadPoolDensity W

theorem roughCanonicalUniformRawRowCorrectionDensityConstant_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalUniformRawRowCorrectionDensityConstant
      W K0 c beta := by
  unfold roughCanonicalUniformRawRowCorrectionDensityConstant
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (roughCanonicalSharpUnifiedRowScaleConstant_nonneg
        W K0 (beta := beta) hc))
    (roughCanonicalRawBroadPoolDensity_pos W).le

private theorem rawRowCorrectionRate_L_sq_div_rpow_tendsto_zero
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => L n ^ 2 / (n : Real) ^ deltaStar)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real =>
        Real.log x ^ (2 : Real) / x ^ deltaStar)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real) hdelta).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : Nat =>
      Real.log (n : Real) ^ (2 : Real) / (n : Real) ^ deltaStar)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

private theorem rawRowCorrectionRate_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- The literal balanced raw correction density has the strict
`constant/(4 L^2)` scale, eventually and uniformly over every attained
active nonexceptional label. -/
theorem eventually_roughCanonicalUniformRawRowCorrectionDensityBound
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalUniformRawRowCorrectionDensityBound
        W n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        (roughCanonicalUniformRawRowCorrectionDensityConstant
          W K0 c beta / (4 * L n ^ 2)) := by
  let C := roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta
  let d := roughCanonicalRawBroadPoolDensity W
  have hC : 0 <= C := by
    dsimp only [C]
    exact roughCanonicalSharpUnifiedRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hd : 0 < d := by
    dsimp only [d]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have hraw :=
    Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
      W K0 (beta := beta) hc hdelta
  have hpool :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W (K0 + 1) hc hdelta
  have hratio : ∀ᶠ n : Nat in atTop,
      L n ^ 2 / (n : Real) ^ deltaStar < 1 / 4 :=
    (rawRowCorrectionRate_L_sq_div_rpow_tendsto_zero hdelta).eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 4))
  have hpower : ∀ᶠ n : Nat in atTop,
      (4 : Real) <= (n : Real) ^ deltaStar :=
    (rawRowCorrectionRate_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop 4)
  filter_upwards [eventually_gt_atTop 1, hraw, hpool, hratio, hpower]
      with n hn hrawN hpoolN hratioN hpowerN
  unfold RoughCanonicalUniformRawRowCorrectionDensityBound
  intro label hlabel
  have hlabelParts :=
    mem_roughCanonicalActiveRawCorrectionLabels.mp hlabel
  let row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
    ⟨label, hlabelParts.1⟩
  have hlabelData : IsCompleteRoughLabel (yNat n) label := by
    simpa only [row] using
      (isCompleteRoughLabel_of_canonicalCompleteRoughRow row)
  have hlabelPos : 0 < label := hlabelData.1
  have hlabelReal : (0 : Real) < (label : Real) := by
    exact_mod_cast hlabelPos
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast (show 0 < n by omega)
  have hpowPos : (0 : Real) < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hL : 0 < L n := L_pos hn
  let X : Real := ((n / label : Nat) : Real)
  have hquotient :
      (n : Real) ^ deltaStar / 2 <=
        (n : Real) / (label : Real) := by
    apply (div_le_iff₀ (by norm_num : (0 : Real) < 2)).2
    calc
      (n : Real) ^ deltaStar <=
          2 * (n : Real) / (label : Real) := hlabelParts.2.2
      _ = (n : Real) / (label : Real) * 2 := by ring
  have hnatUpper :
      (n : Real) / (label : Real) < X + 1 := by
    dsimp only [X]
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
      (Nat.lt_succ_self (n / label))
    exact_mod_cast hnat
  have hlogSmall :
      L n ^ 2 < (n : Real) ^ deltaStar / 4 := by
    have hcross := (div_lt_iff₀ hpowPos).mp hratioN
    nlinarith
  have hpowerAbsorb :
      2 * (L n ^ 2 + 1) <= (n : Real) ^ deltaStar := by
    nlinarith
  have hX : L n ^ 2 <= X := by
    have hstrict : L n ^ 2 < X := by
      nlinarith
    exact hstrict.le
  have hXPos : 0 < X := (sq_pos_of_pos hL).trans_le hX
  have hpoolLower :
      d * X <=
        ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
          (K0 + 1) (yNat n) label).card : Real) := by
    simpa only [d, X] using hpoolN label hlabelData hlabelParts.2
  have hpoolPos :
      (0 : Real) <
        ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
          (K0 + 1) (yNat n) label).card : Real) :=
    (mul_pos hd hXPos).trans_le hpoolLower
  have hone : (1 : Real) <= X / L n ^ 2 := by
    exact (le_div_iff₀ (sq_pos_of_pos hL)).2 (by simpa using hX)
  have hrawRow :
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) row| <=
        3 * (C * (X / L n ^ 2 + 1)) := by
    simpa only [C, X, row] using hrawN row hlabelParts.2
  have hquota :
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) row| <=
        6 * C * X / L n ^ 2 := by
    calc
      _ <= 3 * (C * (X / L n ^ 2 + 1)) := hrawRow
      _ <= 3 * (C * (X / L n ^ 2 + X / L n ^ 2)) := by
        gcongr
      _ = 6 * C * X / L n ^ 2 := by ring
  have hcoefficient :
      0 <= (24 * C / d) / (4 * L n ^ 2) := by positivity
  have hdensity :
      |roughCanonicalRawCorrectionDensityAtLabel
          W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) label| <=
        (24 * C / d) / (4 * L n ^ 2) := by
    have hpoolNonneg :
        (0 : Real) <=
          ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
            (K0 + 1) (yNat n) label).card : Real) :=
      Nat.cast_nonneg _
    rw [roughCanonicalRawCorrectionDensityAtLabel_eq_quotaError_div hlabel,
      abs_div, abs_of_nonneg hpoolNonneg]
    apply (div_le_iff₀ hpoolPos).2
    calc
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n)
          ⟨label, hlabelParts.1⟩| <=
          6 * C * X / L n ^ 2 := by
        simpa only [row] using hquota
      _ = ((24 * C / d) / (4 * L n ^ 2)) * (d * X) := by
        field_simp [hd.ne', hL.ne']; ring
      _ <= ((24 * C / d) / (4 * L n ^ 2)) *
          ((roughCanonicalBroadCorrectionPool W n
            (upperTailLength c n) (K0 + 1) (yNat n) label).card : Real) :=
        mul_le_mul_of_nonneg_left hpoolLower hcoefficient
  simpa only [
    roughCanonicalUniformRawRowCorrectionDensityConstant, C, d] using
      hdensity

/-- The pointwise closure above and the already proved valuation census give
the complete aggregate raw correction at the strict paper rate, uniformly
over all medium primes. -/
theorem eventually_roughCanonicalAggregateRawRowCorrectionBound_strictScale
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop, forall p : Nat,
      p.Prime ->
      RoughCanonicalAggregateRawRowCorrectionBound
        W n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) p
        (roughCanonicalUniformRawRowCorrectionDensityConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n)) := by
  have hdensity :=
    eventually_roughCanonicalUniformRawRowCorrectionDensityBound
      W K0 (beta := beta) hc hdelta
  have hconstant :=
    roughCanonicalUniformRawRowCorrectionDensityConstant_nonneg
      W K0 (beta := beta) hc
  filter_upwards [eventually_gt_atTop 1, hdensity]
      with n hn hdensityN
  intro p hp
  exact
    roughCanonicalAggregateRawRowCorrectionBound_strictScale_of_uniformDensity
      hn hp hconstant hdensityN

end BankPaperRealization

end

end Erdos390.WholePaper
