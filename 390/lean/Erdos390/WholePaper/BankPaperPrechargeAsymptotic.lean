import Erdos390.WholePaper.BankPaperPrecharge
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Negligible small-prime cost of the precharged bank

The precharged base product has valuation at most the global marker budget
times one binary logarithm at each prime.  Summing over all primes at most
`yNat` therefore costs at most

`yNat * bankPaperAnchorMarkerBudget * log₂ (3n)`.

This file proves that literal numerical majorant is little-o of the central
second-order scale.  The analytic core is the identity

`y³ log(n) / (n / log(n)) = log(n)² / n^(1/3)`,

followed by the standard fact that every fixed logarithmic power is
little-o of every positive power.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The cubic endpoint ratio -/

/-- The normalized real model underlying the summed small-prime cost. -/
def bankPaperPrechargeCubicNormalizedCost (n : ℕ) : ℝ :=
  y n ^ 3 * L n / secondOrderScale n

/-- The cubic model reduces exactly to `log(n)² / n^(1/3)`. -/
theorem bankPaperPrechargeCubicNormalizedCost_eq
    {n : ℕ} (hn : 1 < n) :
    bankPaperPrechargeCubicNormalizedCost n =
      L n ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hyPow : y n ^ 3 = (n : ℝ) ^ (2 / 3 : ℝ) := by
    calc
      y n ^ 3 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 := rfl
      _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (3 : ℕ)) :=
        (Real.rpow_mul_natCast (Nat.cast_nonneg n)
          (2 / 9 : ℝ) 3).symm
      _ = (n : ℝ) ^ (2 / 3 : ℝ) := by norm_num
  have hpow :
      (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) =
        (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [bankPaperPrechargeCubicNormalizedCost, secondOrderScale,
    show Real.log (n : ℝ) = L n by rfl, hyPow]
  field_simp [hnR.ne', hL.ne',
    (Real.rpow_pos_of_pos hnR (1 / 3 : ℝ)).ne']
  nlinarith

/-- The cubic normalized model tends to zero. -/
theorem bankPaperPrechargeCubicNormalizedCost_tendsto_zero :
    Tendsto bankPaperPrechargeCubicNormalizedCost atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦
        Real.log x ^ (2 : ℝ) / x ^ (1 / 3 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 3)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ ↦
        Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ))
      atTop (nhds 0) := by
    simpa [Real.rpow_natCast] using
      hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simpa [L] using
    (bankPaperPrechargeCubicNormalizedCost_eq hn).symm

/-- Equivalently, `y³ log n` is little-o of the second-order scale. -/
theorem y_cubed_mul_L_isLittleO_secondOrderScale :
    (fun n : ℕ ↦ y n ^ 3 * L n) =o[atTop] secondOrderScale := by
  have hzero : ∀ᶠ n : ℕ in atTop,
      secondOrderScale n = 0 → y n ^ 3 * L n = 0 := by
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hscaleZero
    exact (hscale.ne' hscaleZero).elim
  apply (isLittleO_iff_tendsto' hzero).mpr
  simpa only [bankPaperPrechargeCubicNormalizedCost] using
    bankPaperPrechargeCubicNormalizedCost_tendsto_zero

/-! ## Integral cutoffs and the binary logarithm -/

/-- The integral cutoff is bounded by its real `n^(2/9)` model. -/
theorem bankPaperPrecharge_yNat_isBigO_y :
    (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop] y := by
  apply IsBigO.of_bound 1
  filter_upwards [] with n
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ yNat n),
    Real.norm_eq_abs, abs_of_nonneg hyNonneg, one_mul]
  exact hyFloor

/-- The literal binary logarithm in the valuation bound is `O(log n)`. -/
theorem natLog_two_three_mul_isBigO_L :
    (fun n : ℕ ↦ (Nat.log 2 (3 * n) : ℝ)) =O[atTop] L := by
  apply IsBigO.of_bound (2 / Real.log 2)
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogn : 0 ≤ L n :=
    (L_pos (show 1 < n by omega)).le
  have hlogThree : Real.log 3 ≤ L n := by
    rw [L]
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogMul : Real.log (3 * (n : ℝ)) =
      Real.log 3 + L n := by
    rw [L, Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnPos.ne']
  have hdepth : (Nat.log 2 (3 * n) : ℝ) ≤
      Real.log (3 * (n : ℝ)) / Real.log 2 := by
    simpa only [Nat.log2_eq_log_two, Nat.cast_mul, Nat.cast_ofNat] using
      Real.log2_le_logb (3 * n)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ Nat.log 2 (3 * n)),
    Real.norm_eq_abs, abs_of_nonneg hlogn]
  rw [hlogMul] at hdepth
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (Nat.log 2 (3 * n) : ℝ) ≤
        (Real.log 3 + L n) / Real.log 2 := hdepth
    _ ≤ (2 / Real.log 2) * L n := by
      apply (div_le_iff₀ hlogTwo).2
      calc
        Real.log 3 + L n ≤ 2 * L n := by linarith
        _ = (2 / Real.log 2) * L n * Real.log 2 := by
          field_simp

/-- The integral cubic-log model is little-o of the central scale. -/
theorem yNat_cubed_mul_natLog_isLittleO_secondOrderScale :
    (fun n : ℕ ↦
      (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ))
      =o[atTop] secondOrderScale := by
  have hraw :=
    (((bankPaperPrecharge_yNat_isBigO_y.mul
        bankPaperPrecharge_yNat_isBigO_y).mul
      bankPaperPrecharge_yNat_isBigO_y).mul
        natLog_two_three_mul_isBigO_L)
  have hcubic :
      (fun n : ℕ ↦
        (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ))
        =O[atTop] (fun n : ℕ ↦ y n ^ 3 * L n) := by
    apply hraw.congr'
    · exact Eventually.of_forall fun n ↦ by ring
    · exact Eventually.of_forall fun n ↦ by ring
  exact hcubic.trans_isLittleO
    y_cubed_mul_L_isLittleO_secondOrderScale

/-! ## The concrete precharge cost -/

/-- Real-valued form of the literal small-prime cost majorant is little-o
of the second-order scale. -/
theorem bankPaperPrechargeSmallPrimeCost_isLittleO_secondOrderScale :
    (fun n : ℕ ↦
      (yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
        (Nat.log 2 (3 * n) : ℝ)) =o[atTop] secondOrderScale := by
  have hraw :=
    ((isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop).mul
      bankPaperAnchorMarkerBudget_isBigO_yNat_sq).mul
        (isBigO_refl
          (fun n : ℕ ↦ (Nat.log 2 (3 * n) : ℝ)) atTop)
  have hcost :
      (fun n : ℕ ↦
        (yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
          (Nat.log 2 (3 * n) : ℝ)) =O[atTop]
        (fun n : ℕ ↦
          (yNat n : ℝ) ^ 3 * (Nat.log 2 (3 * n) : ℝ)) := by
    apply hraw.congr'
    · exact Eventually.of_forall fun n ↦ by ring
    · exact Eventually.of_forall fun n ↦ by ring
  exact hcost.trans_isLittleO
    yNat_cubed_mul_natLog_isLittleO_secondOrderScale

/-- The concrete normalized real cost tends to zero. -/
theorem bankPaperPrechargeSmallPrimeCost_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        ((yNat n : ℝ) * (bankPaperAnchorMarkerBudget n : ℝ) *
          (Nat.log 2 (3 * n) : ℝ)) / secondOrderScale n)
      atTop (nhds 0) :=
  (bankPaperPrechargeSmallPrimeCost_isLittleO_secondOrderScale).tendsto_div_nhds_zero

/-- Natural-valued version of the same universal majorant. -/
def bankPaperPrechargeSmallPrimeCostMajorant (n : ℕ) : ℕ :=
  yNat n * bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n)

/-- The cast of the literal natural majorant has vanishing normalized cost. -/
theorem bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeSmallPrimeCostMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  simpa only [bankPaperPrechargeSmallPrimeCostMajorant, Nat.cast_mul] using
    bankPaperPrechargeSmallPrimeCost_normalized_tendsto_zero

/-- Any nonnegative natural cost eventually dominated by the displayed
majorant is negligible on the second-order scale. -/
theorem normalized_tendsto_zero_of_eventually_le_prechargeSmallPrimeCost
    (cost : ℕ → ℕ)
    (hcost : ∀ᶠ n : ℕ in atTop,
      cost n ≤ bankPaperPrechargeSmallPrimeCostMajorant n) :
    Tendsto
      (fun n : ℕ ↦ (cost n : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    exact div_nonneg (by positivity) hscale.le
  · filter_upwards [hcost, eventually_secondOrderScale_pos]
      with n hbound hscale
    exact div_le_div_of_nonneg_right (by exact_mod_cast hbound) hscale.le

namespace BankPaperRealization

/-- Total base-product valuation over all primes at most `yNat`. -/
def prechargeSmallPrimeValuationCost
    {n M : ℕ} (R : BankPaperRealization n M) : ℕ :=
  ∑ p ∈ primesUpTo (yNat n),
    (R.prechargeBaseStateProduct).factorization p

/-- The actual total small-prime valuation is bounded by the number of
possible primes times the uniform per-prime cost. -/
theorem prechargeSmallPrimeValuationCost_le
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeSmallPrimeValuationCost ≤
      yNat n *
        (bankPaperAnchorMarkerBudget n * Nat.log 2 M) := by
  have hprimeSubset : primesUpTo (yNat n) ⊆ Finset.Ioc 0 (yNat n) := by
    intro p hp
    have hpData := mem_primesUpTo.mp hp
    exact Finset.mem_Ioc.mpr ⟨hpData.1.pos, hpData.2⟩
  have hprimeCard : (primesUpTo (yNat n)).card ≤ yNat n := by
    calc
      (primesUpTo (yNat n)).card ≤
          (Finset.Ioc 0 (yNat n)).card :=
        Finset.card_le_card hprimeSubset
      _ = yNat n := by simp
  rw [prechargeSmallPrimeValuationCost]
  calc
    ∑ p ∈ primesUpTo (yNat n),
        (R.prechargeBaseStateProduct).factorization p ≤
        ∑ _p ∈ primesUpTo (yNat n),
          bankPaperAnchorMarkerBudget n * Nat.log 2 M := by
      apply Finset.sum_le_sum
      intro p hp
      exact R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget
        (mem_primesUpTo.mp hp).1
    _ = (primesUpTo (yNat n)).card *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 M) := by simp
    _ ≤ yNat n *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 M) :=
      Nat.mul_le_mul_right _ hprimeCard

/-- If the realized endpoint is at most `3n`, its actual summed small-prime
valuation is bounded by the universal negligible majorant. -/
theorem prechargeSmallPrimeValuationCost_le_majorant
    {n M : ℕ} (R : BankPaperRealization n M)
    (hM : M ≤ 3 * n) :
    R.prechargeSmallPrimeValuationCost ≤
      bankPaperPrechargeSmallPrimeCostMajorant n := by
  calc
    R.prechargeSmallPrimeValuationCost ≤
        yNat n *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 M) :=
      R.prechargeSmallPrimeValuationCost_le
    _ ≤ yNat n *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n)) := by
      exact Nat.mul_le_mul_left _
        (Nat.mul_le_mul_left _ (Nat.log_mono_right hM))
    _ = bankPaperPrechargeSmallPrimeCostMajorant n := by
      simp [bankPaperPrechargeSmallPrimeCostMajorant, Nat.mul_assoc]

/-- Endpoint-specialized form: a tail of length at most `n` automatically
lies below `3n`. -/
theorem prechargeSmallPrimeValuationCost_le_majorant_at_upperEndpoint
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (hh : h ≤ n) :
    R.prechargeSmallPrimeValuationCost ≤
      bankPaperPrechargeSmallPrimeCostMajorant n := by
  exact R.prechargeSmallPrimeValuationCost_le_majorant
    (upperEndpoint_le_three_mul hh)

end BankPaperRealization

end

end Erdos390.WholePaper
