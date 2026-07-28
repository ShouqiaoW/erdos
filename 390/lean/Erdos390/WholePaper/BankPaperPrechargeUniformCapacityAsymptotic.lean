import Erdos390.WholePaper.BankPaperPrechargeAsymptotic

/-!
# Uniform precharge capacity at every moving small prime

The summed small-prime precharge cost is negligible, but the moving-prime
allocation needs two uniform consequences.  First, the per-prime cost must
fit below an arbitrarily small multiple of `secondOrderScale / (p-1)` for
every prime `p ≤ yNat`.  Second, after adjoining the logarithmic error from
the lower factorial-valuation bound, the total natural cost must fit inside
the actual upper-tail length.

Both statements are derived from the cubic-log majorant proved in
`BankPaperPrechargeAsymptotic`; no new prime-counting input is used here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Uniform per-prime reserve -/

/-- Eventually, the uniform precharge valuation at every moving small prime
fits below any prescribed positive fraction of its natural
`secondOrderScale / (p-1)` capacity. -/
theorem eventually_bankPaperPrecharge_perPrimeCapacity
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ,
      p.Prime → p ≤ yNat n →
        (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) ≤
          delta / (((p - 1 : ℕ) : ℝ)) * secondOrderScale n := by
  have hsmall :=
    bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero.eventually
      (eventually_lt_nhds hdelta)
  filter_upwards [hsmall, eventually_secondOrderScale_pos]
      with n hnormalized hscale
  intro p hpPrime hpY
  have hpredNat : p - 1 ≤ yNat n := (Nat.sub_le p 1).trans hpY
  have hpred : (((p - 1 : ℕ) : ℝ)) ≤ (yNat n : ℝ) := by
    exact_mod_cast hpredNat
  have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
  have hpredPos : 0 < (((p - 1 : ℕ) : ℝ)) := by
    exact_mod_cast hpredPosNat
  have hmajorant :
      (yNat n : ℝ) *
          (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) ≤
        delta * secondOrderScale n := by
    have hscaled := (div_lt_iff₀ hscale).mp hnormalized
    simpa only [bankPaperPrechargeSmallPrimeCostMajorant,
      Nat.cast_mul, mul_assoc] using hscaled.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpredPos).2
  calc
    (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) *
          (((p - 1 : ℕ) : ℝ)) =
        (((p - 1 : ℕ) : ℝ)) *
          (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) :=
      mul_comm _ _
    _ ≤ (yNat n : ℝ) *
          (((bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hpred (by positivity)
    _ ≤ delta * secondOrderScale n := hmajorant

/-! ## Combined moving-prime capacity cost -/

/-- Natural cubic-log term which absorbs the moving logarithmic remainder. -/
def bankPaperPrechargeCubicLogMajorant (n : ℕ) : ℕ :=
  yNat n ^ 3 * Nat.log 2 (3 * n)

/-- The natural cubic-log term has vanishing normalized cost. -/
theorem bankPaperPrechargeCubicLogMajorant_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeCubicLogMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  simpa only [bankPaperPrechargeCubicLogMajorant,
    Nat.cast_mul, Nat.cast_pow] using
      (yNat_cubed_mul_natLog_isLittleO_secondOrderScale).tendsto_div_nhds_zero

/-- A realization-independent majorant for the precharge cost together with
the lower factorial-valuation logarithmic error. -/
def bankPaperPrechargeUniformCapacityMajorant (n : ℕ) : ℕ :=
  bankPaperPrechargeSmallPrimeCostMajorant n +
    2 * bankPaperPrechargeCubicLogMajorant n

/-- The combined universal capacity majorant is negligible. -/
theorem bankPaperPrechargeUniformCapacityMajorant_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeUniformCapacityMajorant n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hcubicTwo : Tendsto
      (fun n : ℕ ↦
        2 * ((bankPaperPrechargeCubicLogMajorant n : ℝ) /
          secondOrderScale n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      bankPaperPrechargeCubicLogMajorant_normalized_tendsto_zero.const_mul
        (2 : ℝ)
  have hsum : Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeSmallPrimeCostMajorant n : ℝ) /
            secondOrderScale n +
          2 * ((bankPaperPrechargeCubicLogMajorant n : ℝ) /
            secondOrderScale n))
      atTop (nhds 0) := by
    simpa only [zero_add] using
      bankPaperPrechargeSmallPrimeCostMajorant_normalized_tendsto_zero.add
        hcubicTwo
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [bankPaperPrechargeUniformCapacityMajorant,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring

/-- The literal cost appearing in the moving-prime lower-cross inequality. -/
def bankPaperPrechargeUniformCapacityCost (c : ℝ) (n : ℕ) : ℕ :=
  yNat n *
    (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
      Nat.log2 (upperTailLength c n) + 1)

/-- Once the upper tail is at most `n`, the logarithmic remainder and its
extra `+1` are absorbed by twice the cubic-log term. -/
theorem eventually_bankPaperPrechargeUniformCapacityCost_le_majorant
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      bankPaperPrechargeUniformCapacityCost c n ≤
        bankPaperPrechargeUniformCapacityMajorant n := by
  filter_upwards [eventually_upperTailLength_le hc,
      eventually_ge_atTop 1] with n htail hn
  have htailThree : upperTailLength c n ≤ 3 * n := by omega
  have hlogTail : Nat.log2 (upperTailLength c n) ≤
      Nat.log 2 (3 * n) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_mono_right htailThree
  have hlogOne : 1 ≤ Nat.log 2 (3 * n) := by
    calc
      1 = Nat.log 2 2 := by norm_num
      _ ≤ Nat.log 2 (3 * n) := Nat.log_mono_right (by omega)
  have hlogAdd : Nat.log2 (upperTailLength c n) + 1 ≤
      2 * Nat.log 2 (3 * n) := by omega
  have hyCube : yNat n ≤ yNat n ^ 3 :=
    Nat.le_pow (by omega : 0 < 3)
  have hextra :
      yNat n * (Nat.log2 (upperTailLength c n) + 1) ≤
        2 * bankPaperPrechargeCubicLogMajorant n := by
    calc
      yNat n * (Nat.log2 (upperTailLength c n) + 1) ≤
          yNat n * (2 * Nat.log 2 (3 * n)) :=
        Nat.mul_le_mul_left _ hlogAdd
      _ ≤ yNat n ^ 3 * (2 * Nat.log 2 (3 * n)) :=
        Nat.mul_le_mul_right _ hyCube
      _ = 2 * bankPaperPrechargeCubicLogMajorant n := by
        rw [bankPaperPrechargeCubicLogMajorant]
        ring
  rw [bankPaperPrechargeUniformCapacityCost,
    bankPaperPrechargeUniformCapacityMajorant]
  calc
    yNat n *
        (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
          Nat.log2 (upperTailLength c n) + 1) =
        bankPaperPrechargeSmallPrimeCostMajorant n +
          yNat n * (Nat.log2 (upperTailLength c n) + 1) := by
      rw [bankPaperPrechargeSmallPrimeCostMajorant]
      ring
    _ ≤ bankPaperPrechargeSmallPrimeCostMajorant n +
          2 * bankPaperPrechargeCubicLogMajorant n :=
      Nat.add_le_add_left hextra _

/-- The full natural cost used by the moving-prime capacity argument has
vanishing normalized size. -/
theorem bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (bankPaperPrechargeUniformCapacityCost c n : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hbound :=
    eventually_bankPaperPrechargeUniformCapacityCost_le_majorant hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    bankPaperPrechargeUniformCapacityMajorant_normalized_tendsto_zero
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    exact div_nonneg (by positivity) hscale.le
  · filter_upwards [hbound, eventually_secondOrderScale_pos]
      with n hcost hscale
    exact div_le_div_of_nonneg_right (by exact_mod_cast hcost) hscale.le

/-- Eventually the entire precharge valuation cost plus the logarithmic
lower-cross error fits inside the actual upper-tail length. -/
theorem eventually_bankPaperPrecharge_uniformMovingPrimeCapacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      yNat n *
          (bankPaperAnchorMarkerBudget n * Nat.log 2 (3 * n) +
            Nat.log2 (upperTailLength c n) + 1) ≤
        upperTailLength c n := by
  have hcostSmall :=
    (bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero hc).eventually
      (eventually_lt_nhds (half_pos hc))
  have htailLarge :=
    (upperTailLength_normalized_tendsto hc).eventually
      (eventually_gt_nhds (half_lt_self hc))
  filter_upwards [hcostSmall, htailLarge,
      eventually_secondOrderScale_pos] with n hcost htail hscale
  have hratio :
      (bankPaperPrechargeUniformCapacityCost c n : ℝ) /
          secondOrderScale n <
        (upperTailLength c n : ℝ) / secondOrderScale n :=
    hcost.trans htail
  have hcast : (bankPaperPrechargeUniformCapacityCost c n : ℝ) ≤
      (upperTailLength c n : ℝ) :=
    ((div_lt_div_iff_of_pos_right hscale).mp hratio).le
  simpa only [bankPaperPrechargeUniformCapacityCost] using
    (by exact_mod_cast hcast :
      bankPaperPrechargeUniformCapacityCost c n ≤ upperTailLength c n)

end

end Erdos390.WholePaper
