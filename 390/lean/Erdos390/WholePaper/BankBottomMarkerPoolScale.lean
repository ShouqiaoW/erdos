import Erdos390.WholePaper.BankBottomMarkerPools
import Erdos390.WholePaper.SafeShortIntervalPrimeCounting
import Erdos390.WholePaper.VariablePrimeCounting

/-!
# Prime-counting scales for bottom marker pools

The bottom intervals have length of order `n / log n`, while their prime
cardinality has order `n / log n ^ 2`.  Consequently their cardinality
divided by `secondOrderScale n = n / log n` tends to zero, not to a positive
constant.  This file records that coarse-scale fact and then applies the
audited `theta`-difference squeeze to obtain the positive constants on the
finer scale `secondOrderScale n / log n`.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The scale `N/L = n/(log n)^2` used by the paper for bottom primes. -/
def bankBottomPrimeScale (n : ℕ) : ℝ :=
  SafePrimeCounting.shortIntervalPrimeScale n

private theorem natDiv_endpoint_ratio_tendsto
    {m : ℕ → ℕ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a))
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ ↦ ((m n / d : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a / (d : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / (n : ℝ)) / (d : ℝ))
        atTop (nhds (a / (d : ℝ))) :=
    hm.div_const (d : ℝ)
  have hinv :
      Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hlower :
      Tendsto
        (fun n : ℕ ↦
          ((m n : ℝ) / (n : ℝ)) / (d : ℝ) - 1 / (n : ℝ))
        atTop (nhds (a / (d : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hfloor :
        (m n : ℝ) / (d : ℝ) < ((m n / d : ℕ) : ℝ) + 1 := by
      simpa only [Nat.floor_div_eq_div] using
        (Nat.lt_floor_add_one ((m n : ℝ) / (d : ℝ)))
    have hbase :
        (m n : ℝ) / (d : ℝ) - 1 ≤ ((m n / d : ℕ) : ℝ) := by
      linarith
    calc
      ((m n : ℝ) / (n : ℝ)) / (d : ℝ) - 1 / (n : ℝ) =
          ((m n : ℝ) / (d : ℝ) - 1) / (n : ℝ) := by
            field_simp
      _ ≤ ((m n / d : ℕ) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hbase hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcast :
        ((m n / d : ℕ) : ℝ) ≤ (m n : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    calc
      ((m n / d : ℕ) : ℝ) / (n : ℝ) ≤
          ((m n : ℝ) / (d : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hcast hnR.le
      _ = ((m n : ℝ) / (n : ℝ)) / (d : ℝ) := by
        field_simp

private theorem natCast_self_ratio_tendsto_one :
    Tendsto (fun n : ℕ ↦ (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (div_self (by exact_mod_cast hn.ne')).symm

private theorem two_mul_natCast_ratio_tendsto_two :
    Tendsto (fun n : ℕ ↦ ((2 * n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

private theorem upperScaledEndpoint_ratio_tendsto_two
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperEndpoint n (upperTailLength c n) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  have hsum : Tendsto
      (fun n : ℕ ↦ (2 : ℝ) +
        (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
    simpa only [add_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2)).add
          (upperTailLength_ratio_tendsto_zero hc)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

/-- Common first-order location of the two endpoints of a bottom row. -/
def bankBottomMarkerBase : BankBottomMove → ℝ
  | .fiveToFour => 1 / 3
  | .fourToThree => 2 / 5
  | .threeToTwo => 2 / 3
  | .twoToOne => 1 / 2

theorem bankBottomMarkerBase_pos (move : BankBottomMove) :
    0 < bankBottomMarkerBase move := by
  cases move <;> norm_num [bankBottomMarkerBase]

theorem bankBottomMarkerLower_ratio_tendsto (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦ (bankBottomMarkerLower n move : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase move)) := by
  cases move
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto natCast_self_ratio_tendsto_one 3 (by omega)
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto two_mul_natCast_ratio_tendsto_two 5 (by omega)
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto two_mul_natCast_ratio_tendsto_two 3 (by omega)
  · simpa only [bankBottomMarkerLower, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto natCast_self_ratio_tendsto_one 2 (by omega)

theorem bankBottomMarkerUpper_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomMarkerUpper
          (upperEndpoint n (upperTailLength c n)) move : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase move)) := by
  have hM := upperScaledEndpoint_ratio_tendsto_two hc
  cases move
  · convert natDiv_endpoint_ratio_tendsto hM 6 (by omega) using 1
    norm_num [bankBottomMarkerUpper, bankBottomMarkerBase]
  · simpa only [bankBottomMarkerUpper, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto hM 5 (by omega)
  · simpa only [bankBottomMarkerUpper, bankBottomMarkerBase] using
      natDiv_endpoint_ratio_tendsto hM 3 (by omega)
  · convert natDiv_endpoint_ratio_tendsto hM 4 (by omega) using 1
    norm_num [bankBottomMarkerUpper, bankBottomMarkerBase]

/-- The divisor through which the upper-tail length enters each bottom row. -/
def bankBottomMarkerDenominator : BankBottomMove → ℕ
  | .fiveToFour => 6
  | .fourToThree => 5
  | .threeToTwo => 3
  | .twoToOne => 4

theorem bankBottomMarkerDenominator_pos (move : BankBottomMove) :
    0 < bankBottomMarkerDenominator move := by
  cases move <;> norm_num [bankBottomMarkerDenominator]

/-- Lower endpoint of an oriented half-pool. -/
def bankBottomOrientedMarkerLower (n M : ℕ)
    (pool : BankBottomOrientationPool) : ℕ :=
  match pool.2 with
  | .downward => bankBottomMarkerLower n pool.1
  | .upward => bankBottomOrientationCut n M pool.1

/-- Upper endpoint of an oriented half-pool. -/
def bankBottomOrientedMarkerUpper (n M : ℕ)
    (pool : BankBottomOrientationPool) : ℕ :=
  match pool.2 with
  | .downward => bankBottomOrientationCut n M pool.1
  | .upward => bankBottomMarkerUpper M pool.1

@[simp] theorem bankBottomOrientedMarkerInterval_eq_Ioc
    (n M : ℕ) (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerInterval n M pool =
      Finset.Ioc (bankBottomOrientedMarkerLower n M pool)
        (bankBottomOrientedMarkerUpper n M pool) := by
  rcases pool with ⟨move, orientation⟩
  cases orientation <;>
    rfl

theorem bankBottomOrientedMarkerLower_le_upper
    {n M : ℕ} (hM : 2 * n ≤ M) (pool : BankBottomOrientationPool) :
    bankBottomOrientedMarkerLower n M pool ≤
      bankBottomOrientedMarkerUpper n M pool := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomMarkerLower_le_cut n M move
  · exact bankBottomOrientationCut_le_upper hM move

private theorem natDiv_scale_normalized_tendsto
    {m : ℕ → ℕ} {scale : ℕ → ℝ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / scale n)
      atTop (nhds a))
    (hscale : Tendsto scale atTop atTop)
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ ↦ ((m n / d : ℕ) : ℝ) / scale n)
      atTop (nhds (a / (d : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / scale n) / (d : ℝ))
        atTop (nhds (a / (d : ℝ))) :=
    hm.div_const (d : ℝ)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / scale n)
      atTop (nhds 0) := by
    simpa only [one_div] using hscale.inv_tendsto_atTop
  have hlower : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / scale n) / (d : ℝ) - 1 / scale n)
      atTop (nhds (a / (d : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [hscale.eventually (eventually_gt_atTop 0)] with n hn
    have hfloor :
        (m n : ℝ) / (d : ℝ) < ((m n / d : ℕ) : ℝ) + 1 := by
      simpa only [Nat.floor_div_eq_div] using
        (Nat.lt_floor_add_one ((m n : ℝ) / (d : ℝ)))
    have hbase :
        (m n : ℝ) / (d : ℝ) - 1 ≤ ((m n / d : ℕ) : ℝ) := by
      linarith
    calc
      ((m n : ℝ) / scale n) / (d : ℝ) - 1 / scale n =
          ((m n : ℝ) / (d : ℝ) - 1) / scale n := by
            have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
            field_simp
      _ ≤ ((m n / d : ℕ) : ℝ) / scale n :=
        div_le_div_of_nonneg_right hbase hn.le
  · filter_upwards [hscale.eventually (eventually_gt_atTop 0)] with n hn
    have hcast : ((m n / d : ℕ) : ℝ) ≤ (m n : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    calc
      ((m n / d : ℕ) : ℝ) / scale n ≤
          ((m n : ℝ) / (d : ℝ)) / scale n :=
        div_le_div_of_nonneg_right hcast hn.le
      _ = ((m n : ℝ) / scale n) / (d : ℝ) := by
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp

/-- The full row width differs from the tail length divided by the row
denominator by at most one integer. -/
theorem bankBottomMarkerGap_bounds
    (n h : ℕ) (move : BankBottomMove) :
    h / bankBottomMarkerDenominator move ≤
        bankBottomMarkerUpper (upperEndpoint n h) move -
          bankBottomMarkerLower n move ∧
      bankBottomMarkerUpper (upperEndpoint n h) move -
          bankBottomMarkerLower n move ≤
        h / bankBottomMarkerDenominator move + 1 := by
  cases move <;>
    simp only [bankBottomMarkerDenominator, bankBottomMarkerUpper,
      bankBottomMarkerLower, upperEndpoint] <;>
    omega

/-- Thus an unsplit row has normalized width `c / d` on the
`secondOrderScale` length scale. -/
theorem bankBottomMarkerGap_normalized_tendsto
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move : ℝ) -
            (bankBottomMarkerLower n move : ℝ)) /
          secondOrderScale n)
      atTop (nhds (c / (bankBottomMarkerDenominator move : ℝ))) := by
  have hdiv := natDiv_scale_normalized_tendsto
    (upperTailLength_normalized_tendsto hc)
    secondOrderScale_tendsto_atTop
    (bankBottomMarkerDenominator move)
    (bankBottomMarkerDenominator_pos move)
  have hinv : Tendsto (fun n : ℕ ↦ 1 / secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [one_div] using secondOrderScale_tendsto_atTop.inv_tendsto_atTop
  have hupper : Tendsto
      (fun n : ℕ ↦
        ((upperTailLength c n / bankBottomMarkerDenominator move : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n)
      atTop (nhds (c / (bankBottomMarkerDenominator move : ℝ))) := by
    simpa only [add_zero] using hdiv.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hdiv hupper
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hrow := bankBottomMarkerLower_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) move
    have hbounds := bankBottomMarkerGap_bounds
      n (upperTailLength c n) move
    rw [← Nat.cast_sub hrow]
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast hbounds.1
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hrow := bankBottomMarkerLower_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) move
    have hbounds := bankBottomMarkerGap_bounds
      n (upperTailLength c n) move
    rw [← Nat.cast_sub hrow]
    have hcast :
        (bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move -
            bankBottomMarkerLower n move : ℕ) ≤
          upperTailLength c n / bankBottomMarkerDenominator move + 1 :=
      hbounds.2
    have hdivLe :
        ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move -
            bankBottomMarkerLower n move : ℕ) : ℝ) /
              secondOrderScale n ≤
          (((upperTailLength c n /
              bankBottomMarkerDenominator move : ℕ) : ℝ) + 1) /
            secondOrderScale n := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact_mod_cast hcast
    calc
      ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move -
            bankBottomMarkerLower n move : ℕ) : ℝ) /
          secondOrderScale n ≤
        (((upperTailLength c n /
            bankBottomMarkerDenominator move : ℕ) : ℝ) + 1) /
          secondOrderScale n := hdivLe
      _ = ((upperTailLength c n /
              bankBottomMarkerDenominator move : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n := by ring

/-- The integer midpoint remains at the same first-order linear location as
the two endpoints surrounding it. -/
theorem bankBottomOrientationCut_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomOrientationCut n
          (upperEndpoint n (upperTailLength c n)) move : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase move)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (bankBottomMarkerLower_ratio_tendsto move)
    (bankBottomMarkerUpper_ratio_tendsto hc move)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
    exact_mod_cast bankBottomMarkerLower_le_cut n
      (upperEndpoint n (upperTailLength c n)) move
  · filter_upwards [eventually_gt_atTop 0] with n hn
    apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ n)
    exact_mod_cast bankBottomOrientationCut_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) move

theorem bankBottomOrientedMarkerLower_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomOrientedMarkerLower n
          (upperEndpoint n (upperTailLength c n)) pool : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase pool.1)) := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomMarkerLower_ratio_tendsto move
  · exact bankBottomOrientationCut_ratio_tendsto hc move

theorem bankBottomOrientedMarkerUpper_ratio_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomOrientedMarkerUpper n
          (upperEndpoint n (upperTailLength c n)) pool : ℝ) / (n : ℝ))
      atTop (nhds (bankBottomMarkerBase pool.1)) := by
  rcases pool with ⟨move, orientation⟩
  cases orientation
  · exact bankBottomOrientationCut_ratio_tendsto hc move
  · exact bankBottomMarkerUpper_ratio_tendsto hc move

/-- Both integer midpoint halves lie between `floor(width/2)` and one more
than that number. -/
theorem bankBottomOrientedMarkerGap_bounds
    {n M : ℕ} (hM : 2 * n ≤ M) (pool : BankBottomOrientationPool) :
    (bankBottomMarkerUpper M pool.1 -
        bankBottomMarkerLower n pool.1) / 2 ≤
      bankBottomOrientedMarkerUpper n M pool -
        bankBottomOrientedMarkerLower n M pool ∧
    bankBottomOrientedMarkerUpper n M pool -
        bankBottomOrientedMarkerLower n M pool ≤
      (bankBottomMarkerUpper M pool.1 -
        bankBottomMarkerLower n pool.1) / 2 + 1 := by
  rcases pool with ⟨move, orientation⟩
  have hrow := bankBottomMarkerLower_le_upper hM move
  cases orientation <;>
    simp only [bankBottomOrientedMarkerLower,
      bankBottomOrientedMarkerUpper, bankBottomOrientationCut] <;>
    omega

/-- Limiting supply constant for either orientation of a bottom row. -/
def bankBottomOrientedPrimeConstant
    (c : ℝ) (pool : BankBottomOrientationPool) : ℝ :=
  c / (2 * (bankBottomMarkerDenominator pool.1 : ℝ))

theorem bankBottomOrientedPrimeConstant_pos
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    0 < bankBottomOrientedPrimeConstant c pool := by
  unfold bankBottomOrientedPrimeConstant
  exact div_pos hc (mul_pos (by norm_num)
    (by exact_mod_cast bankBottomMarkerDenominator_pos pool.1))

/-- Each fixed midpoint orientation receives exactly half the row-width
constant on the `secondOrderScale` length scale. -/
theorem bankBottomOrientedMarkerGap_normalized_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool : ℝ) -
            (bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℝ)) /
          secondOrderScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
  have hrow := bankBottomMarkerGap_normalized_tendsto hc pool.1
  have hrowNat : Tendsto
      (fun n : ℕ ↦
        ((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1 : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds (c / (bankBottomMarkerDenominator pool.1 : ℝ))) := by
    apply hrow.congr'
    exact Eventually.of_forall fun n ↦ by
      dsimp only
      rw [Nat.cast_sub (bankBottomMarkerLower_le_upper
        (two_mul_le_upperEndpoint n (upperTailLength c n)) pool.1)]
  have hhalf0 := natDiv_scale_normalized_tendsto hrowNat
    secondOrderScale_tendsto_atTop 2 (by omega)
  have hhalf : Tendsto
      (fun n : ℕ ↦
        (((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
    simpa only [bankBottomOrientedPrimeConstant, div_div, Nat.cast_ofNat,
      mul_comm] using hhalf0
  have hinv : Tendsto (fun n : ℕ ↦ 1 / secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [one_div] using secondOrderScale_tendsto_atTop.inv_tendsto_atTop
  have hupper : Tendsto
      (fun n : ℕ ↦
        (((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
    simpa only [add_zero] using hhalf.add hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hhalf hupper
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hM := two_mul_le_upperEndpoint n (upperTailLength c n)
    have hpOrder := bankBottomOrientedMarkerLower_le_upper hM pool
    have hbounds := bankBottomOrientedMarkerGap_bounds hM pool
    rw [← Nat.cast_sub hpOrder]
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast hbounds.1
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    have hM := two_mul_le_upperEndpoint n (upperTailLength c n)
    have hpOrder := bankBottomOrientedMarkerLower_le_upper hM pool
    have hbounds := bankBottomOrientedMarkerGap_bounds hM pool
    rw [← Nat.cast_sub hpOrder]
    have hcast :
        (bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool -
            bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℕ) ≤
          (bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 + 1 :=
      hbounds.2
    have hdivLe :
        ((bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool -
            bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℕ) : ℝ) /
              secondOrderScale n ≤
          ((((bankBottomMarkerUpper
                (upperEndpoint n (upperTailLength c n)) pool.1 -
              bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) + 1) /
            secondOrderScale n := by
      apply div_le_div_of_nonneg_right _ hscale.le
      exact_mod_cast hcast
    calc
      ((bankBottomOrientedMarkerUpper n
              (upperEndpoint n (upperTailLength c n)) pool -
            bankBottomOrientedMarkerLower n
              (upperEndpoint n (upperTailLength c n)) pool : ℕ) : ℝ) /
          secondOrderScale n ≤
        ((((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) + 1) /
          secondOrderScale n := hdivLe
      _ = (((bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) pool.1 -
            bankBottomMarkerLower n pool.1) / 2 : ℕ) : ℝ) /
            secondOrderScale n + 1 / secondOrderScale n := by ring

/-- Each of the eight literal oriented prime pools has the advertised
positive limiting cardinality on the finer prime scale. -/
theorem bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) /
            bankBottomPrimeScale n)
      atTop (nhds (bankBottomOrientedPrimeConstant c pool)) := by
  have horder : ∀ᶠ n : ℕ in atTop,
      bankBottomOrientedMarkerLower n
          (upperEndpoint n (upperTailLength c n)) pool ≤
        bankBottomOrientedMarkerUpper n
          (upperEndpoint n (upperTailLength c n)) pool :=
    Eventually.of_forall fun n ↦ bankBottomOrientedMarkerLower_le_upper
      (two_mul_le_upperEndpoint n (upperTailLength c n)) pool
  have hshort :=
    SafePrimeCounting.prime_Ioc_shortMovingInterval_normalized_tendsto
      (bankBottomMarkerBase_pos pool.1)
      (bankBottomOrientedMarkerLower_ratio_tendsto hc pool)
      (bankBottomOrientedMarkerUpper_ratio_tendsto hc pool)
      (bankBottomOrientedMarkerGap_normalized_tendsto hc pool)
      horder
  simpa only [bankBottomOrientedMarkerPrimes,
    bankBottomOrientedMarkerInterval_eq_Ioc, bankBottomPrimeScale] using hshort

private theorem card_filter_prime_Ioc {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  have hdiff :
      (Finset.Ioc a b).filter Nat.Prime =
        (Finset.range (b + 1)).filter Nat.Prime \
          (Finset.range (a + 1)).filter Nat.Prime := by
    ext prime
    by_cases hp : prime.Prime
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Finset.mem_range, hp, and_true]
      omega
    · simp [hp]
  have hsubset :
      (Finset.range (a + 1)).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime := by
    intro prime hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.add_le_add_right hab 1), hp.2⟩
  rw [hdiff, Finset.card_sdiff_of_subset hsubset]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

theorem bankBottomMarkerPrimes_card_eq_primeCounting_sub
    {n M : ℕ} (hM : 2 * n ≤ M) (move : BankBottomMove) :
    (bankBottomMarkerPrimes n M move).card =
      Nat.primeCounting (bankBottomMarkerUpper M move) -
        Nat.primeCounting (bankBottomMarkerLower n move) := by
  unfold bankBottomMarkerPrimes bankBottomMarkerInterval
  exact card_filter_prime_Ioc (bankBottomMarkerLower_le_upper hM move)

/-- At the scale actually named `secondOrderScale` in this repository, an
unsplit bottom prime pool has limit zero. -/
theorem bankBottomMarkerPrimes_card_div_secondOrderScale_tendsto_zero
    {c : ℝ} (hc : 0 < c) (move : BankBottomMove) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) move).card : ℝ) /
            secondOrderScale n)
      atTop (nhds 0) := by
  have hlower :=
    SafePrimeCounting.primeCounting_movingEndpoint_normalized_tendsto
      (bankBottomMarkerBase_pos move)
      (bankBottomMarkerLower_ratio_tendsto move)
  have hupper :=
    SafePrimeCounting.primeCounting_movingEndpoint_normalized_tendsto
      (bankBottomMarkerBase_pos move)
      (bankBottomMarkerUpper_ratio_tendsto hc move)
  have hsub := hupper.sub hlower
  have hsubNat : Tendsto
      (fun n : ℕ ↦
        ((Nat.primeCounting
            (bankBottomMarkerUpper
              (upperEndpoint n (upperTailLength c n)) move) -
          Nat.primeCounting (bankBottomMarkerLower n move) : ℕ) : ℝ) /
            secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [sub_self] using hsub.congr' (Eventually.of_forall fun n ↦ by
      have hargs := bankBottomMarkerLower_le_upper
        (two_mul_le_upperEndpoint n (upperTailLength c n)) move
      have hpi := Nat.monotone_primeCounting hargs
      rw [Nat.cast_sub hpi, secondOrderScale]
      ring)
  apply hsubNat.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [bankBottomMarkerPrimes_card_eq_primeCounting_sub
      (two_mul_le_upperEndpoint n (upperTailLength c n))]

/-- Each oriented half also has zero limit at `secondOrderScale`. -/
theorem bankBottomOrientedMarkerPrimes_card_div_secondOrderScale_tendsto_zero
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    Tendsto
      (fun n : ℕ ↦
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) /
            secondOrderScale n)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (nhds 0))
    (bankBottomMarkerPrimes_card_div_secondOrderScale_tendsto_zero hc pool.1)
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    exact div_nonneg (by positivity) hscale.le
  · filter_upwards [eventually_secondOrderScale_pos] with n hscale
    apply div_le_div_of_nonneg_right _ hscale.le
    exact_mod_cast Finset.card_le_card
      (bankBottomOrientedMarkerPrimes_subset
        (two_mul_le_upperEndpoint n (upperTailLength c n)) pool)

/-- The scaled endpoint is eventually narrow enough for all four rows, and
hence all eight oriented pools, to be disjoint. -/
theorem eventually_bankBottom_scaledEndpoint_narrow
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      5 * upperEndpoint n (upperTailLength c n) ≤ 12 * n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 2 / 5))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have htailR :
      5 * (upperTailLength c n : ℝ) < 2 * (n : ℝ) := by
    have := (div_lt_iff₀ hnR).mp hratio
    linarith
  have htail : 5 * upperTailLength c n ≤ 2 * n := by
    exact_mod_cast htailR.le
  unfold upperEndpoint
  omega

end

end Erdos390.WholePaper
