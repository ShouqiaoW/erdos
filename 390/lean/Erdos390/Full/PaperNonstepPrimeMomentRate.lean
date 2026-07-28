import Erdos390.Full.PrimeSums

/-!
# Vanishing reciprocal-square logarithmic moment

The moving-low non-step ledger needs the literal quantity
`sum t_p / p^2`, not a step-function surrogate.  This file proves directly
that it tends to zero for every fixed cutoff.  The proof uses only the
already-audited harmonic prime bound and `log p ≤ p`; no PNT asymptotic is
introduced.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PrimeSums

open ArithmeticModel Scale

noncomputable section

/-- The global `G₂` output moment in the non-step slow-row ledger. -/
def bandTReciprocalSquareSum (n W : ℕ) : ℝ :=
  ∑ p ∈ primeBand n W, tPrime n p * (1 / (p : ℝ)) ^ 2

theorem bandTReciprocalSquareSum_nonneg
    {n W : ℕ} (hn : 1 < n) :
    0 ≤ bandTReciprocalSquareSum n W := by
  unfold bandTReciprocalSquareSum
  exact Finset.sum_nonneg fun p hp ↦
    mul_nonneg
      (by
        unfold tPrime
        apply div_nonneg
        · exact Real.log_nonneg
            (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
        · rw [log_y (Nat.zero_lt_of_lt hn)]
          exact (mul_pos (by norm_num)
            (Real.log_pos (by exact_mod_cast hn))).le)
      (sq_nonneg _)

/-- Elementary domination by the harmonic mass divided by `log y`. -/
theorem bandTReciprocalSquareSum_le
    {n W : ℕ} (hn : 1 < n) :
    bandTReciprocalSquareSum n W ≤
      bandReciprocalSum n W / Real.log (y n) := by
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  unfold bandTReciprocalSquareSum bandReciprocalSum
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime := prime_of_mem_primeBand hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hlogp : Real.log (p : ℝ) ≤ (p : ℝ) := by
    have h := Real.log_le_sub_one_of_pos hpR
    linarith
  unfold tPrime
  rw [show (Real.log (p : ℝ) / Real.log (y n)) *
      (1 / (p : ℝ)) ^ 2 =
        (Real.log (p : ℝ) / (p : ℝ)) *
          (1 / (p : ℝ)) / Real.log (y n) by ring]
  apply div_le_div_of_nonneg_right _ hlogy.le
  have hinv : 0 ≤ (1 / (p : ℝ)) := by positivity
  calc
    (Real.log (p : ℝ) / (p : ℝ)) * (1 / (p : ℝ)) ≤
        1 * (1 / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ hinv
      exact (div_le_one hpR).2 hlogp
    _ = 1 / (p : ℝ) := one_mul _

/-- For every fixed cutoff, the literal global `sum t_p/p²` tends to zero.
This rate is independent of every later mesh and tilt box. -/
theorem tendsto_bandTReciprocalSquareSum_zero (W : ℕ) :
    Tendsto (fun n : ℕ ↦ bandTReciprocalSquareSum n W)
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLdivL : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajorant : Tendsto (fun n : ℕ ↦
      54 * (Real.log (L n) / L n)) atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlogLdivL
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ bandTReciprocalSquareSum n W := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact bandTReciprocalSquareSum_nonneg hn
  have hupper : ∀ᶠ n : ℕ in atTop,
      bandTReciprocalSquareSum n W ≤
        54 * (Real.log (L n) / L n) := by
    filter_upwards [eventually_gt_atTop 1,
      eventually_bandReciprocalSum_le_logL W] with n hn hmass
    have hlogyN : 0 < Real.log (y n) := by
      rw [log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    have hraw := (bandTReciprocalSquareSum_le hn).trans
      (div_le_div_of_nonneg_right hmass hlogyN.le)
    calc
      bandTReciprocalSquareSum n W ≤
          (12 * Real.log (L n)) / Real.log (y n) := hraw
      _ = 54 * (Real.log (L n) / L n) := by
        rw [log_y (Nat.zero_lt_of_lt hn)]
        ring
  exact squeeze_zero' hnonneg hupper hmajorant

end

end Erdos390.Full.PrimeSums
