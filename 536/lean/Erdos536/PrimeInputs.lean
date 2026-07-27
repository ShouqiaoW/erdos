import PrimeNumberTheoremAnd.BrunTitchmarsh
import PrimeNumberTheoremAnd.MediumPNT

/-!
# Audited analytic prime inputs for Erdős 536

This module exposes only results whose dependency closure has been fully
checked. The quantitative prime-number theorem comes from
`PrimeNumberTheoremAnd.MediumPNT`, and the interval bound comes from the
fully proved Selberg-sieve development in
`PrimeNumberTheoremAnd.BrunTitchmarsh`.

The medium PNT has a stretched-exponential error.  The elementary
`ψ - θ` estimate in Mathlib then implies a `θ` error smaller than every
fixed real power of `1 / log x`.
-/

open Filter Topology Asymptotics

namespace Erdos536.PrimeInputs

/-- A local, audited name for the clean medium-strength prime number
theorem supplied by `PrimeNumberTheoremAnd`. Its dependency closure uses
only Lean's standard logical principles. -/
theorem mediumPNT :
    ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        (fun x : ℝ ↦
          x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :=
  MediumPNT

/-- The medium PNT error for `ψ` is smaller than every fixed real
logarithmic power. -/
theorem psi_error_isBigO_log_power (A : ℝ) :
    (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ ↦ x / (Real.log x) ^ A) := by
  obtain ⟨c, hc, hPNT⟩ := mediumPNT
  apply hPNT.trans
  have hpow : Tendsto (fun x : ℝ ↦ (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atTop := by
    exact tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10) |>.comp
      Real.tendsto_log_atTop
  have hdecay :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-10 * A)).comp_tendsto hpow
  have hdecay' :
      (fun x : ℝ ↦ Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =O[atTop] (fun x : ℝ ↦ (Real.log x) ^ (-A)) := by
    apply hdecay.isBigO.congr' (Eventually.of_forall fun x ↦ rfl)
    filter_upwards [Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (0 : ℝ))] with x hx
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hx]
    congr 2
    ring
  have hmul := (isBigO_refl (fun x : ℝ ↦ x) atTop).mul hdecay'
  apply hmul.congr' (Eventually.of_forall fun x ↦ rfl)
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (0 : ℝ))] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- The elementary prime-power correction `√x log x` is smaller than the
same arbitrary fixed logarithmic PNT scale. -/
theorem sqrt_mul_log_isBigO_log_power (A : ℝ) :
    (fun x : ℝ ↦ Real.sqrt x * Real.log x) =O[atTop]
      (fun x : ℝ ↦ x / (Real.log x) ^ A) := by
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop (A + 1)
      (by norm_num : (0 : ℝ) < 1 / 2)).isBigO
  let common : ℝ → ℝ := fun x ↦ x ^ ((1 : ℝ) / 2) / (Real.log x) ^ A
  have hmul := hlog.mul (isBigO_refl common atTop)
  apply hmul.congr'
  · filter_upwards [Real.tendsto_log_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)), eventually_gt_atTop (0 : ℝ)]
      with x hlogx hx
    dsimp [common]
    rw [Real.sqrt_eq_rpow, Real.rpow_add hlogx]
    field_simp
    simp [Real.rpow_one]
  · filter_upwards [Real.tendsto_log_atTop.eventually
      (eventually_gt_atTop (0 : ℝ)), eventually_gt_atTop (0 : ℝ)]
      with x hlogx hx
    dsimp [common]
    calc
      x ^ ((1 : ℝ) / 2) *
          (x ^ ((1 : ℝ) / 2) / Real.log x ^ A) =
          (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) /
            Real.log x ^ A := by ring
      _ = x ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2) /
          Real.log x ^ A := by
        rw [Real.rpow_add hx]
      _ = x / Real.log x ^ A := by
        norm_num [Real.rpow_one]

/-- Quantitative PNT for Chebyshev's `θ`, at every fixed real logarithmic
power.  This is the form needed for partial summation over primes. -/
theorem theta_error_isBigO_log_power (A : ℝ) :
    (Chebyshev.theta - id) =O[atTop]
      (fun x : ℝ ↦ x / (Real.log x) ^ A) := by
  have hraw :
      (Chebyshev.theta - Chebyshev.psi) =O[atTop]
        (fun x : ℝ ↦ Real.sqrt x * Real.log x) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hnonneg : 0 ≤ Real.sqrt x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm,
      Real.norm_of_nonneg hnonneg, mul_assoc] using
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hdiff := hraw.trans (sqrt_mul_log_isBigO_log_power A)
  have hadd := hdiff.add (psi_error_isBigO_log_power A)
  apply hadd.congr' (Eventually.of_forall fun x ↦ ?_)
    (Eventually.of_forall fun x ↦ rfl)
  simp only [Pi.sub_apply, id_eq]
  ring

/-- The clean Selberg-sieve interval estimate from
`PrimeNumberTheoremAnd`, restated in the namespace used by this project.

Here `BrunTitchmarsh.primesBetween x (x + y)` is the number of primes in
the closed integer interval from `ceil x` through `floor (x + y)`.
Choosing (for example) `z = y^(1/2)` gives the
`O(y / log y)` interval upper bound required in the paper; the displayed
remainder is negligible in the exponentially long intervals used there. -/
theorem interval_prime_count_le (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) :
    (BrunTitchmarsh.primesBetween x (x + y) : ℝ) ≤
      2 * y / Real.log z + 6 * z * (1 + Real.log z) ^ 3 :=
  BrunTitchmarsh.primesBetween_le x y z hx hy hz

/-- A parameter-free form of `interval_prime_count_le`, obtained by
choosing the Selberg-sieve level `z = y^(1/2)`.  Its leading term is
`4 y / log y`, and its explicit square-root remainder is negligible for
the exponentially long intervals used in the prime-band argument. -/
theorem interval_prime_count_le_sqrt (x y : ℝ)
    (hx : 0 < x) (hy : 1 < y) :
    (BrunTitchmarsh.primesBetween x (x + y) : ℝ) ≤
      4 * y / Real.log y +
        6 * y ^ ((1 : ℝ) / 2) *
          (1 + (1 / 2 : ℝ) * Real.log y) ^ 3 := by
  have h := interval_prime_count_le x y (y ^ ((1 : ℝ) / 2)) hx
    (by positivity) (Real.one_lt_rpow hy (by norm_num))
  rw [Real.log_rpow (by positivity)] at h
  convert h using 1
  all_goals ring

end Erdos536.PrimeInputs
