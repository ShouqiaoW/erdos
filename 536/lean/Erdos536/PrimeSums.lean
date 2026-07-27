import Erdos536.PrimeInputs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Abel summation and prime sums

This file derives the prime-sum estimates used in the proof from the
audited quantitative prime-number theorem in `Erdos536.PrimeInputs`.
In particular, no version of Mertens' theorem is assumed.
-/

open scoped BigOperators Nat.Prime
open Filter Topology Asymptotics Set

noncomputable section

namespace Erdos536.PrimeSums

open MeasureTheory
open Erdos536.PrimeInputs

/-- The finite set of primes at most `Y`. -/
def primesUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 0 Y).filter Nat.Prime

/-- The logarithmically weighted prime harmonic sum up to `Y`. -/
def fullLogReciprocalSum (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)

/-- The prime harmonic sum up to `Y`. -/
def fullReciprocalSum (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, 1 / (p : ℝ)

/-- The prime harmonic sum with the denominator shifted by one. -/
def fullShiftedReciprocalSum (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, 1 / ((p : ℝ) + 1)

/-- The square-reciprocal mass of primes in `(A,Y]`. -/
def reciprocalSquareSumBetween (A Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y \ primesUpTo A, 1 / (p : ℝ) ^ 2

private def primeLogCoeff (k : ℕ) : ℝ :=
  if k.Prime then Real.log (k : ℝ) else 0

private theorem sum_primeLogCoeff_Icc (x : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoeff k) =
      Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  rw [Finset.sum_filter]
  rfl

private theorem inv_sq_le_telescope {k : ℕ} (hk : 2 ≤ k) :
    1 / (k : ℝ) ^ 2 ≤
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hk10 : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < k - 1)
  have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ k by omega)]
    norm_num
  have hrhs :
      1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) =
        1 / ((k : ℝ) * ((k - 1 : ℕ) : ℝ)) := by
    field_simp [hk0.ne', hk10.ne']
    nlinarith [hcast]
  rw [hrhs]
  gcongr
  nlinarith

private theorem telescope_Icc_le_inv (A Y : ℕ) (hA : 1 ≤ A) :
    (∑ k ∈ Finset.Icc (A + 1) Y,
      (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ))) ≤
        1 / (A : ℝ) := by
  by_cases hAY : A ≤ Y
  · have hset : Finset.Icc (A + 1) Y =
        Finset.Ico (A + 1) (Y + 1) := by
      ext k
      simp
    rw [hset, Finset.sum_Ico_eq_sum_range]
    have hterm : ∀ i ∈ Finset.range ((Y + 1) - (A + 1)),
        1 / ((((A + 1) + i) - 1 : ℕ) : ℝ) -
            1 / ((A + 1 + i : ℕ) : ℝ) =
          1 / ((A + i : ℕ) : ℝ) -
            1 / ((A + i + 1 : ℕ) : ℝ) := by
      intro i hi
      congr 2 <;> norm_cast <;> omega
    rw [Finset.sum_congr rfl hterm]
    have htel :=
      Finset.sum_range_sub'
        (fun i : ℕ => 1 / ((A + i : ℕ) : ℝ)) (Y - A)
    rw [show (Y + 1) - (A + 1) = Y - A by omega]
    have htel' :
        (∑ i ∈ Finset.range (Y - A),
          (1 / ((A + i : ℕ) : ℝ) -
            1 / ((A + i + 1 : ℕ) : ℝ))) =
          1 / ((A + 0 : ℕ) : ℝ) -
            1 / ((A + (Y - A) : ℕ) : ℝ) := by
      simpa only [Nat.add_assoc] using htel
    rw [htel']
    exact sub_le_self _ (by positivity)
  · have hempty : Finset.Icc (A + 1) Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hempty]
    simp

/-- The square-reciprocal tail over primes in `(A,Y]` is at most `1/A`. -/
theorem reciprocalSquareSumBetween_le (A Y : ℕ) (hA : 1 ≤ A) :
    reciprocalSquareSumBetween A Y ≤ 1 / (A : ℝ) := by
  calc
    reciprocalSquareSumBetween A Y ≤
        ∑ p ∈ primesUpTo Y \ primesUpTo A,
          (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := by
        have hpY : p ≤ Y ∧ p.Prime := by
          simpa [primesUpTo] using (Finset.mem_sdiff.mp hp).1
        exact hpY.2
      exact inv_sq_le_telescope hpPrime.two_le
    _ ≤ ∑ k ∈ Finset.Icc (A + 1) Y,
          (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpY : p ≤ Y ∧ p.Prime := by
          simpa [primesUpTo] using (Finset.mem_sdiff.mp hp).1
        have hpA : ¬p ≤ A := by
          simpa [primesUpTo, hpY.2] using (Finset.mem_sdiff.mp hp).2
        simp [hpY.1, Nat.lt_iff_add_one_le.mp (lt_of_not_ge hpA)]
      · intro k hk hnot
        have hk' := Finset.mem_Icc.mp hk
        exact le_trans (by positivity : (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2)
          (inv_sq_le_telescope (by omega))
    _ ≤ 1 / (A : ℝ) := telescope_Icc_le_inv A Y hA

/-- Abel summation for `∑_{p≤Y} log p / p`. -/
theorem fullLogReciprocalSum_eq (Y : ℕ) (hY : 2 ≤ Y) :
    fullLogReciprocalSum Y =
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
        ∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2 := by
  let c : ℕ → ℝ := primeLogCoeff
  have hc0 : c 0 = 0 := by simp [c, primeLogCoeff]
  have hc1 : c 1 = 0 := by simp [c, primeLogCoeff]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) Y,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (by linarith [ht.1])
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun x : ℝ => x⁻¹)) (Set.Icc (2 : ℝ) Y) := by
    rw [show deriv (fun x : ℝ => x⁻¹) =
        fun x => -(x ^ 2)⁻¹ by
      funext x
      exact deriv_inv]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht20 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    exact ContinuousAt.continuousWithinAt
      (((continuousAt_id.pow 2).inv₀ ht20).neg)
  have habel := sum_mul_eq_sub_integral_mul₁
    (f := fun x : ℝ => x⁻¹) c hc0 hc1 (Y : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hY)] at habel
  rw [show (⌊(Y : ℝ)⌋₊ : ℕ) = Y by simp] at habel
  have hcumY : (∑ k ∈ Finset.Icc 0 Y, c k) =
      Chebyshev.theta (Y : ℝ) := by
    simpa [c] using sum_primeLogCoeff_Icc (Y : ℝ)
  have hcum : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
        Chebyshev.theta t := by
    intro t
    simpa [c] using sum_primeLogCoeff_Icc t
  rw [hcumY] at habel
  simp_rw [hcum] at habel
  simp_rw [deriv_inv] at habel
  have hlhs :
      (∑ k ∈ Finset.Icc 0 Y, (k : ℝ)⁻¹ * c k) =
        fullLogReciprocalSum Y := by
    simp [fullLogReciprocalSum, primesUpTo, c, primeLogCoeff,
      Finset.sum_filter, div_eq_mul_inv, mul_comm]
  rw [hlhs] at habel
  have hInt :
      (∫ x in (2 : ℝ)..Y,
        -(x ^ 2)⁻¹ * Chebyshev.theta x) =
        -(∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x / x ^ 2) := by
    calc
      (∫ x in (2 : ℝ)..Y, -(x ^ 2)⁻¹ * Chebyshev.theta x) =
          ∫ x in (2 : ℝ)..Y,
            -(Chebyshev.theta x / x ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simp only [div_eq_mul_inv]
        ring
      _ = -(∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x / x ^ 2) :=
        intervalIntegral.integral_neg
  rw [hInt] at habel
  calc
    fullLogReciprocalSum Y =
        (Y : ℝ)⁻¹ * Chebyshev.theta (Y : ℝ) +
          ∫ x in (2 : ℝ)..Y,
            Chebyshev.theta x / x ^ 2 := by
      linarith
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
        ∫ t in (2 : ℝ)..Y,
          Chebyshev.theta t / t ^ 2 := by
      rw [div_eq_mul_inv]
      ring

private theorem deriv_inv_mul_log {x : ℝ} (hx : x ≠ 0)
    (hlog : Real.log x ≠ 0) :
    deriv (fun z : ℝ => (z * Real.log z)⁻¹) x =
      -(Real.log x + 1) /
        (x ^ 2 * Real.log x ^ 2) := by
  have hmul : HasDerivAt (fun z : ℝ => z * Real.log z)
      (Real.log x + x * x⁻¹) x := by
    simpa only [one_mul, id_eq] using
      (hasDerivAt_id x).mul (Real.hasDerivAt_log hx)
  have hinv : HasDerivAt
      (fun z : ℝ => (z * Real.log z)⁻¹)
      (-(Real.log x + x * x⁻¹) /
        (x * Real.log x) ^ 2) x :=
    hmul.inv (mul_ne_zero hx hlog)
  rw [hinv.deriv]
  field_simp

/-- Abel summation for `∑_{p≤Y} 1/p`. -/
theorem fullReciprocalSum_eq (Y : ℕ) (hY : 2 ≤ Y) :
    fullReciprocalSum Y =
      Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) +
        ∫ t in (2 : ℝ)..Y,
          Chebyshev.theta t * (Real.log t + 1) /
            (t ^ 2 * Real.log t ^ 2) := by
  let c : ℕ → ℝ := primeLogCoeff
  have hc0 : c 0 = 0 := by simp [c, primeLogCoeff]
  have hc1 : c 1 = 0 := by simp [c, primeLogCoeff]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) Y,
      DifferentiableAt ℝ
        (fun x : ℝ => (x * Real.log x)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one
        (by linarith [ht.1]) (by linarith [ht.1])
    exact
      (((differentiableAt_id.mul
          (Real.differentiableAt_log ht0))).inv
        (mul_ne_zero ht0 hlog0))
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun x : ℝ => (x * Real.log x)⁻¹))
        (Set.Icc (2 : ℝ) Y) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one
        (by linarith [ht.1]) (by linarith [ht.1])
    have hcont : ContinuousWithinAt
        (fun u : ℝ => -(Real.log u + 1) /
          (u ^ 2 * Real.log u ^ 2))
        (Set.Icc (2 : ℝ) Y) t :=
      ContinuousAt.continuousWithinAt
        (((Real.continuousAt_log ht0).add
          continuousAt_const).neg.div
          ((continuousAt_id.pow 2).mul
            ((Real.continuousAt_log ht0).pow 2))
          (mul_ne_zero (pow_ne_zero 2 ht0)
            (pow_ne_zero 2 hlog0)))
    refine hcont.congr (fun (u : ℝ) hu => ?_) ?_
    · exact deriv_inv_mul_log
        (by linarith [hu.1])
        (Real.log_ne_zero_of_pos_of_ne_one
          (by linarith [hu.1]) (by linarith [hu.1]))
    · exact deriv_inv_mul_log ht0 hlog0
  have habel := sum_mul_eq_sub_integral_mul₁
    (f := fun x : ℝ => (x * Real.log x)⁻¹)
    c hc0 hc1 (Y : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le
    (by exact_mod_cast hY)] at habel
  rw [show (⌊(Y : ℝ)⌋₊ : ℕ) = Y by simp] at habel
  have hcumY : (∑ k ∈ Finset.Icc 0 Y, c k) =
      Chebyshev.theta (Y : ℝ) := by
    simpa [c] using sum_primeLogCoeff_Icc (Y : ℝ)
  have hcum : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
        Chebyshev.theta t := by
    intro t
    simpa [c] using sum_primeLogCoeff_Icc t
  rw [hcumY] at habel
  simp_rw [hcum] at habel
  have hlhs :
      (∑ k ∈ Finset.Icc 0 Y,
        ((k : ℝ) * Real.log (k : ℝ))⁻¹ * c k) =
        fullReciprocalSum Y := by
    rw [fullReciprocalSum, primesUpTo, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hprime : k.Prime
    · have hk0 : (k : ℝ) ≠ 0 := by
        exact_mod_cast hprime.ne_zero
      have hlog0 : Real.log (k : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one
          (by exact_mod_cast hprime.pos)
          (by exact_mod_cast hprime.ne_one)
      simp only [c, primeLogCoeff, hprime, if_true]
      field_simp
    · simp [c, primeLogCoeff, hprime]
  rw [hlhs] at habel
  have hInt :
      (∫ x in (2 : ℝ)..Y,
        deriv (fun z : ℝ =>
          (z * Real.log z)⁻¹) x * Chebyshev.theta x) =
        -(∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2)) := by
    calc
      (∫ x in (2 : ℝ)..Y,
        deriv (fun z : ℝ => (z * Real.log z)⁻¹) x *
          Chebyshev.theta x) =
          ∫ x in (2 : ℝ)..Y,
            -(Chebyshev.theta x * (Real.log x + 1) /
              (x ^ 2 * Real.log x ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le
          (by exact_mod_cast hY)] at hx
        have hx0 : x ≠ 0 := by linarith [hx.1]
        have hlog0 : Real.log x ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one
            (by linarith [hx.1]) (by linarith [hx.1])
        change deriv (fun z : ℝ =>
          (z * Real.log z)⁻¹) x *
            Chebyshev.theta x = _
        rw [deriv_inv_mul_log hx0 hlog0]
        ring
      _ = -(∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2)) :=
        intervalIntegral.integral_neg
  rw [hInt] at habel
  have hY0 : (Y : ℝ) ≠ 0 := by positivity
  have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by positivity)
      (by exact_mod_cast (show Y ≠ 1 by omega))
  calc
    fullReciprocalSum Y =
        (((Y : ℝ) * Real.log (Y : ℝ))⁻¹ *
            Chebyshev.theta (Y : ℝ)) +
          ∫ x in (2 : ℝ)..Y,
            Chebyshev.theta x * (Real.log x + 1) /
              (x ^ 2 * Real.log x ^ 2) := by
      linarith
    _ = Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) +
        ∫ t in (2 : ℝ)..Y,
          Chebyshev.theta t * (Real.log t + 1) /
            (t ^ 2 * Real.log t ^ 2) := by
      field_simp

/-- Local integrability of the first Abel kernel. -/
theorem intervalIntegrable_theta_div_sq {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t / t ^ 2)
      MeasureTheory.volume 2 Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hY]
  conv =>
    arg 1
    ext t
    rw [Chebyshev.theta, div_eq_mul_inv, mul_comm,
      Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) ?_
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  exact ContinuousAt.continuousWithinAt
    ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0))

/-- Local integrability of the harmonic Abel kernel. -/
theorem intervalIntegrable_mertensIntegrand {Y : ℝ}
    (hY : 2 ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ =>
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2))
      MeasureTheory.volume 2 Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hY]
  have hg : MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        ((Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) *
            Chebyshev.theta t)
      (Set.Icc (2 : ℝ) Y) := by
    conv =>
      arg 1
      ext t
      rw [Chebyshev.theta, Finset.sum_filter]
    refine integrableOn_mul_sum_Icc _ (by norm_num) ?_
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one
        (by linarith [ht.1]) (by linarith [ht.1])
    exact (((Real.continuousAt_log ht0).add
      continuousAt_const).div
      ((continuousAt_id.pow 2).mul
        ((Real.continuousAt_log ht0).pow 2))
      (mul_ne_zero (pow_ne_zero 2 ht0)
        (pow_ne_zero 2 hlog0))).continuousWithinAt
  exact hg.congr_fun (by
    intro t ht
    ring) measurableSet_Icc

/-! ## Exact two-endpoint formulae -/

/-- The main primitive in Abel summation for the prime harmonic sum. -/
def mertensMainPrimitive (x : ℝ) : ℝ :=
  Real.log (Real.log x) - (Real.log x)⁻¹

/-- The corresponding main integrand. -/
def mertensMainKernel (x : ℝ) : ℝ :=
  (Real.log x + 1) / (x * Real.log x ^ 2)

/-- The PNT error `θ(x)-x`. -/
def thetaError (x : ℝ) : ℝ :=
  Chebyshev.theta x - x

/-- The exact error integrand for harmonic-prime quadrature. -/
def mertensErrorKernel (x : ℝ) : ℝ :=
  thetaError x * (Real.log x + 1) /
    (x ^ 2 * Real.log x ^ 2)

lemma hasDerivAt_mertensMainPrimitive {x : ℝ} (hx : 1 < x) :
    HasDerivAt mertensMainPrimitive (mertensMainKernel x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have hloglog := (Real.hasDerivAt_log hx0).log hlog0
  have hinv := (Real.hasDerivAt_log hx0).inv hlog0
  have hsub := hloglog.sub hinv
  convert hsub using 1
  unfold mertensMainKernel
  field_simp [hx0, hlog0]
  ring

lemma continuousOn_mertensMainKernel {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn mertensMainKernel (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx1)
  unfold mertensMainKernel
  exact (((Real.continuousAt_log hx0).add
    continuousAt_const).div
    (continuousAt_id.mul
      ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero hx0 (pow_ne_zero 2 hlog0))).continuousWithinAt

/-- Exact integral of the Mertens main kernel. -/
lemma integral_mertensMainKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, mertensMainKernel x) =
      mertensMainPrimitive Y - mertensMainPrimitive A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_mertensMainPrimitive
      (by linarith [hx.1, hA])
  · exact
      (continuousOn_mertensMainKernel (by linarith [hA]))
        |>.intervalIntegrable_of_Icc hAY

private def mertensAbelKernel (x : ℝ) : ℝ :=
  Chebyshev.theta x * (Real.log x + 1) /
    (x ^ 2 * Real.log x ^ 2)

private lemma mertensAbelKernel_eq_main_add_error
    {x : ℝ} (hx : 1 < x) :
    mertensAbelKernel x =
      mertensMainKernel x + mertensErrorKernel x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx)
  unfold mertensAbelKernel mertensMainKernel
    mertensErrorKernel thetaError
  field_simp [hx0, hlog0]
  ring

private lemma intervalIntegrable_mertensAbelKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable mertensAbelKernel volume A Y := by
  have h2Y : (2 : ℝ) ≤ Y := hA.trans hAY
  have hfull := intervalIntegrable_mertensIntegrand h2Y
  apply hfull.mono_set
  rw [uIcc_of_le hAY, uIcc_of_le h2Y]
  intro x hx
  exact ⟨hA.trans hx.1, hx.2⟩

private lemma integral_mertensAbelKernel_sub {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (2 : ℝ)..Y, mertensAbelKernel x) -
        (∫ x in (2 : ℝ)..A, mertensAbelKernel x) =
      ∫ x in (A : ℝ)..Y, mertensAbelKernel x := by
  have h2A : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hleft : IntervalIntegrable mertensAbelKernel volume
      2 (A : ℝ) := by
    simpa only [mertensAbelKernel] using
      (intervalIntegrable_mertensIntegrand h2A)
  have hright : IntervalIntegrable mertensAbelKernel volume
      (A : ℝ) (Y : ℝ) :=
    intervalIntegrable_mertensAbelKernel h2A hAYR
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

private lemma intervalIntegrable_mertensErrorKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable mertensErrorKernel volume A Y := by
  have habel := intervalIntegrable_mertensAbelKernel hA hAY
  have hmain : IntervalIntegrable mertensMainKernel volume A Y :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_mertensMainKernel (A := A) (Y := Y)
        (by linarith [hA]))
  have hsub := habel.sub hmain
  apply hsub.congr
  intro x hx
  change mertensAbelKernel x - mertensMainKernel x =
    mertensErrorKernel x
  rw [mertensAbelKernel_eq_main_add_error (by
    rw [uIoc_of_le hAY] at hx
    linarith [hx.1, hA])]
  ring

/-- Exact two-endpoint harmonic-prime identity.  All nonconstant
arithmetic content is isolated in `thetaError`. -/
theorem fullReciprocalSum_interval_error_identity {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) =
      thetaError (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) -
      thetaError (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
      ∫ x in (A : ℝ)..Y, mertensErrorKernel x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hmain := integral_mertensMainKernel hAR hAYR
  have herrInt := intervalIntegrable_mertensErrorKernel hAR hAYR
  have hmainInt :
      IntervalIntegrable mertensMainKernel volume
        (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) hAYR
      (continuousOn_mertensMainKernel
        (A := (A : ℝ)) (Y := (Y : ℝ))
        (by linarith [hAR]))
  have hsplit :
      (∫ x in (A : ℝ)..Y, mertensAbelKernel x) =
        (∫ x in (A : ℝ)..Y, mertensMainKernel x) +
          ∫ x in (A : ℝ)..Y, mertensErrorKernel x := by
    rw [← intervalIntegral.integral_add hmainInt herrInt]
    apply intervalIntegral.integral_congr
    intro x hx
    exact mertensAbelKernel_eq_main_add_error (by
      rw [uIcc_of_le hAYR] at hx
      linarith [hx.1, hAR])
  rw [fullReciprocalSum_eq Y hY,
    fullReciprocalSum_eq A hA]
  have habelSub := integral_mertensAbelKernel_sub hA hAY
  calc
    (Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) +
          (∫ x in (2 : ℝ)..Y, mertensAbelKernel x)) -
        (Chebyshev.theta (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
          ∫ x in (2 : ℝ)..A, mertensAbelKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) =
      Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) -
        Chebyshev.theta (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
        ((∫ x in (2 : ℝ)..Y, mertensAbelKernel x) -
          ∫ x in (2 : ℝ)..A, mertensAbelKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) := by
      ring
    _ = Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) -
        Chebyshev.theta (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
        (∫ x in (A : ℝ)..Y, mertensMainKernel x) +
        (∫ x in (A : ℝ)..Y, mertensErrorKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) := by
      rw [habelSub, hsplit]
      ring
    _ = _ := by
      rw [hmain]
      unfold mertensMainPrimitive thetaError
      have hA0 : (A : ℝ) ≠ 0 := by positivity
      have hY0 : (Y : ℝ) ≠ 0 := by positivity
      have hlogA0 : Real.log (A : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos
          (by exact_mod_cast (show 1 < A by omega)))
      have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos
          (by exact_mod_cast (show 1 < Y by omega)))
      field_simp [hA0, hY0, hlogA0, hlogY0]
      ring

/-! ## The first logarithmic moment -/

/-- PNT remainder in Abel summation for `∑ log p / p`. -/
def logReciprocalErrorKernel (x : ℝ) : ℝ :=
  thetaError x / x ^ 2

private lemma intervalIntegrable_thetaDivSq_segment {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ => Chebyshev.theta x / x ^ 2)
      volume A Y := by
  have h2Y : (2 : ℝ) ≤ Y := hA.trans hAY
  have hfull := intervalIntegrable_theta_div_sq h2Y
  apply hfull.mono_set
  rw [uIcc_of_le hAY, uIcc_of_le h2Y]
  intro x hx
  exact ⟨hA.trans hx.1, hx.2⟩

private lemma integral_thetaDivSq_sub {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (2 : ℝ)..Y,
        Chebyshev.theta x / x ^ 2) -
        (∫ x in (2 : ℝ)..A,
          Chebyshev.theta x / x ^ 2) =
      ∫ x in (A : ℝ)..Y,
        Chebyshev.theta x / x ^ 2 := by
  have h2A : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hleft := intervalIntegrable_theta_div_sq h2A
  have hright :=
    intervalIntegrable_thetaDivSq_segment h2A hAYR
  have hadd :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

private lemma intervalIntegrable_oneDiv_segment {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable (fun x : ℝ => 1 / x) volume A Y := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hA, hx.1]
  exact
    (continuousAt_const.div continuousAt_id hx0).continuousWithinAt

private lemma intervalIntegrable_logReciprocalErrorKernel
    {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable logReciprocalErrorKernel volume A Y := by
  have htheta := intervalIntegrable_thetaDivSq_segment hA hAY
  have hmain := intervalIntegrable_oneDiv_segment hA hAY
  apply (htheta.sub hmain).congr
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [uIoc_of_le hAY] at hx
    linarith [hA, hx.1]
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]

private lemma integral_thetaDivSq_split {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, Chebyshev.theta x / x ^ 2) =
      (∫ x in A..Y, 1 / x) +
        ∫ x in A..Y, logReciprocalErrorKernel x := by
  have hmain := intervalIntegrable_oneDiv_segment hA hAY
  have herr :=
    intervalIntegrable_logReciprocalErrorKernel hA hAY
  rw [← intervalIntegral.integral_add hmain herr]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [uIcc_of_le hAY] at hx
    linarith [hA, hx.1]
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]
  ring

/-- Exact two-endpoint identity for the first logarithmic moment. -/
theorem fullLogReciprocalSum_interval_error_identity {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) =
      thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y,
          logReciprocalErrorKernel x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  rw [fullLogReciprocalSum_eq Y hY,
    fullLogReciprocalSum_eq A hA]
  have hsub := integral_thetaDivSq_sub hA hAY
  have hsplit := integral_thetaDivSq_split hAR hAYR
  have hmain : (∫ x in (A : ℝ)..Y, 1 / x) =
      Real.log (Y : ℝ) - Real.log (A : ℝ) := by
    rw [integral_one_div_of_pos hApos hYpos,
      Real.log_div (ne_of_gt hYpos) (ne_of_gt hApos)]
  calc
    (Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
          ∫ x in (2 : ℝ)..Y,
            Chebyshev.theta x / x ^ 2) -
        (Chebyshev.theta (A : ℝ) / (A : ℝ) +
          ∫ x in (2 : ℝ)..A,
            Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) =
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        ((∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x / x ^ 2) -
          ∫ x in (2 : ℝ)..A,
            Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by
      ring
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        (∫ x in (A : ℝ)..Y,
          Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by
      rw [hsub]
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        ((∫ x in (A : ℝ)..Y, 1 / x) +
          ∫ x in (A : ℝ)..Y,
            logReciprocalErrorKernel x) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by
      rw [hsplit]
    _ = thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y,
          logReciprocalErrorKernel x := by
      rw [hmain]
      unfold thetaError
      field_simp [ne_of_gt hApos, ne_of_gt hYpos]
      ring

/-! ## Quantitative PNT remainder -/

/-- An elementary majorant for the Abel-summed PNT error. -/
def mertensErrorMajorant (C x : ℝ) : ℝ :=
  3 * C / (x * Real.log x ^ 4)

/-- Primitive of the preceding majorant. -/
def mertensErrorPrimitive (C x : ℝ) : ℝ :=
  -C / Real.log x ^ 3

lemma hasDerivAt_mertensErrorPrimitive (C : ℝ)
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt (mertensErrorPrimitive C)
      (mertensErrorMajorant C x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx)
  have hpow := (Real.hasDerivAt_log hx0).pow 3
  have hinv := hpow.inv (pow_ne_zero 3 hlog0)
  have hmul := (hasDerivAt_const x (-C)).mul hinv
  convert hmul using 1
  unfold mertensErrorMajorant
  simp only [Pi.pow_apply]
  field_simp [hx0, hlog0]
  ring

lemma continuousOn_mertensErrorMajorant (C : ℝ)
    {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn (mertensErrorMajorant C) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx1)
  unfold mertensErrorMajorant
  exact
    continuousAt_const.div
      (continuousAt_id.mul
        ((Real.continuousAt_log hx0).pow 4))
      (mul_ne_zero hx0 (pow_ne_zero 4 hlog0))
      |>.continuousWithinAt

lemma integral_mertensErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, mertensErrorMajorant C x) =
      mertensErrorPrimitive C Y -
        mertensErrorPrimitive C A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_mertensErrorPrimitive C
      (by linarith [hx.1, hA])
  · exact ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) hAY
      (continuousOn_mertensErrorMajorant C
        (A := A) (Y := Y) (by linarith [hA]))

lemma abs_mertensErrorKernel_le (C : ℝ) (hC : 0 ≤ C)
    {A Y x : ℝ} (hA : 2 ≤ A) (hx : x ∈ Icc A Y)
    (hTheta :
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |mertensErrorKernel x| ≤
      mertensErrorMajorant C x := by
  have hx2 : 2 ≤ x := hA.trans hx.1
  have hx0 : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx2
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have hlogplus : 0 ≤ Real.log x + 1 := by linarith
  have hlogthree :
      Real.log x + 1 ≤ 3 * Real.log x := by linarith
  unfold mertensErrorKernel mertensErrorMajorant
  rw [abs_div, abs_mul, abs_of_nonneg hlogplus,
    abs_of_pos
      (mul_pos (sq_pos_of_pos hx0)
        (sq_pos_of_pos hlogpos))]
  calc
    |thetaError x| * (Real.log x + 1) /
        (x ^ 2 * Real.log x ^ 2) ≤
      (C * x / Real.log x ^ 3) *
          (3 * Real.log x) /
        (x ^ 2 * Real.log x ^ 2) := by
      gcongr
    _ = 3 * C / (x * Real.log x ^ 4) := by
      field_simp [ne_of_gt hx0, hlog0]

lemma abs_logReciprocalErrorKernel_le (C : ℝ)
    (hC : 0 ≤ C) {A Y x : ℝ} (hA : 2 ≤ A)
    (hx : x ∈ Icc A Y)
    (hTheta :
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |logReciprocalErrorKernel x| ≤
      C / (x * Real.log A ^ 3) := by
  have hxpos : 0 < x := by linarith [hA, hx.1]
  have hApos : 0 < A := by linarith
  have hlogApos : 0 < Real.log A :=
    Real.log_pos (by linarith)
  have hlogxpos : 0 < Real.log x :=
    Real.log_pos (by linarith [hx.1, hA])
  have hlogAx : Real.log A ≤ Real.log x :=
    Real.log_le_log hApos hx.1
  have hlogpow :
      Real.log A ^ 3 ≤ Real.log x ^ 3 := by
    gcongr
  unfold logReciprocalErrorKernel
  rw [abs_div, abs_of_pos (sq_pos_of_pos hxpos)]
  calc
    |thetaError x| / x ^ 2 ≤
        (C * x / Real.log x ^ 3) / x ^ 2 := by
      gcongr
    _ = C / (x * Real.log x ^ 3) := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogxpos]
    _ ≤ C / (x * Real.log A ^ 3) := by
      apply div_le_div_of_nonneg_left hC
      · exact mul_pos hxpos (pow_pos hlogApos 3)
      · exact mul_le_mul_of_nonneg_left hlogpow hxpos.le

private lemma intervalIntegrable_logErrorMajorant (C : ℝ)
    {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable
      (fun x => C / (x * Real.log A ^ 3))
      volume A Y := by
  have hlogA0 : Real.log A ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith [hA]))
  apply ContinuousOn.intervalIntegrable_of_Icc
    (μ := volume) hAY
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hA, hx.1]
  exact
    (continuousAt_const.div
      (continuousAt_id.mul continuousAt_const)
      (mul_ne_zero hx0
        (pow_ne_zero 3 hlogA0))).continuousWithinAt

private lemma integral_logErrorMajorant (C : ℝ)
    {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, C / (x * Real.log A ^ 3)) =
      C / Real.log A ^ 3 *
        (Real.log Y - Real.log A) := by
  have hApos : 0 < A := by linarith
  have hYpos : 0 < Y := by linarith
  calc
    (∫ x in A..Y, C / (x * Real.log A ^ 3)) =
        ∫ x in A..Y,
          (C / Real.log A ^ 3) * (1 / x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = (C / Real.log A ^ 3) *
          (∫ x in A..Y, 1 / x) :=
      intervalIntegral.integral_const_mul _ _
    _ = C / Real.log A ^ 3 *
        (Real.log Y - Real.log A) := by
      rw [integral_one_div_of_pos hApos hYpos,
        Real.log_div (ne_of_gt hYpos) (ne_of_gt hApos)]

/-- Explicit positive-cell error for `∑ log p/p`. -/
theorem fullLogReciprocalSum_interval_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      C * (2 + (Real.log (Y : ℝ) -
        Real.log (A : ℝ))) /
        Real.log (A : ℝ) ^ 3 := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogApos : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < A by omega))
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < Y by omega))
  have hlogAY :
      Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt :=
    intervalIntegrable_logReciprocalErrorKernel hAR hAYR
  have hmajorInt :=
    intervalIntegrable_logErrorMajorant C hAR hAYR
  have hIntBound :
      |∫ x in (A : ℝ)..Y,
        logReciprocalErrorKernel x| ≤
        C / Real.log (A : ℝ) ^ 3 *
          (Real.log (Y : ℝ) -
            Real.log (A : ℝ)) := by
    calc
      |∫ x in (A : ℝ)..Y,
          logReciprocalErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y,
            |logReciprocalErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y,
          C / (x * Real.log (A : ℝ) ^ 3) := by
        exact intervalIntegral.integral_mono_on hAYR
          herrInt.abs hmajorInt
          (fun x hx =>
            abs_logReciprocalErrorKernel_le
              C hC hAR hx (hTheta x hx))
      _ = _ := integral_logErrorMajorant C hAR hAYR
  rw [fullLogReciprocalSum_interval_error_identity hA hAY]
  have hThetaA :=
    hTheta (A : ℝ) ⟨le_rfl, hAYR⟩
  have hThetaY :=
    hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩
  have hAterm :
      |thetaError (A : ℝ) / (A : ℝ)| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hApos]
    calc
      _ ≤ (C * (A : ℝ) /
          Real.log (A : ℝ) ^ 3) / (A : ℝ) := by
        gcongr
      _ = _ := by field_simp [ne_of_gt hApos]
  have hYterm :
      |thetaError (Y : ℝ) / (Y : ℝ)| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hYpos]
    calc
      _ ≤ (C * (Y : ℝ) /
          Real.log (Y : ℝ) ^ 3) / (Y : ℝ) := by
        gcongr
      _ = C / Real.log (Y : ℝ) ^ 3 := by
        field_simp [ne_of_gt hYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by
        gcongr
  calc
    |thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y,
          logReciprocalErrorKernel x| ≤
      |thetaError (Y : ℝ) / (Y : ℝ)| +
        |thetaError (A : ℝ) / (A : ℝ)| +
        |∫ x in (A : ℝ)..Y,
          logReciprocalErrorKernel x| := by
      have h₁ := abs_add_le
        (thetaError (Y : ℝ) / (Y : ℝ) -
          thetaError (A : ℝ) / (A : ℝ))
        (∫ x in (A : ℝ)..Y,
          logReciprocalErrorKernel x)
      have h₂ := abs_sub
        (thetaError (Y : ℝ) / (Y : ℝ))
        (thetaError (A : ℝ) / (A : ℝ))
      linarith
    _ ≤ C / Real.log (A : ℝ) ^ 3 +
        C / Real.log (A : ℝ) ^ 3 +
        C / Real.log (A : ℝ) ^ 3 *
          (Real.log (Y : ℝ) -
            Real.log (A : ℝ)) := by
      linarith
    _ = C * (2 + (Real.log (Y : ℝ) -
        Real.log (A : ℝ))) /
        Real.log (A : ℝ) ^ 3 := by
      ring

/-- Explicit two-endpoint error for prime harmonic mass. -/
theorem fullReciprocalSum_interval_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * C / Real.log (A : ℝ) ^ 3 := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono :
        Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by
    linarith
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast
      (show 1 < Y by omega))
  have hlogAY :
      Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt :=
    intervalIntegrable_mertensErrorKernel hAR hAYR
  have hmajorInt :
      IntervalIntegrable (mertensErrorMajorant C) volume
        (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc
      (μ := volume) hAYR
      (continuousOn_mertensErrorMajorant C
        (A := (A : ℝ)) (Y := (Y : ℝ))
        (by linarith [hAR]))
  have habsInt :
      IntervalIntegrable
        (fun x => |mertensErrorKernel x|)
        volume (A : ℝ) (Y : ℝ) :=
    herrInt.abs
  have hIntBound :
      |∫ x in (A : ℝ)..Y,
        mertensErrorKernel x| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    calc
      |∫ x in (A : ℝ)..Y,
          mertensErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y,
            |mertensErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y,
          mertensErrorMajorant C x := by
        exact intervalIntegral.integral_mono_on hAYR
          habsInt hmajorInt
          (fun x hx => abs_mertensErrorKernel_le
            C hC hAR hx (hTheta x hx))
      _ = mertensErrorPrimitive C (Y : ℝ) -
          mertensErrorPrimitive C (A : ℝ) :=
        integral_mertensErrorMajorant C hAR hAYR
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg :
            0 ≤ C / Real.log (Y : ℝ) ^ 3 := by
          positivity
        have heq :
            -C / Real.log (Y : ℝ) ^ 3 -
                (-C / Real.log (A : ℝ) ^ 3) =
              C / Real.log (A : ℝ) ^ 3 -
                C / Real.log (Y : ℝ) ^ 3 := by
          ring
        rw [heq]
        exact sub_le_self _ hnonneg
  rw [fullReciprocalSum_interval_error_identity hA hAY]
  have hThetaA :=
    hTheta (A : ℝ) ⟨le_rfl, hAYR⟩
  have hThetaY :=
    hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩
  have hAterm :
      |thetaError (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ))| ≤
        C / Real.log (A : ℝ) ^ 4 := by
    rw [abs_div,
      abs_of_pos (mul_pos hApos hlogApos)]
    calc
      _ ≤ (C * (A : ℝ) /
          Real.log (A : ℝ) ^ 3) /
          ((A : ℝ) * Real.log (A : ℝ)) := by
        gcongr
      _ = C / Real.log (A : ℝ) ^ 4 := by
        field_simp [ne_of_gt hApos, ne_of_gt hlogApos]
  have hYterm :
      |thetaError (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ))| ≤
        C / Real.log (A : ℝ) ^ 4 := by
    rw [abs_div,
      abs_of_pos (mul_pos hYpos hlogYpos)]
    calc
      _ ≤ (C * (Y : ℝ) /
          Real.log (Y : ℝ) ^ 3) /
          ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
      _ = C / Real.log (Y : ℝ) ^ 4 := by
        field_simp [ne_of_gt hYpos, ne_of_gt hlogYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 4 := by
        gcongr
  calc
    |thetaError (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) -
        thetaError (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
        ∫ x in (A : ℝ)..Y,
          mertensErrorKernel x| ≤
      |thetaError (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ))| +
        |thetaError (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ))| +
        |∫ x in (A : ℝ)..Y,
          mertensErrorKernel x| := by
      calc
        _ ≤
            |thetaError (Y : ℝ) /
                ((Y : ℝ) * Real.log (Y : ℝ)) -
              thetaError (A : ℝ) /
                ((A : ℝ) * Real.log (A : ℝ))| +
              |∫ x in (A : ℝ)..Y,
                mertensErrorKernel x| :=
          abs_add_le _ _
        _ ≤ _ := by
          have hsub := abs_sub
            (thetaError (Y : ℝ) /
              ((Y : ℝ) * Real.log (Y : ℝ)))
            (thetaError (A : ℝ) /
              ((A : ℝ) * Real.log (A : ℝ)))
          linarith
    _ ≤ C / Real.log (A : ℝ) ^ 4 +
        C / Real.log (A : ℝ) ^ 4 +
        C / Real.log (A : ℝ) ^ 3 := by
      linarith
    _ ≤ 5 * C / Real.log (A : ℝ) ^ 3 := by
      have hinv4 :
          1 / Real.log (A : ℝ) ^ 4 ≤
            2 / Real.log (A : ℝ) ^ 3 := by
        have hone :
            1 ≤ 2 * Real.log (A : ℝ) := by
          linarith
        have hpowNonneg :
            0 ≤ Real.log (A : ℝ) ^ 3 :=
          pow_nonneg hlogApos.le 3
        have hmul :=
          mul_le_mul_of_nonneg_right hone hpowNonneg
        apply (div_le_div_iff₀
          (pow_pos hlogApos 4)
          (pow_pos hlogApos 3)).2
        calc
          1 * Real.log (A : ℝ) ^ 3 ≤
              (2 * Real.log (A : ℝ)) *
                Real.log (A : ℝ) ^ 3 := hmul
          _ = 2 * Real.log (A : ℝ) ^ 4 := by ring
      have hscaled :
          C / Real.log (A : ℝ) ^ 4 ≤
            2 * C / Real.log (A : ℝ) ^ 3 := by
        calc
          C / Real.log (A : ℝ) ^ 4 =
              C *
                (1 / Real.log (A : ℝ) ^ 4) := by
            ring
          _ ≤ C *
              (2 / Real.log (A : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left hinv4 hC
          _ = 2 * C /
              Real.log (A : ℝ) ^ 3 := by
            ring
      have hscaled' :
          C / Real.log (A : ℝ) ^ 4 ≤
            2 * (C / Real.log (A : ℝ) ^ 3) := by
        calc
          C / Real.log (A : ℝ) ^ 4 ≤
              2 * C / Real.log (A : ℝ) ^ 3 :=
            hscaled
          _ = 2 *
              (C / Real.log (A : ℝ) ^ 3) := by
            ring
      calc
        C / Real.log (A : ℝ) ^ 4 +
              C / Real.log (A : ℝ) ^ 4 +
              C / Real.log (A : ℝ) ^ 3 ≤
            2 * (C / Real.log (A : ℝ) ^ 3) +
              2 * (C / Real.log (A : ℝ) ^ 3) +
              C / Real.log (A : ℝ) ^ 3 :=
          add_le_add (add_le_add hscaled' hscaled') le_rfl
        _ = 5 * C / Real.log (A : ℝ) ^ 3 := by
          ring

/-- The clean PNT gives one log-cube error constant and threshold. -/
theorem exists_thetaError_log_cube_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x, X₀ ≤ x →
      |thetaError x| ≤ C * x / Real.log x ^ 3 := by
  obtain ⟨C, hC, hbound⟩ :=
    (theta_error_isBigO_log_power (3 : ℝ)).exists_pos
  rw [IsBigOWith, eventually_atTop] at hbound
  obtain ⟨X₀, hX₀⟩ := hbound
  refine ⟨C, hC, max X₀ 2, fun x hx => ?_⟩
  have hxX₀ : X₀ ≤ x :=
    (le_max_left X₀ 2).trans hx
  have hx2 : (2 : ℝ) ≤ x :=
    (le_max_right X₀ 2).trans hx
  have htargetR :
      0 ≤ x / Real.log x ^ ((3 : ℕ) : ℝ) := by
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x :=
      Real.log_pos (by linarith)
    positivity
  have hb := hX₀ x hxX₀
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hb
  calc
    |thetaError x| =
        |Chebyshev.theta x - x| := rfl
    _ ≤ C * |x / Real.log x ^ ((3 : ℕ) : ℝ)| := hb
    _ = C * (x / Real.log x ^ ((3 : ℕ) : ℝ)) := by
      congr 1
      exact abs_of_nonneg htargetR
    _ = C * x / Real.log x ^ 3 := by
      rw [Real.rpow_natCast]
      ring

/-- Uniform two-endpoint harmonic quadrature beyond one cutoff. -/
theorem exists_fullReciprocalSum_interval_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀, hTheta⟩ :=
    exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀
  refine ⟨C, hC, max N 2, fun A Y hA hAY => ?_⟩
  have hA2 : 2 ≤ A :=
    (le_max_right N 2).trans hA
  apply fullReciprocalSum_interval_error_bound
    hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A :=
    (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hNA
  linarith [hx.1]

/-- Uniform two-endpoint first-log-moment quadrature. -/
theorem exists_fullLogReciprocalSum_interval_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullLogReciprocalSum Y -
          fullLogReciprocalSum A -
          (Real.log (Y : ℝ) -
            Real.log (A : ℝ))| ≤
        C * (2 + (Real.log (Y : ℝ) -
          Real.log (A : ℝ))) /
          Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀, hTheta⟩ :=
    exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀
  refine ⟨C, hC, max N 2, fun A Y hA hAY => ?_⟩
  have hA2 : 2 ≤ A :=
    (le_max_right N 2).trans hA
  apply fullLogReciprocalSum_interval_error_bound
    hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A :=
    (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hNA
  linarith [hx.1]

/-! ## Exponential prime bands -/

/-- The integral endpoint just above `exp(Ta)`. -/
def expEndpoint (a : ℝ) (T : ℕ) : ℕ :=
  ⌈Real.exp ((T : ℝ) * a)⌉₊

/-- Harmonic mass of the exponential band `(exp(Ta), exp(Tb)]`,
with endpoints rounded upward. -/
def expBandReciprocalMass (T : ℕ) (a b : ℝ) : ℝ :=
  fullReciprocalSum (expEndpoint b T) -
    fullReciprocalSum (expEndpoint a T)

/-- The normalized logarithmic first moment on the same band. -/
def expBandLogMoment (T : ℕ) (a b : ℝ) : ℝ :=
  (fullLogReciprocalSum (expEndpoint b T) -
    fullLogReciprocalSum (expEndpoint a T)) / (T : ℝ)

/-- The analogous band mass with the denominator `p+1`. -/
def expBandShiftedReciprocalMass (T : ℕ) (a b : ℝ) : ℝ :=
  fullShiftedReciprocalSum (expEndpoint b T) -
    fullShiftedReciprocalSum (expEndpoint a T)

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter,
    Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

private lemma reciprocal_sub_shifted_nonneg
    {p : ℕ} (hp : p.Prime) :
    0 ≤ 1 / (p : ℝ) - 1 / ((p : ℝ) + 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  field_simp [hpR.ne', hpR1.ne']
  linarith

private lemma reciprocal_sub_shifted_le_square
    {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) - 1 / ((p : ℝ) + 1) ≤
      1 / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  field_simp [hpR.ne', hpR1.ne']
  nlinarith

/-- Replacing `1/p` by `1/(p+1)` on `(A,Y]` costs at most the
square-reciprocal tail `1/A`. -/
theorem reciprocal_interval_sub_shifted_abs_le
    (A Y : ℕ) (hA : 1 ≤ A) (hAY : A ≤ Y) :
    |(fullReciprocalSum Y - fullReciprocalSum A) -
        (fullShiftedReciprocalSum Y -
          fullShiftedReciprocalSum A)| ≤
      1 / (A : ℝ) := by
  have hsub := primesUpTo_mono hAY
  have hrec :
      fullReciprocalSum Y - fullReciprocalSum A =
        ∑ p ∈ primesUpTo Y \ primesUpTo A,
          1 / (p : ℝ) := by
    simpa only [fullReciprocalSum] using
      (Finset.sum_sdiff_eq_sub
        (f := fun p : ℕ => 1 / (p : ℝ)) hsub).symm
  have hshift :
      fullShiftedReciprocalSum Y -
          fullShiftedReciprocalSum A =
        ∑ p ∈ primesUpTo Y \ primesUpTo A,
          1 / ((p : ℝ) + 1) := by
    simpa only [fullShiftedReciprocalSum] using
      (Finset.sum_sdiff_eq_sub
        (f := fun p : ℕ => 1 / ((p : ℝ) + 1)) hsub).symm
  rw [hrec, hshift, ← Finset.sum_sub_distrib]
  have hnonneg :
      0 ≤ ∑ p ∈ primesUpTo Y \ primesUpTo A,
        (1 / (p : ℝ) - 1 / ((p : ℝ) + 1)) := by
    apply Finset.sum_nonneg
    intro p hpMem
    apply reciprocal_sub_shifted_nonneg
    have hpY : p ≤ Y ∧ p.Prime := by
      simpa [primesUpTo] using (Finset.mem_sdiff.mp hpMem).1
    exact hpY.2
  rw [abs_of_nonneg hnonneg]
  calc
    (∑ p ∈ primesUpTo Y \ primesUpTo A,
        (1 / (p : ℝ) - 1 / ((p : ℝ) + 1))) ≤
        reciprocalSquareSumBetween A Y := by
      apply Finset.sum_le_sum
      intro p hpMem
      apply reciprocal_sub_shifted_le_square
      have hpY : p ≤ Y ∧ p.Prime := by
        simpa [primesUpTo] using (Finset.mem_sdiff.mp hpMem).1
      exact hpY.2
    _ ≤ 1 / (A : ℝ) :=
      reciprocalSquareSumBetween_le A Y hA

lemma expEndpoint_mono {a b : ℝ} (hab : a ≤ b) (T : ℕ) :
    expEndpoint a T ≤ expEndpoint b T := by
  apply Nat.ceil_le_ceil
  rw [Real.exp_le_exp]
  exact mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg T)

lemma expEndpoint_tendsto_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (expEndpoint a) atTop atTop := by
  apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
  have hexp :
      Tendsto (fun T : ℕ => Real.exp ((T : ℝ) * a))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (tendsto_natCast_atTop_atTop.atTop_mul_const ha)
  simpa only [expEndpoint] using
    Filter.tendsto_atTop_mono
      (fun T : ℕ => Nat.le_ceil
        (Real.exp ((T : ℝ) * a))) hexp

private lemma expEndpoint_log_error_nonneg
    {a : ℝ} (T : ℕ) :
    0 ≤ Real.log (expEndpoint a T : ℝ) -
      (T : ℝ) * a := by
  have hceil :
      Real.exp ((T : ℝ) * a) ≤
        (expEndpoint a T : ℝ) :=
    Nat.le_ceil _
  have hceilPos : (0 : ℝ) < expEndpoint a T := by
    exact_mod_cast
      (Nat.ceil_pos.mpr
        (Real.exp_pos ((T : ℝ) * a)))
  have hlog :=
    Real.log_le_log (Real.exp_pos _) hceil
  rw [Real.log_exp] at hlog
  linarith

private lemma expEndpoint_log_error_le
    {a : ℝ} (ha : 0 < a) (T : ℕ) :
    Real.log (expEndpoint a T : ℝ) -
        (T : ℝ) * a ≤ Real.log 2 := by
  have hexpOne :
      (1 : ℝ) ≤ Real.exp ((T : ℝ) * a) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (Nat.cast_nonneg T) ha.le
  have hceilLt :
      (expEndpoint a T : ℝ) <
        Real.exp ((T : ℝ) * a) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hceilLe :
      (expEndpoint a T : ℝ) ≤
        2 * Real.exp ((T : ℝ) * a) := by
    linarith
  have hceilPos : (0 : ℝ) < expEndpoint a T := by
    exact_mod_cast
      (Nat.ceil_pos.mpr
        (Real.exp_pos ((T : ℝ) * a)))
  have hlog :=
    Real.log_le_log hceilPos hceilLe
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  linarith

lemma expEndpoint_log_div_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℕ =>
        Real.log (expEndpoint a T : ℝ) / (T : ℝ))
      atTop (𝓝 a) := by
  have hupper :
      Tendsto (fun T : ℕ => Real.log 2 / (T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      tendsto_natCast_atTop_atTop
  have herr :
      Tendsto
        (fun T : ℕ =>
          (Real.log (expEndpoint a T : ℝ) -
            (T : ℝ) * a) / (T : ℝ))
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact div_nonneg
        (expEndpoint_log_error_nonneg T)
        (Nat.cast_nonneg T)
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact div_le_div_of_nonneg_right
        (expEndpoint_log_error_le ha T)
        (Nat.cast_nonneg T)
    · exact hupper
  have hadd := herr.add_const a
  have heq :
      (fun T : ℕ =>
        (Real.log (expEndpoint a T : ℝ) -
          (T : ℝ) * a) / (T : ℝ) + a) =ᶠ[atTop]
      (fun T : ℕ =>
        Real.log (expEndpoint a T : ℝ) / (T : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hTR : (T : ℝ) ≠ 0 := by
      exact_mod_cast hT.ne'
    field_simp [hTR]
    ring
  simpa only [zero_add] using hadd.congr' heq

lemma expEndpoint_log_tendsto_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℕ => Real.log (expEndpoint a T : ℝ))
      atTop atTop :=
  Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_iff.mpr
      (expEndpoint_tendsto_atTop ha))

lemma expEndpoint_log_ratio_tendsto {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun T : ℕ =>
        Real.log (expEndpoint b T : ℝ) /
          Real.log (expEndpoint a T : ℝ))
      atTop (𝓝 (b / a)) := by
  have hdiv :=
    (expEndpoint_log_div_tendsto hb).div
      (expEndpoint_log_div_tendsto ha) ha.ne'
  apply hdiv.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (T : ℝ) ≠ 0 := by
    exact_mod_cast hT.ne'
  change
    (Real.log (expEndpoint b T : ℝ) / (T : ℝ)) /
        (Real.log (expEndpoint a T : ℝ) / (T : ℝ)) =
      Real.log (expEndpoint b T : ℝ) /
        Real.log (expEndpoint a T : ℝ)
  exact div_div_div_cancel_right₀ hTR _ _

lemma expEndpoint_logLog_sub_tendsto {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun T : ℕ =>
        Real.log (Real.log (expEndpoint b T : ℝ)) -
          Real.log (Real.log (expEndpoint a T : ℝ)))
      atTop (𝓝 (Real.log (b / a))) := by
  have hratio :=
    (expEndpoint_log_ratio_tendsto ha hb).log
      (div_ne_zero hb.ne' ha.ne')
  apply hratio.congr'
  filter_upwards [
    (expEndpoint_log_tendsto_atTop ha).eventually
      (eventually_gt_atTop (0 : ℝ)),
    (expEndpoint_log_tendsto_atTop hb).eventually
      (eventually_gt_atTop (0 : ℝ))]
      with T hloga hlogb
  rw [Real.log_div hlogb.ne' hloga.ne']

lemma expEndpoint_log_sub_div_tendsto {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun T : ℕ =>
        (Real.log (expEndpoint b T : ℝ) -
          Real.log (expEndpoint a T : ℝ)) / (T : ℝ))
      atTop (𝓝 (b - a)) := by
  have hsub :=
    (expEndpoint_log_div_tendsto hb).sub
      (expEndpoint_log_div_tendsto ha)
  apply hsub.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (T : ℝ) ≠ 0 := by
    exact_mod_cast hT.ne'
  field_simp [hTR]

/-- Prime harmonic mass on a fixed positive exponential band converges
to its logarithmic-coordinate mass. -/
theorem expBandReciprocalMass_tendsto {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun T : ℕ => expBandReciprocalMass T a b)
      atTop (𝓝 (Real.log (b / a))) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  have hlogTop := expEndpoint_log_tendsto_atTop ha
  have hlogCube :
      Tendsto
        (fun T : ℕ =>
          Real.log (expEndpoint a T : ℝ) ^ 3)
        atTop atTop := by
    simpa [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_atTop
        (by norm_num : (0 : ℝ) < 3)).comp hlogTop
  have hupper :
      Tendsto
        (fun T : ℕ =>
          5 * C /
            Real.log (expEndpoint a T : ℝ) ^ 3)
        atTop (𝓝 0) :=
    hlogCube.const_div_atTop (5 * C)
  have herr :
      Tendsto
        (fun T : ℕ =>
          expBandReciprocalMass T a b -
            (Real.log
                (Real.log (expEndpoint b T : ℝ)) -
              Real.log
                (Real.log (expEndpoint a T : ℝ))))
        atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero'
    · exact Eventually.of_forall (fun T => abs_nonneg _)
    · filter_upwards [
        (expEndpoint_tendsto_atTop ha).eventually
          (eventually_ge_atTop X₀)] with T hT
      simpa only [expBandReciprocalMass] using
        hquad (expEndpoint a T) (expEndpoint b T) hT
          (expEndpoint_mono hab T)
    · simpa only [abs_zero] using hupper
  have hmain :=
    expEndpoint_logLog_sub_tendsto ha hb
  have hadd := herr.add hmain
  have heq :
      (fun T : ℕ =>
        (expBandReciprocalMass T a b -
            (Real.log
                (Real.log (expEndpoint b T : ℝ)) -
              Real.log
                (Real.log (expEndpoint a T : ℝ)))) +
          (Real.log
              (Real.log (expEndpoint b T : ℝ)) -
            Real.log
              (Real.log (expEndpoint a T : ℝ)))) =ᶠ[atTop]
      (fun T : ℕ => expBandReciprocalMass T a b) :=
    Eventually.of_forall (fun T => by ring)
  simpa only [zero_add] using hadd.congr' heq

/-- The normalized first logarithmic moment on a fixed positive
exponential band converges to its ordinary coordinate length. -/
theorem expBandLogMoment_tendsto {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun T : ℕ => expBandLogMoment T a b)
      atTop (𝓝 (b - a)) := by
  have hb : 0 < b := ha.trans_le hab
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullLogReciprocalSum_interval_error_bound
  have hmain :=
    expEndpoint_log_sub_div_tendsto ha hb
  have htwo :
      Tendsto (fun T : ℕ => (2 : ℝ) / (T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      tendsto_natCast_atTop_atTop
  have hinner :
      Tendsto
        (fun T : ℕ =>
          (2 + (Real.log (expEndpoint b T : ℝ) -
            Real.log (expEndpoint a T : ℝ))) / (T : ℝ))
        atTop (𝓝 (b - a)) := by
    have hadd := htwo.add hmain
    have heq :
        (fun T : ℕ =>
          (2 : ℝ) / (T : ℝ) +
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ)) / (T : ℝ)) =ᶠ[atTop]
        (fun T : ℕ =>
          (2 + (Real.log (expEndpoint b T : ℝ) -
            Real.log (expEndpoint a T : ℝ))) / (T : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      have hTR : (T : ℝ) ≠ 0 := by
        exact_mod_cast hT.ne'
      field_simp [hTR]
    simpa only [zero_add] using hadd.congr' heq
  have hnum :
      Tendsto
        (fun T : ℕ =>
          C * ((2 +
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ)))
        atTop (𝓝 (C * (b - a))) :=
    hinner.const_mul C
  have hlogTop := expEndpoint_log_tendsto_atTop ha
  have hlogCube :
      Tendsto
        (fun T : ℕ =>
          Real.log (expEndpoint a T : ℝ) ^ 3)
        atTop atTop := by
    simpa [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_atTop
        (by norm_num : (0 : ℝ) < 3)).comp hlogTop
  have hupper :
      Tendsto
        (fun T : ℕ =>
          (C * ((2 +
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ))) /
            Real.log (expEndpoint a T : ℝ) ^ 3)
        atTop (𝓝 0) :=
    hnum.div_atTop hlogCube
  have herr :
      Tendsto
        (fun T : ℕ =>
          (fullLogReciprocalSum (expEndpoint b T) -
            fullLogReciprocalSum (expEndpoint a T) -
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ))
        atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero'
    · exact Eventually.of_forall (fun T => abs_nonneg _)
    · filter_upwards [
        (expEndpoint_tendsto_atTop ha).eventually
          (eventually_ge_atTop X₀),
        eventually_gt_atTop 0] with T hcut hT
      have hTR : (0 : ℝ) < (T : ℝ) := by
        exact_mod_cast hT
      have hbound :=
        hquad (expEndpoint a T) (expEndpoint b T) hcut
          (expEndpoint_mono hab T)
      change
        |(fullLogReciprocalSum (expEndpoint b T) -
            fullLogReciprocalSum (expEndpoint a T) -
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ)| ≤
          (C * ((2 +
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ))) /
            Real.log (expEndpoint a T : ℝ) ^ 3
      rw [abs_div, abs_of_pos hTR]
      calc
        |fullLogReciprocalSum (expEndpoint b T) -
              fullLogReciprocalSum (expEndpoint a T) -
              (Real.log (expEndpoint b T : ℝ) -
                Real.log (expEndpoint a T : ℝ))| /
            (T : ℝ) ≤
          (C * (2 +
              (Real.log (expEndpoint b T : ℝ) -
                Real.log (expEndpoint a T : ℝ))) /
              Real.log (expEndpoint a T : ℝ) ^ 3) /
            (T : ℝ) :=
          div_le_div_of_nonneg_right hbound hTR.le
        _ =
          (C * ((2 +
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ))) /
            Real.log (expEndpoint a T : ℝ) ^ 3 := by
          ring
    · simpa only [abs_zero] using hupper
  have hadd := herr.add hmain
  have heq :
      (fun T : ℕ =>
        (fullLogReciprocalSum (expEndpoint b T) -
            fullLogReciprocalSum (expEndpoint a T) -
            (Real.log (expEndpoint b T : ℝ) -
              Real.log (expEndpoint a T : ℝ))) / (T : ℝ) +
          (Real.log (expEndpoint b T : ℝ) -
            Real.log (expEndpoint a T : ℝ)) / (T : ℝ)) =ᶠ[atTop]
      (fun T : ℕ => expBandLogMoment T a b) := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hTR : (T : ℝ) ≠ 0 := by
      exact_mod_cast hT.ne'
    simp only [expBandLogMoment]
    field_simp [hTR]
    ring
  simpa only [zero_add] using hadd.congr' heq

/-- The same harmonic-band limit holds after replacing every `1/p` by
`1/(p+1)`; the difference is killed by the square-reciprocal tail. -/
theorem expBandShiftedReciprocalMass_tendsto {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun T : ℕ => expBandShiftedReciprocalMass T a b)
      atTop (𝓝 (Real.log (b / a))) := by
  have hcastTop :
      Tendsto (fun T : ℕ => (expEndpoint a T : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_iff.mpr
      (expEndpoint_tendsto_atTop ha)
  have hupper :
      Tendsto
        (fun T : ℕ => (1 : ℝ) / (expEndpoint a T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hcastTop
  have hdiff :
      Tendsto
        (fun T : ℕ =>
          expBandShiftedReciprocalMass T a b -
            expBandReciprocalMass T a b)
        atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero'
    · exact Eventually.of_forall (fun T => abs_nonneg _)
    · exact Eventually.of_forall (fun T => by
        change
          |expBandShiftedReciprocalMass T a b -
              expBandReciprocalMass T a b| ≤
            1 / (expEndpoint a T : ℝ)
        rw [abs_sub_comm]
        simpa only [expBandReciprocalMass,
          expBandShiftedReciprocalMass] using
          reciprocal_interval_sub_shifted_abs_le
            (expEndpoint a T) (expEndpoint b T)
            (Nat.ceil_pos.mpr (Real.exp_pos _))
            (expEndpoint_mono hab T))
    · simpa only [abs_zero] using hupper
  have hmass := expBandReciprocalMass_tendsto ha hab
  have hadd := hdiff.add hmass
  have heq :
      (fun T : ℕ =>
        (expBandShiftedReciprocalMass T a b -
          expBandReciprocalMass T a b) +
          expBandReciprocalMass T a b) =ᶠ[atTop]
      (fun T : ℕ => expBandShiftedReciprocalMass T a b) :=
    Eventually.of_forall (fun T => by ring)
  simpa only [zero_add] using hadd.congr' heq

end Erdos536.PrimeSums
