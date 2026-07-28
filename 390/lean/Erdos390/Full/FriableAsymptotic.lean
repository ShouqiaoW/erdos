import Erdos390.Full.DickmanBasic
import Erdos390.Full.StructuredCells
import Erdos390.Full.Scale
import PrimeNumberTheoremAnd.MediumPNT
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Friable counts on the Erdős 390 scale

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's actual finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace Erdos390.Full.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/

/-- The medium PNT error for `ψ` is `O(x / log(x)^A)` for every fixed real
power `A`. -/
theorem psi_error_isBigO_log_power (A : ℝ) :
    (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ A) := by
  obtain ⟨c, hc, hPNT⟩ := MediumPNT
  apply hPNT.trans
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atTop := by
    exact tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10) |>.comp
      Real.tendsto_log_atTop
  have hdecay :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-10 * A)).comp_tendsto hpow
  have hdecay' :
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =O[atTop] (fun x : ℝ => (Real.log x) ^ (-A)) := by
    apply hdecay.isBigO.congr' (Eventually.of_forall fun x => rfl)
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))]
      with x hx
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hx]
    congr 2
    ring
  have hmul := (isBigO_refl (fun x : ℝ => x) atTop).mul hdecay'
  apply hmul.congr' (Eventually.of_forall fun x => rfl)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- The prime-power correction `√x log x` is smaller than the same arbitrary
fixed logarithmic PNT scale. -/
theorem sqrt_mul_log_isBigO_log_power (A : ℝ) :
    (fun x : ℝ => Real.sqrt x * Real.log x) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ A) := by
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 1 / 2)).isBigO
  let common : ℝ → ℝ := fun x => x ^ ((1 : ℝ) / 2) / (Real.log x) ^ A
  have hmul := hlog.mul (isBigO_refl common atTop)
  apply hmul.congr'
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hlogx hx
    dsimp [common]
    rw [Real.sqrt_eq_rpow, Real.rpow_add hlogx]
    field_simp
    simp [Real.rpow_one]
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hlogx hx
    dsimp [common]
    calc
      x ^ ((1 : ℝ) / 2) * (x ^ ((1 : ℝ) / 2) / Real.log x ^ A) =
          (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) / Real.log x ^ A := by ring
      _ = x ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2) / Real.log x ^ A := by
        rw [Real.rpow_add hx]
      _ = x / Real.log x ^ A := by norm_num [Real.rpow_one]

/-- Quantitative PNT for Chebyshev's `θ`, at every fixed logarithmic power.
This is the form used by partial summation over primes. -/
theorem theta_error_isBigO_log_power (A : ℝ) :
    (Chebyshev.theta - id) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ A) := by
  have hraw :
      (Chebyshev.theta - Chebyshev.psi) =O[atTop]
        (fun x : ℝ => Real.sqrt x * Real.log x) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hnonneg : 0 ≤ Real.sqrt x * Real.log x :=
      mul_nonneg (Real.sqrt_nonneg x) (Real.log_nonneg hx)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm,
      Real.norm_of_nonneg hnonneg, mul_assoc] using
      Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
  have hdiff := hraw.trans (sqrt_mul_log_isBigO_log_power A)
  have hadd := hdiff.add (psi_error_isBigO_log_power A)
  apply hadd.congr' (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => rfl)
  simp only [Pi.sub_apply, id_eq]
  ring

/-- The actual finite Chebyshev prime sum, written with the same
`Nat.primesBelow` finset used by the friable recurrence. -/
noncomputable def primeLogSumUpTo (X : ℕ) : ℝ :=
  ∑ p ∈ (X + 1).primesBelow, Real.log (p : ℝ)

theorem primeLogSumUpTo_eq_theta (X : ℕ) :
    primeLogSumUpTo X = Chebyshev.theta (X : ℝ) := by
  have hfin : (X + 1).primesBelow = (Finset.Ioc 0 X).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpX, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
    · rintro ⟨⟨_, hpX⟩, hp⟩
      exact ⟨by omega, hp⟩
  rw [primeLogSumUpTo, hfin, Chebyshev.theta]
  simp only [Nat.floor_natCast]

/-- Quantitative PNT for the precise natural-number prime finset used below.
-/
theorem primeLogSumUpTo_error_isBigO_log_power (A : ℝ) :
    (fun X : ℕ => primeLogSumUpTo X - (X : ℝ)) =O[atTop]
      (fun X : ℕ => (X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  have h := (theta_error_isBigO_log_power A).comp_tendsto
    tendsto_natCast_atTop_atTop
  apply h.congr' (Eventually.of_forall fun X => ?_)
    (Eventually.of_forall fun X => rfl)
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, primeLogSumUpTo_eq_theta]

/-- An explicit eventual inequality extracted from the quantitative PNT.  In
particular, later uses may choose the constant and threshold before starting
the finite de Bruijn induction. -/
theorem exists_primeLogSumUpTo_error_bound (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  obtain ⟨C, hC, hbound⟩ :=
    (primeLogSumUpTo_error_isBigO_log_power A).exists_pos
  rw [IsBigOWith, eventually_atTop] at hbound
  obtain ⟨X₀, hX₀⟩ := hbound
  refine ⟨C, hC, max X₀ 2, fun X hX => ?_⟩
  have hXX₀ : X₀ ≤ X := (le_max_left X₀ 2).trans hX
  have hX2 : 2 ≤ X := (le_max_right X₀ 2).trans hX
  have htarget : 0 ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
    positivity
  simpa only [Real.norm_eq_abs, Real.norm_of_nonneg htarget] using
    hX₀ X hXX₀

/-- The logarithmically weighted prime sum on the half-open natural interval
`z < p ≤ y`. -/
noncomputable def primeLogSumInterval (z y : ℕ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
    Real.log (p : ℝ)

theorem primeLogSumInterval_eq_sub {z y : ℕ} (hzy : z ≤ y) :
    primeLogSumInterval z y = primeLogSumUpTo y - primeLogSumUpTo z := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum := Finset.sum_sdiff
    (f := fun p : ℕ => Real.log (p : ℝ)) hsubset
  simp only [primeLogSumInterval, primeLogSumUpTo] at hsum ⊢
  linarith

/-- Uniform two-endpoint form of the quantitative PNT.  This is the exact
finite interval estimate used on each cell of a prime Stieltjes partition. -/
theorem primeLogSumInterval_error_bound {A C : ℝ} {X₀ z y : ℕ}
    (hbound : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A))
    (hz : X₀ ≤ z) (hy : X₀ ≤ y) (hzy : z ≤ y) :
    |primeLogSumInterval z y - ((y : ℝ) - (z : ℝ))| ≤
      C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A +
        (z : ℝ) / (Real.log (z : ℝ)) ^ A) := by
  rw [primeLogSumInterval_eq_sub hzy]
  calc
    |(primeLogSumUpTo y - primeLogSumUpTo z) - ((y : ℝ) - (z : ℝ))| =
        |(primeLogSumUpTo y - (y : ℝ)) -
          (primeLogSumUpTo z - (z : ℝ))| := by ring_nf
    _ ≤ |primeLogSumUpTo y - (y : ℝ)| +
        |primeLogSumUpTo z - (z : ℝ)| := abs_sub _ _
    _ ≤ C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A) +
        C * ((z : ℝ) / (Real.log (z : ℝ)) ^ A) :=
      add_le_add (hbound y hy) (hbound z hz)
    _ = _ := by ring

/-- The point mass of the Chebyshev `θ` measure at an integer. -/
noncomputable def primeLogIncrement (m : ℕ) : ℝ :=
  if m.Prime then Real.log (m : ℝ) else 0

theorem sum_range_primeLogIncrement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), primeLogIncrement m =
      primeLogSumUpTo n := by
  rw [primeLogSumUpTo]
  simp only [primeLogIncrement]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesBelow]
  · intro p hp
    rfl

/-- A prime Stieltjes sum, still written as a finite sum. -/
noncomputable def primeThetaWeightedInterval (f : ℕ → ℝ) (z y : ℕ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
    f p * Real.log (p : ℝ)

theorem primeThetaWeightedInterval_eq_Ioc (f : ℕ → ℝ) {z y : ℕ} :
    primeThetaWeightedInterval f z y =
      ∑ m ∈ Finset.Ioc z y, f m * primeLogIncrement m := by
  rw [primeThetaWeightedInterval]
  simp only [primeLogIncrement, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesBelow,
      Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpy, hp⟩, hpz⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hnot
      apply hpz
      exact ⟨by omega, hp⟩
    · rintro ⟨⟨hzp, hpy⟩, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
  · intro p hp
    rfl

/-- Exact Abel summation for a prime Stieltjes sum.  No asymptotic statement
is hidden here: the cumulative mass is the actual finite `primeLogSumUpTo`.
This is the arithmetic identity to which the quantitative PNT error is
applied. -/
theorem primeThetaWeightedInterval_by_parts (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    primeThetaWeightedInterval f z y =
      f y * primeLogSumUpTo y - f (z + 1) * primeLogSumUpTo z -
        ∑ m ∈ Finset.Ioc z (y - 1),
          (f (m + 1) - f m) * primeLogSumUpTo m := by
  rw [primeThetaWeightedInterval_eq_Ioc f]
  have hparts := Finset.sum_Ioc_by_parts f primeLogIncrement hzy
  simpa only [smul_eq_mul, sum_range_primeLogIncrement,
    Nat.add_sub_cancel] using hparts

/-- Abel's main term after replacing the cumulative prime mass `θ(m)` by its
PNT main term `m`.  This is deliberately kept discrete; the subsequent
comparison with a Dickman integral is a separate Riemann-sum step. -/
noncomputable def integerAbelMain (f : ℕ → ℝ) (z y : ℕ) : ℝ :=
  f y * (y : ℝ) - f (z + 1) * (z : ℝ) -
    ∑ m ∈ Finset.Ioc z (y - 1),
      (f (m + 1) - f m) * (m : ℝ)

/-- Unit mass on the positive integers.  Its cumulative mass through `n` is
exactly `n`, matching the main term of `θ(n)`. -/
def positiveIncrement (m : ℕ) : ℝ := if m = 0 then 0 else 1

theorem sum_range_positiveIncrement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), positiveIncrement m = (n : ℝ) := by
  induction n with
  | zero => simp [positiveIncrement]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [positiveIncrement]

/-- Consequently the discrete Abel main term is just the ordinary integer
Riemann sum of the test weight. -/
theorem integerAbelMain_eq_sum_Ioc (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    integerAbelMain f z y = ∑ m ∈ Finset.Ioc z y, f m := by
  have hparts := Finset.sum_Ioc_by_parts f positiveIncrement hzy
  have hlhs : (∑ m ∈ Finset.Ioc z y, f m * positiveIncrement m) =
      ∑ m ∈ Finset.Ioc z y, f m := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by
      rw [Finset.mem_Ioc] at hm
      omega
    simp [positiveIncrement, hm0]
  simp only [smul_eq_mul] at hparts
  rw [hlhs] at hparts
  simpa only [sum_range_positiveIncrement,
    Nat.add_sub_cancel, integerAbelMain, mul_one] using hparts.symm

/-- Shift a sum over `z < m ≤ y` to the adjacent unit cells
`z ≤ k < y`. -/
theorem sum_Ioc_shift (f : ℕ → ℝ) {z y : ℕ} :
    ∑ m ∈ Finset.Ioc z y, f m =
      ∑ k ∈ Finset.Ico z y, f (k + 1) := by
  have hfin : (Finset.Ico z y).image (fun k => k + 1) =
      Finset.Ioc z y := by
    ext m
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    · rintro ⟨k, ⟨hzk, hky⟩, rfl⟩
      omega
    · rintro ⟨hzm, hmy⟩
      refine ⟨m - 1, ?_, by omega⟩
      omega
  have hinj : Set.InjOn (fun k : ℕ => k + 1)
      (Finset.Ico z y : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  rw [← hfin, Finset.sum_image hinj]

/-- Exact decomposition of an integer Riemann-sum error into its unit-cell
errors. -/
theorem sum_sub_integral_identity (f : ℝ → ℝ) {z y : ℕ}
    (hzy : z ≤ y)
    (hint : ∀ k ∈ Set.Ico z y,
      IntervalIntegrable f MeasureTheory.volume (k : ℝ) (k + 1 : ℕ)) :
    (∑ m ∈ Finset.Ioc z y, f m) -
        ∫ t in (z : ℝ)..(y : ℝ), f t =
      ∑ k ∈ Finset.Ico z y,
        (f (k + 1) - ∫ t in (k : ℝ)..(k + 1 : ℕ), f t) := by
  rw [sum_Ioc_shift (fun m => f m)]
  have hintsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := f) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ)) hzy hint
  simp only [Nat.cast_add, Nat.cast_one] at hintsum
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hintsum, Finset.sum_sub_distrib]

/-- A quantitative Riemann-sum estimate from a supplied oscillation on each
unit cell.  Later the one-Lipschitz Dickman bound supplies `hosc` for the
specific de Bruijn kernel. -/
theorem sum_integral_error_bound (f : ℝ → ℝ) (e : ℕ → ℝ)
    {z y : ℕ} (hzy : z ≤ y)
    (hint : ∀ k ∈ Set.Ico z y,
      IntervalIntegrable f MeasureTheory.volume (k : ℝ) (k + 1 : ℕ))
    (hosc : ∀ k ∈ Finset.Ico z y,
      ∀ t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
        |f (k + 1) - f t| ≤ e k) :
    |(∑ m ∈ Finset.Ioc z y, f m) -
        ∫ t in (z : ℝ)..(y : ℝ), f t| ≤
      ∑ k ∈ Finset.Ico z y, e k := by
  rw [sum_sub_integral_identity f hzy hint]
  calc
    |∑ k ∈ Finset.Ico z y,
        (f (k + 1) - ∫ t in (k : ℝ)..(k + 1 : ℕ), f t)| ≤
        ∑ k ∈ Finset.Ico z y,
          |f (k + 1) - ∫ t in (k : ℝ)..(k + 1 : ℕ), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico z y, e k := by
      apply Finset.sum_le_sum
      intro k hk
      have hconst :
          (∫ _t in (k : ℝ)..(k + 1 : ℕ), f (k + 1)) =
            f (k + 1) := by
        simp
      rw [← hconst, ← intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable _ _)
        (hint k (by simpa using hk))]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => f (k + 1) - f t) (C := e k)
        (a := (k : ℝ)) (b := (k + 1 : ℕ)) (fun t ht => ?_)
      · simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_left, abs_one, mul_one] using hnorm
      · apply hosc k hk t
        have ht' := Set.uIoc_subset_uIcc ht
        rw [Set.uIcc_of_le
          (by norm_num : (k : ℝ) ≤ (k + 1 : ℕ))] at ht'
        exact ht'

/-- Exact decomposition of the prime Stieltjes error into endpoint errors and
the discrete variation of the test weight. -/
theorem primeThetaWeightedInterval_error_identity (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    primeThetaWeightedInterval f z y - integerAbelMain f z y =
      f y * (primeLogSumUpTo y - (y : ℝ)) -
      f (z + 1) * (primeLogSumUpTo z - (z : ℝ)) -
      ∑ m ∈ Finset.Ioc z (y - 1),
        (f (m + 1) - f m) *
          (primeLogSumUpTo m - (m : ℝ)) := by
  rw [primeThetaWeightedInterval_by_parts f hzy]
  simp only [integerAbelMain]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Total-variation estimate for the prime Stieltjes error.  Together with
`exists_primeLogSumUpTo_error_bound`, this is a quantitative and fully finite
partial-summation interface; no prime asymptotic is assumed by callers. -/
theorem primeThetaWeightedInterval_error_bound (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    |primeThetaWeightedInterval f z y - integerAbelMain f z y| ≤
      |f y| * |primeLogSumUpTo y - (y : ℝ)| +
      |f (z + 1)| * |primeLogSumUpTo z - (z : ℝ)| +
      ∑ m ∈ Finset.Ioc z (y - 1),
        |f (m + 1) - f m| *
          |primeLogSumUpTo m - (m : ℝ)| := by
  rw [primeThetaWeightedInterval_error_identity f hzy]
  calc
    |f y * (primeLogSumUpTo y - (y : ℝ)) -
        f (z + 1) * (primeLogSumUpTo z - (z : ℝ)) -
        ∑ m ∈ Finset.Ioc z (y - 1),
          (f (m + 1) - f m) *
            (primeLogSumUpTo m - (m : ℝ))| ≤
      |f y * (primeLogSumUpTo y - (y : ℝ)) -
        f (z + 1) * (primeLogSumUpTo z - (z : ℝ))| +
        |∑ m ∈ Finset.Ioc z (y - 1),
          (f (m + 1) - f m) *
            (primeLogSumUpTo m - (m : ℝ))| := abs_sub _ _
    _ ≤ (|f y * (primeLogSumUpTo y - (y : ℝ))| +
        |f (z + 1) * (primeLogSumUpTo z - (z : ℝ))|) +
        ∑ m ∈ Finset.Ioc z (y - 1),
          |(f (m + 1) - f m) *
            (primeLogSumUpTo m - (m : ℝ))| := by
      apply add_le_add
      · exact abs_sub _ _
      · exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul]

/-- The preceding variation estimate with the quantitative PNT substituted at
every endpoint.  The single threshold `X₀` is uniform over the whole finite
prime interval. -/
theorem primeThetaWeightedInterval_pnt_bound (f : ℕ → ℝ)
    {A C : ℝ} {X₀ z y : ℕ}
    (hbound : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A))
    (hz : X₀ ≤ z) (hzy : z < y) :
    |primeThetaWeightedInterval f z y - integerAbelMain f z y| ≤
      |f y| * (C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A)) +
      |f (z + 1)| * (C * ((z : ℝ) / (Real.log (z : ℝ)) ^ A)) +
      ∑ m ∈ Finset.Ioc z (y - 1),
        |f (m + 1) - f m| *
          (C * ((m : ℝ) / (Real.log (m : ℝ)) ^ A)) := by
  calc
    |primeThetaWeightedInterval f z y - integerAbelMain f z y| ≤
        |f y| * |primeLogSumUpTo y - (y : ℝ)| +
        |f (z + 1)| * |primeLogSumUpTo z - (z : ℝ)| +
        ∑ m ∈ Finset.Ioc z (y - 1),
          |f (m + 1) - f m| *
            |primeLogSumUpTo m - (m : ℝ)| :=
      primeThetaWeightedInterval_error_bound f hzy
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (hbound y (hz.trans hzy.le)) (abs_nonneg (f y))
        · exact mul_le_mul_of_nonneg_left
            (hbound z hz) (abs_nonneg (f (z + 1)))
      · apply Finset.sum_le_sum
        intro m hm
        apply mul_le_mul_of_nonneg_left
        · apply hbound m
          exact hz.trans (Nat.le_of_lt (Finset.mem_Ioc.mp hm).1)
        · exact abs_nonneg (f (m + 1) - f m)

/-! ## Explicit regularity of the finite Dickman kernel -/

/-- The method-of-steps Dickman solution is at most one on the full compact
range used by the friable induction. -/
theorem rho_le_one_of_le_five {x : ℝ} (hx5 : x ≤ 5) :
    rho x ≤ 1 := by
  by_cases hx1 : x ≤ 1
  · rw [rho_eq_one_of_le_one hx1]
  · have hxmem : x ∈ Set.Icc (1 : ℝ) 5 :=
      ⟨le_of_not_ge hx1, hx5⟩
    have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by norm_num
    simpa [rho_one] using
      antitoneOn_rho_one_five hone hxmem hxmem.1

/-- On `[1,5]` the delay-equation integrand lies in `[0,1]`. -/
theorem rho_delay_integrand_bounds {t : ℝ} (ht1 : 1 ≤ t) (ht5 : t ≤ 5) :
    0 ≤ rho (t - 1) / t ∧ rho (t - 1) / t ≤ 1 := by
  have hrpos : 0 < rho (t - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hrle : rho (t - 1) ≤ 1 :=
    rho_le_one_of_le_five (by linarith)
  constructor
  · exact div_nonneg hrpos.le (by linarith)
  · apply (div_le_one (by linarith : 0 < t)).mpr
    exact hrle.trans ht1

/-- Explicit one-Lipschitz estimate for `rho` to the right of its initial
corner.  The proof integrates the actual delay equation, so no smoothness at
the corner `1` is assumed. -/
theorem rho_lipschitz_one_five {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    |rho b - rho a| ≤ b - a := by
  let g : ℝ → ℝ := fun t => rho (t - 1) / t
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact continuous_id.continuousOn
    · intro t ht
      exact ne_of_gt (by linarith [ha, ht.1])
  have hgint_ab : IntervalIntegrable g MeasureTheory.volume a b :=
    by
      rw [← Set.uIcc_of_le hab] at hgcont
      exact hgcont.intervalIntegrable
  have hgint_1a : IntervalIntegrable g MeasureTheory.volume 1 a := by
    have hgcont_1a : ContinuousOn g (Set.Icc (1 : ℝ) a) := by
      apply ContinuousOn.div
      · exact (continuous_rho.comp
          (continuous_id.sub continuous_const)).continuousOn
      · exact continuous_id.continuousOn
      · intro t ht
        exact ne_of_gt (by linarith [ht.1])
    rw [← Set.uIcc_of_le ha] at hgcont_1a
    exact hgcont_1a.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hgint_1a hgint_ab
  have hrhoa := rho_integral_eq ha (hab.trans hb)
  have hrhob := rho_integral_eq (ha.trans hab) hb
  have hdiff : rho b - rho a = -(∫ t in a..b, g t) := by
    dsimp [g] at hadd ⊢
    linarith
  rw [hdiff, abs_neg]
  have hnonneg : 0 ≤ ∫ t in a..b, g t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact (rho_delay_integrand_bounds
      (ha.trans ht.1) (ht.2.trans hb)).1
  rw [abs_of_nonneg hnonneg]
  have hmono := intervalIntegral.integral_mono_on hab hgint_ab
    (continuous_const.intervalIntegrable a b)
    (fun t ht => (rho_delay_integrand_bounds
      (ha.trans ht.1) (ht.2.trans hb)).2)
  simpa using hmono

/-- Global ordered one-Lipschitz estimate on `[0,5]`, including intervals
that cross the corner at `1`. -/
theorem rho_lipschitz_of_le_five {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ 5) :
    |rho b - rho a| ≤ b - a := by
  by_cases hb1 : b ≤ 1
  · rw [rho_eq_one_of_le_one hb1,
      rho_eq_one_of_le_one (hab.trans hb1)]
    simp only [sub_self, abs_zero]
    linarith
  by_cases ha1 : 1 ≤ a
  · exact rho_lipschitz_one_five ha1 hab hb
  · have hcross := rho_lipschitz_one_five
      (a := (1 : ℝ)) (b := b) le_rfl (le_of_not_ge hb1) hb
    rw [rho_eq_one_of_le_one (le_of_not_ge ha1)]
    simpa only [rho_one] using hcross.trans (by linarith)

/-! ## The Dickman test weight in the prime recurrence -/

/-- The real main term contributed by a prime `p` in the largest-prime
recurrence. -/
noncomputable def dickmanPrimeSummand (X m : ℕ) : ℝ :=
  (X : ℝ) / (m : ℝ) *
    rho (Real.log (X : ℝ) / Real.log (m : ℝ) - 1)

/-- The corresponding test function against Chebyshev's `θ` measure. -/
noncomputable def dickmanThetaWeight (X m : ℕ) : ℝ :=
  dickmanPrimeSummand X m / Real.log (m : ℝ)

/-- Continuous extension of the Dickman test weight used for the ordinary
Riemann integral. -/
noncomputable def dickmanContinuousWeight (X t : ℝ) : ℝ :=
  (X / t * rho (Real.log X / Real.log t - 1)) / Real.log t

/-- An antiderivative of the Dickman test weight on every compact region
where the Dickman delay equation applies. -/
noncomputable def dickmanAntiderivative (X t : ℝ) : ℝ :=
  X * rho (Real.log X / Real.log t)

theorem dickmanContinuousWeight_nat (X m : ℕ) :
    dickmanContinuousWeight (X : ℝ) (m : ℝ) =
      dickmanThetaWeight X m := by
  simp only [dickmanContinuousWeight, dickmanThetaWeight,
    dickmanPrimeSummand]

/-- The continuous Dickman test weight is continuous away from the two
irrelevant singular points `0` and `1`. -/
theorem continuousOn_dickmanContinuousWeight (X : ℝ) :
    ContinuousOn (dickmanContinuousWeight X) (Set.Ioi (1 : ℝ)) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  have ht0 : t ≠ 0 := by linarith [ht]
  have ht1 : t ≠ 1 := by linarith [ht]
  have hlog_ne : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht]) ht1
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hq : ContinuousAt
      (fun u : ℝ => Real.log X / Real.log u - 1) t :=
    (continuousAt_const.div hlog hlog_ne).sub continuousAt_const
  have hrho : ContinuousAt
      (fun u : ℝ => rho (Real.log X / Real.log u - 1)) t :=
    continuous_rho.continuousAt.comp hq
  have hmain : ContinuousAt
      (fun u : ℝ => X / u * rho (Real.log X / Real.log u - 1)) t :=
    (continuousAt_const.div continuousAt_id ht0).mul hrho
  exact (hmain.div hlog hlog_ne).continuousWithinAt

/-- Pointwise derivative identity behind the de Bruijn integral. -/
theorem hasDerivAt_dickmanAntiderivative (X t : ℝ) (ht : 1 < t)
    (hq1 : 1 < Real.log X / Real.log t)
    (hq6 : Real.log X / Real.log t ≤ 6) :
    HasDerivAt (dickmanAntiderivative X)
      (dickmanContinuousWeight X t) t := by
  have ht0 : t ≠ 0 := by linarith
  have htlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  let q : ℝ → ℝ := fun s => Real.log X / Real.log s
  have hq : HasDerivAt q
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
    have hraw := (hasDerivAt_const t (Real.log X)).div
      (Real.hasDerivAt_log ht0) htlog
    convert hraw using 1
    field_simp
    ring
  have hrho := (hasDerivAt_rho hq1 hq6).comp t hq
  have hmul := (hasDerivAt_const t X).mul hrho
  convert hmul using 1
  unfold dickmanContinuousWeight
  dsimp [q] at hmul ⊢
  have hq0 : Real.log X / Real.log t ≠ 0 := by linarith
  have hlogX : Real.log X ≠ 0 := by
    intro hzero
    apply hq0
    rw [hzero, zero_div]
  field_simp [hlogX, htlog, ht0]
  ring

/-- Exact evaluation of the continuous de Bruijn integral by the Dickman
delay equation.  The compact coordinate condition is stated explicitly and
is elementary to verify in each method-of-steps strip. -/
theorem integral_dickmanContinuousWeight (X z y : ℝ)
    (hz : 1 < z) (hzy : z ≤ y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 < Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    exact (hasDerivAt_dickmanAntiderivative X t
      (hz.trans_le ht.1) (hq t ht).1 (hq t ht).2).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy hcontA
  · intro t ht
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      (hq t ⟨ht.1.le, ht.2.le⟩).1
      (hq t ⟨ht.1.le, ht.2.le⟩).2
  · exact hint

/-- Against a prime point mass, the factor `log p` in `θ` cancels exactly.
Thus the weighted Stieltjes sum is literally the desired Dickman prime sum,
not merely an approximation. -/
theorem primeThetaWeightedInterval_dickman (X : ℕ) {z y : ℕ} :
    primeThetaWeightedInterval (dickmanThetaWeight X) z y =
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p := by
  rw [primeThetaWeightedInterval]
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime := by
    exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hpprime.pos) (by exact_mod_cast hpprime.ne_one)
  rw [dickmanThetaWeight]
  exact div_mul_cancel₀ _ hlog

/-- The genuine finite friable counting function `Ψ(X,y)`. -/
def friableCount (X y : ℕ) : ℕ :=
  (Nat.smoothNumbersUpTo X (y + 1)).card

/-- The Dickman coordinate attached to integral endpoints.  It is total at
the irrelevant boundary `y = 0,1`; analytic statements impose `1 < y`. -/
noncomputable def dickmanU (X y : ℕ) : ℝ :=
  Real.log (X : ℝ) / Real.log (y : ℝ)

@[simp] theorem friableCount_zero (y : ℕ) : friableCount 0 y = 0 := by
  rw [friableCount]
  have hempty : Nat.smoothNumbersUpTo 0 (y + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    rw [Nat.mem_smoothNumbersUpTo] at hm
    have hm0 : m = 0 := by omega
    exact Nat.ne_zero_of_mem_smoothNumbers hm.2 hm0
  rw [hempty]
  simp

theorem friableCount_mono_left {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    friableCount X₁ y ≤ friableCount X₂ y := by
  apply Finset.card_le_card
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩

theorem friableCount_mono_right {X y₁ y₂ : ℕ} (hy : y₁ ≤ y₂) :
    friableCount X y₁ ≤ friableCount X y₂ := by
  apply Finset.card_le_card
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1, Nat.smoothNumbers_mono (by omega) hm.2⟩

/-- Below the smoothness threshold every positive integer is smooth.  This is
the exact (not asymptotic) initial condition for the de Bruijn induction. -/
theorem friableCount_eq_self {X y : ℕ} (hXy : X ≤ y) :
    friableCount X y = X := by
  have hrough : Nat.roughNumbersUpTo X (y + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    rw [Nat.roughNumbersUpTo, Finset.mem_filter, Finset.mem_range] at hm
    exact hm.2.2 (Nat.mem_smoothNumbers_of_lt
      (Nat.pos_of_ne_zero hm.2.1) (by omega))
  have hcard := Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card X (y + 1)
  rw [hrough] at hcard
  simpa [friableCount] using hcard

theorem dickmanU_le_one {X y : ℕ} (hX : 0 < X) (hy : 1 < y)
    (hXy : X ≤ y) : dickmanU X y ≤ 1 := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy)
  have hlogxy : Real.log (X : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hX
    · exact_mod_cast hXy
  rw [dickmanU, div_le_one hlogy]
  exact hlogxy

/-- Exact Dickman formula on the initial face `u ≤ 1`.  The only discrepancy
between the real endpoint and the count is therefore the explicit floor used
to create `X`; no analytic error occurs here. -/
theorem friableCount_eq_dickman_initial {X y : ℕ} (hX : 0 < X)
    (hy : 1 < y) (hXy : X ≤ y) :
    (friableCount X y : ℝ) = (X : ℝ) * rho (dickmanU X y) := by
  rw [friableCount_eq_self hXy, rho_eq_one_of_le_one
    (dickmanU_le_one hX hy hXy)]
  ring

/-- The part of the `p`-smooth count divisible by the newly admitted prime
`p`. -/
def primeMultipleCell (X p : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo X (p + 1)).filter (p ∣ ·)

private theorem mem_smooth_succ_not_smooth_iff_dvd {p m : ℕ}
    (hp : p.Prime) (hm : m ∈ Nat.smoothNumbers (p + 1)) :
    m ∉ Nat.smoothNumbers p ↔ p ∣ m := by
  rw [Nat.mem_smoothNumbers'] at hm
  constructor
  · intro hnot
    by_contra hpdvd
    apply hnot
    rw [Nat.mem_smoothNumbers']
    intro q hq hqdiv
    have hqsucc : q < p + 1 := hm q hq hqdiv
    have hqne : q ≠ p := by
      intro hqp
      exact hpdvd (hqp ▸ hqdiv)
    omega
  · intro hpdiv hsmooth
    rw [Nat.mem_smoothNumbers'] at hsmooth
    exact (Nat.lt_irrefl p) (hsmooth p hp hpdiv)

theorem primeMultipleCell_card (X : ℕ) {p : ℕ} (hp : p.Prime) :
    (primeMultipleCell X p).card = friableCount (X / p) p := by
  classical
  apply Finset.card_bij (fun m _ => m / p)
  · intro m hm
    rw [primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo] at hm
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨?_, Nat.mem_smoothNumbers_of_dvd hm.1.2 (Nat.div_dvd_of_dvd hm.2)⟩
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    simpa [Nat.div_mul_cancel hm.2] using hm.1.1
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [primeMultipleCell, Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / p * p := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / p * p := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    rw [Nat.mem_smoothNumbersUpTo] at hk
    refine ⟨k * p, ?_, ?_⟩
    · rw [primeMultipleCell, Finset.mem_filter,
        Nat.mem_smoothNumbersUpTo]
      refine ⟨⟨?_, Nat.mul_mem_smoothNumbers hk.2 ?_⟩, by simp⟩
      · exact (Nat.le_div_iff_mul_le hp.pos).mp hk.1
      · exact Nat.mem_smoothNumbers_of_lt hp.pos (by omega)
    · exact Nat.mul_div_left k hp.pos

/-- Exact one-prime Buchstab recursion.  The first term excludes `p`; the
second term divides the newly admitted multiples of `p` by `p`.  Repeatedly
applying this identity is the discrete arithmetic induction underlying the
finite-range de Bruijn argument. -/
theorem friableCount_prime_step (X : ℕ) {p : ℕ} (hp : p.Prime) :
    friableCount X p =
      friableCount X (p - 1) + friableCount (X / p) p := by
  classical
  let A := Nat.smoothNumbersUpTo X (p + 1)
  let P : ℕ → Prop := fun m => m ∈ Nat.smoothNumbers p
  have hpartition := Finset.card_filter_add_card_filter_not (s := A) P
  have hbelow : A.filter P = Nat.smoothNumbersUpTo X p := by
    ext m
    simp only [A, P, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hmp⟩
      exact ⟨hmX, hmp⟩
    · rintro ⟨hmX, hmp⟩
      exact ⟨⟨hmX, Nat.smoothNumbers_mono (by omega) hmp⟩, hmp⟩
  have hnew : A.filter (fun m => ¬P m) = primeMultipleCell X p := by
    ext m
    simp only [A, P, primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hn⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mp hn⟩
    · rintro ⟨⟨hmX, hm⟩, hpdiv⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mpr hpdiv⟩
  rw [hbelow, hnew, primeMultipleCell_card X hp] at hpartition
  have hpone : 1 ≤ p := hp.one_le
  simpa [friableCount, Nat.sub_add_cancel hpone, A] using hpartition.symm

/-- At a composite cutoff no new smooth numbers appear. -/
theorem friableCount_composite_step (X : ℕ) {k : ℕ} (hk : ¬k.Prime) :
    friableCount X k = friableCount X (k - 1) := by
  by_cases hk0 : k = 0
  · subst k
    simp [friableCount]
  have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  rw [friableCount, friableCount, Nat.sub_add_cancel hkone]
  unfold Nat.smoothNumbersUpTo
  congr 1
  ext m
  simp only [Finset.mem_filter, Nat.smoothNumbers_succ hk]

private theorem friableCount_cutoff_zero {X : ℕ} (hX : 0 < X) :
    friableCount X 0 = 1 := by
  have hset : Nat.smoothNumbersUpTo X 1 = {1} := by
    ext m
    rw [Nat.mem_smoothNumbersUpTo, Nat.smoothNumbers_one]
    simp only [Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hmX, rfl⟩
      rfl
    · rintro rfl
      exact ⟨hX, rfl⟩
  rw [friableCount, hset]
  simp

/-- Exact largest-prime-factor recursion

`\Psi(X,y) = 1 + \sum_{p \le y} \Psi(\lfloor X/p\rfloor,p)`.

The identity follows here from the one-prime step and therefore does not need
an independently postulated greatest-prime-factor decomposition.  This is the
finite recurrence to which prime Stieltjes summation is applied in the
de Bruijn induction. -/
theorem friableCount_largest_prime (X y : ℕ) (hX : 0 < X) :
    friableCount X y =
      1 + ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
  induction y with
  | zero =>
      rw [friableCount_cutoff_zero hX]
      simp [Nat.primesBelow]
  | succ y ih =>
      by_cases hp : (y + 1).Prime
      · rw [friableCount_prime_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow =
            insert (y + 1) (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, if_pos hp]
        rw [hsub, ih, hprimes,
          Finset.sum_insert (Nat.notMem_primesBelow (y + 1))]
        omega
      · rw [friableCount_composite_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow = (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, if_neg hp]
        rw [hsub, ih, hprimes]

/-- Truncated largest-prime recursion.  This is the induction-friendly form:
choosing `z` so that `log X / log z` is an integer puts the first term on the
previous Dickman step, while every quotient in the prime interval has a
strictly smaller Dickman coordinate. -/
theorem friableCount_prime_interval (X : ℕ) {z y : ℕ} (hX : 0 < X)
    (hzy : z ≤ y) :
    friableCount X y = friableCount X z +
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        friableCount (X / p) p := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum :
      (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          friableCount (X / p) p) +
        ∑ p ∈ (z + 1).primesBelow, friableCount (X / p) p =
          ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
    simpa only using
      (Finset.sum_sdiff (f := fun p => friableCount (X / p) p) hsubset)
  rw [friableCount_largest_prime X y hX,
    friableCount_largest_prime X z hX]
  omega

/-! ## Explicit oscillation and Riemann error for the Dickman weight -/


open DickmanBasic

noncomputable def invMulLog (t : ℝ) : ℝ := 1 / (t * Real.log t)

noncomputable def logRatio (X t : ℝ) : ℝ := Real.log X / Real.log t

theorem deriv_invMulLog {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invMulLog
      (-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
  unfold invMulLog
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s)
      (Real.log t + 1) t := by
    simpa [ht] using (hasDerivAt_id t).mul (Real.hasDerivAt_log ht)
  have hraw := (hasDerivAt_const t (1 : ℝ)).div hden (mul_ne_zero ht hlog)
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem deriv_logRatio (X : ℝ) {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt (logRatio X)
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
  unfold logRatio
  have hraw := (hasDerivAt_const t (Real.log X)).div
    (Real.hasDerivAt_log ht) hlog
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem inv_deriv_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    |-(Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)| ≤
      6 / (k : ℝ) ^ 2 := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.log t + 1),
    abs_mul]
  simp only [abs_pow, abs_of_pos htpos, abs_of_pos hlogpos]
  have hpoly : (Real.log t + 1) / (Real.log t) ^ 2 ≤ 6 := by
    apply (div_le_iff₀ (sq_pos_of_pos hlogpos)).2
    nlinarith [sq_nonneg (Real.log t - 1 / 2)]
  calc
    (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2) =
        ((Real.log t + 1) / Real.log t ^ 2) / t ^ 2 := by field_simp
    _ ≤ 6 / t ^ 2 := by
      exact div_le_div_of_nonneg_right hpoly (sq_nonneg t)
    _ ≤ 6 / (k : ℝ) ^ 2 := by
      gcongr

theorem logRatio_deriv_bound (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {t : ℝ} (ht : (k : ℝ) ≤ t) :
    |-(Real.log X) / (t * (Real.log t) ^ 2)| ≤
      4 * Real.log X / (k : ℝ) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  rw [abs_div, abs_neg, abs_of_nonneg hlogX, abs_mul,
    abs_of_pos htpos, abs_pow, abs_of_pos hlogpos]
  have hlogsq : (1 / 4 : ℝ) ≤ Real.log t ^ 2 := by nlinarith
  apply (div_le_div_iff₀ (mul_pos htpos (sq_pos_of_pos hlogpos)) hkpos).2
  have hden1 : t * (1 / 4 : ℝ) ≤ t * Real.log t ^ 2 :=
    mul_le_mul_of_nonneg_left hlogsq htpos.le
  have hden : (k : ℝ) ≤ 4 * (t * Real.log t ^ 2) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hden hlogX]

theorem invMulLog_cell_lipschitz {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |invMulLog s - invMulLog t| ≤
      (6 / (k : ℝ) ^ 2) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ invMulLog u := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (deriv_invMulLog hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv invMulLog u‖ ≤ 6 / (k : ℝ) ^ 2 := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(deriv_invMulLog hu0 hlogu).deriv, Real.norm_eq_abs]
    exact inv_deriv_bound hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem logRatio_cell_lipschitz (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |logRatio X s - logRatio X t| ≤
      (4 * Real.log X / (k : ℝ)) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ (logRatio X) u := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (deriv_logRatio X hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv (logRatio X) u‖ ≤ 4 * Real.log X / (k : ℝ) := by
    have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hu2 : (2 : ℝ) ≤ u := hkreal.trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(deriv_logRatio X hu0 hlogu).deriv, Real.norm_eq_abs]
    exact logRatio_deriv_bound X hX hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem invMulLog_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    0 ≤ invMulLog t ∧ invMulLog t ≤ 2 / (k : ℝ) := by
  have hkreal : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkt : (2 : ℝ) ≤ t := hkreal.trans ht
  have htpos : 0 < t := by linarith
  have hkposNat : 0 < k := lt_of_lt_of_le (by norm_num : 0 < 2) hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
  have hlog : (1 / 2 : ℝ) ≤ Real.log t := by
    have hlogmono : Real.log 2 ≤ Real.log t := by
      apply Real.log_le_log
      · norm_num
      · exact hkt
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  constructor
  · unfold invMulLog
    positivity
  · unfold invMulLog
    apply (div_le_iff₀ (mul_pos htpos hlogpos)).2
    rw [show 2 / (k : ℝ) * (t * Real.log t) =
      (2 * (t * Real.log t)) / (k : ℝ) by ring]
    apply (le_div_iff₀ hkpos).2
    have hprod : t * (1 / 2 : ℝ) ≤ t * Real.log t :=
      mul_le_mul_of_nonneg_left hlog htpos.le
    nlinarith

theorem rho_logRatio_lipschitz (X s t : ℝ)
    (hs5 : logRatio X s - 1 ≤ 5)
    (ht5 : logRatio X t - 1 ≤ 5) :
    |rho (logRatio X s - 1) - rho (logRatio X t - 1)| ≤
      |logRatio X s - logRatio X t| := by
  by_cases hst : logRatio X t - 1 ≤ logRatio X s - 1
  · have h := rho_lipschitz_of_le_five hst hs5
    calc
      |rho (logRatio X s - 1) - rho (logRatio X t - 1)| ≤
          (logRatio X s - 1) - (logRatio X t - 1) := h
      _ = logRatio X s - logRatio X t := by ring
      _ = |logRatio X s - logRatio X t| := by
        rw [abs_of_nonneg (by linarith)]
  · have h := rho_lipschitz_of_le_five (le_of_not_ge hst) ht5
    rw [abs_sub_comm]
    calc
      |rho (logRatio X t - 1) - rho (logRatio X s - 1)| ≤
          (logRatio X t - 1) - (logRatio X s - 1) := h
      _ = logRatio X t - logRatio X s := by ring
      _ = |logRatio X t - logRatio X s| := by
        rw [abs_of_nonneg (by linarith)]
      _ = |logRatio X s - logRatio X t| := abs_sub_comm _ _

theorem dickmanContinuousWeight_cell_lipschitz (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {s t : ℝ}
    (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (hqs0 : 0 ≤ logRatio X s - 1) (hqs5 : logRatio X s - 1 ≤ 5)
    (hqt5 : logRatio X t - 1 ≤ 5) :
    |dickmanContinuousWeight X s - dickmanContinuousWeight X t| ≤
      (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * |s - t| := by
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hA_t := invMulLog_bound hk ht.1
  have hAdiff := invMulLog_cell_lipschitz hk hs ht
  have hQdiff := logRatio_cell_lipschitz X hX hk hs ht
  have hRdiff := (rho_logRatio_lipschitz X s t hqs5 hqt5).trans hQdiff
  have hRspos : 0 ≤ rho (logRatio X s - 1) :=
    (rho_pos_on_zero_five hqs0 hqs5).le
  have hRsle : rho (logRatio X s - 1) ≤ 1 :=
    rho_le_one_of_le_five hqs5
  have hAstabs : |invMulLog t| ≤ 2 / (k : ℝ) := by
    rw [abs_of_nonneg hA_t.1]
    exact hA_t.2
  have hrewrite (u : ℝ) :
      dickmanContinuousWeight X u =
        X * invMulLog u * rho (logRatio X u - 1) := by
    unfold dickmanContinuousWeight invMulLog logRatio
    ring
  rw [hrewrite, hrewrite]
  have halgebra :
      invMulLog s * rho (logRatio X s - 1) -
          invMulLog t * rho (logRatio X t - 1) =
        (invMulLog s - invMulLog t) * rho (logRatio X s - 1) +
          invMulLog t * (rho (logRatio X s - 1) -
            rho (logRatio X t - 1)) := by ring
  have hfactor :
      X * invMulLog s * rho (logRatio X s - 1) -
          X * invMulLog t * rho (logRatio X t - 1) =
        X * (invMulLog s * rho (logRatio X s - 1) -
          invMulLog t * rho (logRatio X t - 1)) := by ring
  rw [hfactor, abs_mul, abs_of_nonneg hX0, halgebra]
  calc
    X * |(invMulLog s - invMulLog t) * rho (logRatio X s - 1) +
        invMulLog t * (rho (logRatio X s - 1) -
          rho (logRatio X t - 1))| ≤
      X * (|invMulLog s - invMulLog t| *
          |rho (logRatio X s - 1)| +
        |invMulLog t| * |rho (logRatio X s - 1) -
          rho (logRatio X t - 1)|) := by
      apply mul_le_mul_of_nonneg_left _ hX0
      simpa only [abs_mul] using abs_add_le
        ((invMulLog s - invMulLog t) * rho (logRatio X s - 1))
        (invMulLog t * (rho (logRatio X s - 1) -
          rho (logRatio X t - 1)))
    _ ≤ X * ((6 / (k : ℝ) ^ 2 * |s - t|) * 1 +
        (2 / (k : ℝ)) * ((4 * Real.log X / (k : ℝ)) * |s - t|)) := by
      have hRsabs : |rho (logRatio X s - 1)| ≤ 1 := by
        rw [abs_of_nonneg hRspos]
        exact hRsle
      have hBnonneg : 0 ≤ 6 / (k : ℝ) ^ 2 * |s - t| := by positivity
      have hCnonneg : 0 ≤ 2 / (k : ℝ) := by positivity
      have hterm1 :
          |invMulLog s - invMulLog t| * |rho (logRatio X s - 1)| ≤
            (6 / (k : ℝ) ^ 2 * |s - t|) * 1 :=
        mul_le_mul hAdiff hRsabs (abs_nonneg _) hBnonneg
      have hterm2 :
          |invMulLog t| * |rho (logRatio X s - 1) -
              rho (logRatio X t - 1)| ≤
            (2 / (k : ℝ)) *
              ((4 * Real.log X / (k : ℝ)) * |s - t|) :=
        mul_le_mul hAstabs hRdiff (abs_nonneg _) hCnonneg
      exact mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) hX0
    _ = (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * |s - t| := by
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      field_simp
      ring

theorem dickmanContinuousWeight_cell_oscillation (X : ℝ) (hX : 1 ≤ X)
    {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (hq : ∀ u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
      0 ≤ logRatio X u - 1 ∧ logRatio X u - 1 ≤ 5) :
    |dickmanContinuousWeight X (k + 1 : ℕ) -
        dickmanContinuousWeight X t| ≤
      X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2 := by
  have hs : ((k + 1 : ℕ) : ℝ) ∈
      Set.Icc (k : ℝ) (k + 1 : ℕ) := by constructor <;> norm_num
  have h := dickmanContinuousWeight_cell_lipschitz X hX hk hs ht
    (hq _ hs).1 (hq _ hs).2 (hq _ ht).2
  have hdist : |((k + 1 : ℕ) : ℝ) - t| ≤ 1 := by
    rw [abs_of_nonneg (by linarith [ht.2])]
    norm_num
    linarith [ht.1]
  have hcoef : 0 ≤ X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2 := by
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
    positivity
  calc
    |dickmanContinuousWeight X (k + 1 : ℕ) -
        dickmanContinuousWeight X t| ≤
      (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) *
        |((k + 1 : ℕ) : ℝ) - t| := h
    _ ≤ (X * (6 + 8 * Real.log X) / (k : ℝ) ^ 2) * 1 := by
      exact mul_le_mul_of_nonneg_left hdist hcoef
    _ = _ := by ring

theorem sum_Ico_inv_sq_le {z y : ℕ} (hz : 1 ≤ z) :
    (∑ k ∈ Finset.Ico z y, 1 / (k : ℝ) ^ 2) ≤ 2 / (z : ℝ) := by
  have hfin : Finset.Ico z y = Finset.Ioo (z - 1) y := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  rw [hfin]
  have h := sum_Ioo_inv_sq_le (α := ℝ) (z - 1) y
  have hcast : (((z - 1 : ℕ) : ℝ) + 1) = (z : ℝ) := by
    rw [Nat.cast_sub hz]
    norm_num
  rw [hcast] at h
  simpa [one_div] using h

theorem dickmanWeight_sum_integral_bound (X : ℕ) (hX : 1 ≤ X)
    {z y : ℕ} (hz : 2 ≤ z) (hzy : z ≤ y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
        ∫ t in (z : ℝ)..(y : ℝ), dickmanContinuousWeight X t| ≤
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
  have hcoef : 0 ≤ (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) := by positivity
  have hint : ∀ k ∈ Set.Ico z y,
      IntervalIntegrable (dickmanContinuousWeight (X : ℝ))
        MeasureTheory.volume (k : ℝ) (k + 1 : ℕ) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hz.trans hk.1
    have hcont : ContinuousOn (dickmanContinuousWeight (X : ℝ))
        (Set.Icc (k : ℝ) (k + 1 : ℕ)) :=
      (continuousOn_dickmanContinuousWeight (X : ℝ)).mono (fun t ht => by
        rw [Set.mem_Ioi]
        linarith [hk2, ht.1])
    rw [← Set.uIcc_of_le (by norm_num : (k : ℝ) ≤ (k + 1 : ℕ))] at hcont
    exact hcont.intervalIntegrable
  have hosc : ∀ k ∈ Finset.Ico z y,
      ∀ t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
        |dickmanContinuousWeight (X : ℝ) (k + 1 : ℕ) -
          dickmanContinuousWeight (X : ℝ) t| ≤
          (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (k : ℝ) ^ 2 := by
    intro k hk t ht
    rw [Finset.mem_Ico] at hk
    have hk2 : 2 ≤ k := hz.trans hk.1
    apply dickmanContinuousWeight_cell_oscillation (X : ℝ) hXR hk2 ht
    intro u hu
    have huglobal : u ∈ Set.Icc (z : ℝ) (y : ℝ) := by
      constructor
      · have hzk : (z : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        exact hzk.trans hu.1
      · have hky : k + 1 ≤ y := by omega
        exact hu.2.trans (by exact_mod_cast hky)
    have huq := hq u huglobal
    exact ⟨by linarith [huq.1], by linarith [huq.2]⟩
  have hR := sum_integral_error_bound
    (dickmanContinuousWeight (X : ℝ))
    (fun k => (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (k : ℝ) ^ 2)
    hzy hint (by
      simpa only [Nat.cast_add, Nat.cast_one] using hosc)
  simp only [dickmanContinuousWeight_nat] at hR
  calc
    |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
        ∫ t in (z : ℝ)..(y : ℝ), dickmanContinuousWeight X t| ≤
      ∑ k ∈ Finset.Ico z y,
        (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (k : ℝ) ^ 2 := hR
    _ = ((X : ℝ) * (6 + 8 * Real.log (X : ℝ))) *
        ∑ k ∈ Finset.Ico z y, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ ((X : ℝ) * (6 + 8 * Real.log (X : ℝ))) *
        (2 / (z : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ico_inv_sq_le (show 1 ≤ z by omega)) hcoef
    _ = 2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by ring


/-! ## Quantitative PNT transfer for the Dickman prime weight

The following estimates combine the preceding Chebyshev--Stieltjes identity,
the audited medium PNT, and the explicit Dickman-weight oscillation bound.
They are the one-prime analytic input for the finite de Bruijn induction.
-/

theorem continuousWeight_eq (X t : ℝ) :
    dickmanContinuousWeight X t =
      X * invMulLog t * rho (logRatio X t - 1) := by
  unfold dickmanContinuousWeight invMulLog logRatio
  ring

theorem thetaWeight_abs_le (X m : ℕ) (hX : 1 ≤ X) (hm : 2 ≤ m)
    (hq0 : 1 ≤ logRatio (X : ℝ) (m : ℝ))
    (hq6 : logRatio (X : ℝ) (m : ℝ) ≤ 6) :
    |dickmanThetaWeight X m| ≤ 2 * (X : ℝ) / (m : ℝ) := by
  rw [← dickmanContinuousWeight_nat, continuousWeight_eq, abs_mul, abs_mul]
  have hXR : (0 : ℝ) ≤ X := by positivity
  have hA := invMulLog_bound hm (le_refl (m : ℝ))
  have hRpos : 0 ≤ rho (logRatio (X : ℝ) (m : ℝ) - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  have hRle : rho (logRatio (X : ℝ) (m : ℝ) - 1) ≤ 1 :=
    rho_le_one_of_le_five (by linarith)
  rw [abs_of_nonneg hXR, abs_of_nonneg hA.1, abs_of_nonneg hRpos]
  calc
    (X : ℝ) * invMulLog (m : ℝ) * rho (logRatio (X : ℝ) (m : ℝ) - 1) =
        (X : ℝ) * (invMulLog (m : ℝ) *
          rho (logRatio (X : ℝ) (m : ℝ) - 1)) := by ring
    _ ≤ (X : ℝ) * ((2 / (m : ℝ)) * 1) := by
      apply mul_le_mul_of_nonneg_left _ hXR
      exact mul_le_mul hA.2 hRle hRpos (by positivity)
    _ = 2 * (X : ℝ) / (m : ℝ) := by ring

theorem harmonic_Ioc_le {z y : ℕ} :
    (∑ m ∈ Finset.Ioc z y, 1 / (m : ℝ)) ≤ 1 + Real.log (y : ℝ) := by
  calc
    (∑ m ∈ Finset.Ioc z y, 1 / (m : ℝ)) ≤
        ∑ m ∈ Finset.Icc 1 y, 1 / (m : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        rw [Finset.mem_Ioc] at hm
        rw [Finset.mem_Icc]
        exact ⟨by omega, hm.2⟩
      · intro m hm hmn
        positivity
    _ = (harmonic y : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ 1 + Real.log (y : ℝ) := by exact_mod_cast harmonic_le_one_add_log y

theorem thetaWeight_diff_bound (X : ℕ) (hX : 1 ≤ X)
    {m : ℕ} (hm : 2 ≤ m)
    (hq : ∀ u ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
      1 ≤ logRatio (X : ℝ) u ∧ logRatio (X : ℝ) u ≤ 6) :
    |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| ≤
      (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (m : ℝ) ^ 2 := by
  rw [← dickmanContinuousWeight_nat, ← dickmanContinuousWeight_nat]
  have ht : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
    constructor <;> norm_num
  apply dickmanContinuousWeight_cell_oscillation
    (X : ℝ) (by exact_mod_cast hX) hm ht
  intro u hu
  have huq := hq u hu
  exact ⟨by linarith [huq.1], by linarith [huq.2]⟩

set_option maxHeartbeats 800000 in
theorem dickmanWeight_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |primeThetaWeightedInterval (dickmanThetaWeight X) z y -
        integerAbelMain (dickmanThetaWeight X) z y| ≤
      500 * C * (X : ℝ) / Real.log (z : ℝ) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hzR : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hyR : (2 : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast hz.trans hzy.le
  have hlogz : (1 / 2 : ℝ) ≤ Real.log (z : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (z : ℝ) := by
      apply Real.log_le_log
      · norm_num
      · exact hzR
    nlinarith [Real.log_two_gt_d9]
  have hlogzpos : 0 < Real.log (z : ℝ) := by linarith
  have hlogypos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hlogzy : Real.log (z : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hzy.le
  have hzmem : (z : ℝ) ∈ Set.Icc (z : ℝ) (y : ℝ) :=
    ⟨le_rfl, by exact_mod_cast hzy.le⟩
  have hymem : (y : ℝ) ∈ Set.Icc (z : ℝ) (y : ℝ) :=
    ⟨by exact_mod_cast hzy.le, le_rfl⟩
  have hlogX_le : Real.log (X : ℝ) ≤ 6 * Real.log (z : ℝ) := by
    have hzq := (hq _ hzmem).2
    rw [logRatio] at hzq
    exact (div_le_iff₀ hlogzpos).mp hzq
  have hlogy_le : Real.log (y : ℝ) ≤ Real.log (X : ℝ) := by
    have hyq := (hq _ hymem).1
    rw [logRatio] at hyq
    simpa using (le_div_iff₀ hlogypos).mp hyq
  have hone_logy : 1 + Real.log (y : ℝ) ≤ 8 * Real.log (z : ℝ) := by
    linarith
  have hinv3 : 1 / Real.log (z : ℝ) ^ 3 ≤ 4 / Real.log (z : ℝ) := by
    apply (div_le_div_iff₀ (pow_pos hlogzpos 3) hlogzpos).2
    nlinarith [sq_nonneg (Real.log (z : ℝ) - 1 / 2)]
  have hgeneric := primeThetaWeightedInterval_pnt_bound
    (dickmanThetaWeight X) (A := (3 : ℝ)) hbound hX₀z hzy
  simp only [Real.rpow_ofNat] at hgeneric
  have hfy := thetaWeight_abs_le X y hX (hz.trans hzy.le) (hq _ hymem).1 (hq _ hymem).2
  have hz1mem : ((z + 1 : ℕ) : ℝ) ∈ Set.Icc (z : ℝ) (y : ℝ) := by
    constructor
    · norm_num
    · exact_mod_cast (by omega : z + 1 ≤ y)
  have hfz1raw := thetaWeight_abs_le X (z + 1) hX (by omega)
    (hq _ hz1mem).1 (hq _ hz1mem).2
  have hfz1 : |dickmanThetaWeight X (z + 1)| ≤
      2 * (X : ℝ) / (z : ℝ) := by
    exact hfz1raw.trans (by gcongr; omega)
  have htermY :
      |dickmanThetaWeight X y| *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ (3 : ℕ))) ≤
        8 * C * (X : ℝ) / Real.log (z : ℝ) := by
    calc
      _ ≤ (2 * (X : ℝ) / (y : ℝ)) *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ (3 : ℕ))) := by
        gcongr
      _ = 2 * C * (X : ℝ) / Real.log (y : ℝ) ^ 3 := by
        have hy0 : (y : ℝ) ≠ 0 := by positivity
        field_simp [hy0]
      _ ≤ 2 * C * (X : ℝ) / Real.log (z : ℝ) ^ 3 := by
        gcongr
      _ ≤ 8 * C * (X : ℝ) / Real.log (z : ℝ) := by
        have hfac : 0 ≤ 2 * C * (X : ℝ) := by positivity
        calc
          _ = (2 * C * (X : ℝ)) *
              (1 / Real.log (z : ℝ) ^ 3) := by ring
          _ ≤ (2 * C * (X : ℝ)) *
              (4 / Real.log (z : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv3 hfac
          _ = _ := by ring
  have htermZ :
      |dickmanThetaWeight X (z + 1)| *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) ≤
        8 * C * (X : ℝ) / Real.log (z : ℝ) := by
    calc
      _ ≤ (2 * (X : ℝ) / (z : ℝ)) *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) := by
        gcongr
      _ = 2 * C * (X : ℝ) / Real.log (z : ℝ) ^ 3 := by
        have hz0 : (z : ℝ) ≠ 0 := by positivity
        field_simp [hz0]
      _ ≤ 8 * C * (X : ℝ) / Real.log (z : ℝ) := by
        have hfac : 0 ≤ 2 * C * (X : ℝ) := by positivity
        calc
          _ = (2 * C * (X : ℝ)) *
              (1 / Real.log (z : ℝ) ^ 3) := by ring
          _ ≤ (2 * C * (X : ℝ)) *
              (4 / Real.log (z : ℝ)) :=
            mul_le_mul_of_nonneg_left hinv3 hfac
          _ = _ := by ring
  have hvar :
      (∑ m ∈ Finset.Ioc z (y - 1),
        |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ)))) ≤
        480 * C * (X : ℝ) / Real.log (z : ℝ) := by
    let K : ℝ := 6 + 8 * Real.log (X : ℝ)
    have hlogXnonneg : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hXR
    have hKnonneg : 0 ≤ K := by
      dsimp [K]
      positivity
    have hKle : K ≤ 6 + 48 * Real.log (z : ℝ) := by
      dsimp [K]
      nlinarith
    have hinv2 : 1 / Real.log (z : ℝ) ^ 2 ≤
        2 / Real.log (z : ℝ) := by
      apply (div_le_div_iff₀ (pow_pos hlogzpos 2) hlogzpos).2
      nlinarith [sq_nonneg (Real.log (z : ℝ) - 1 / 2)]
    have hpoint : ∀ m ∈ Finset.Ioc z (y - 1),
        |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) ≤
          (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
            (1 / (m : ℝ)) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm2 : 2 ≤ m := by omega
      have hm1y : m + 1 ≤ y := by omega
      have hqcell : ∀ u ∈ Set.Icc (m : ℝ) (m + 1 : ℕ),
          1 ≤ logRatio (X : ℝ) u ∧ logRatio (X : ℝ) u ≤ 6 := by
        intro u hu
        apply hq u
        constructor
        · calc
            (z : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1.le
            _ ≤ u := hu.1
        · calc
            u ≤ ((m + 1 : ℕ) : ℝ) := hu.2
            _ ≤ (y : ℝ) := by exact_mod_cast hm1y
      have hdiff := thetaWeight_diff_bound X hX hm2 hqcell
      have hlogmpos : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      have hlogzm : Real.log (z : ℝ) ≤ Real.log (m : ℝ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hm.1.le
      have hinvlog : 1 / Real.log (m : ℝ) ^ 3 ≤
          1 / Real.log (z : ℝ) ^ 3 := by
        gcongr
      have hfactor : 0 ≤ C * ((m : ℝ) / Real.log (m : ℝ) ^ 3) := by
        positivity
      calc
        _ ≤ ((X : ℝ) * K / (m : ℝ) ^ 2) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) := by
          exact mul_le_mul_of_nonneg_right hdiff hfactor
        _ = (C * (X : ℝ) * K *
              (1 / Real.log (m : ℝ) ^ 3)) * (1 / (m : ℝ)) := by
          have hm0 : (m : ℝ) ≠ 0 := by positivity
          field_simp
        _ ≤ (C * (X : ℝ) * K *
              (1 / Real.log (z : ℝ) ^ 3)) * (1 / (m : ℝ)) := by
          gcongr
        _ = (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
              (1 / (m : ℝ)) := by ring
    have hsum :
        (∑ m ∈ Finset.Ioc z (y - 1),
          |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3))) ≤
          (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
            (∑ m ∈ Finset.Ioc z (y - 1), 1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun m hm => hpoint m hm
    have hhar : (∑ m ∈ Finset.Ioc z (y - 1), 1 / (m : ℝ)) ≤
        1 + Real.log (y : ℝ) := by
      calc
        _ ≤ ∑ m ∈ Finset.Ioc z y, 1 / (m : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro m hm
            rw [Finset.mem_Ioc] at hm ⊢
            omega
          · intro m hm hmn
            positivity
        _ ≤ 1 + Real.log (y : ℝ) := harmonic_Ioc_le
    calc
      _ ≤ (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
          (∑ m ∈ Finset.Ioc z (y - 1), 1 / (m : ℝ)) := hsum
      _ ≤ (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
          (1 + Real.log (y : ℝ)) := by gcongr
      _ ≤ (C * (X : ℝ) * K / Real.log (z : ℝ) ^ 3) *
          (8 * Real.log (z : ℝ)) := by gcongr
      _ = 8 * C * (X : ℝ) * K / Real.log (z : ℝ) ^ 2 := by
        field_simp
      _ ≤ 8 * C * (X : ℝ) *
          (6 + 48 * Real.log (z : ℝ)) /
            Real.log (z : ℝ) ^ 2 := by gcongr
      _ = 48 * C * (X : ℝ) / Real.log (z : ℝ) ^ 2 +
          384 * C * (X : ℝ) / Real.log (z : ℝ) := by
        field_simp
        ring
      _ ≤ 480 * C * (X : ℝ) / Real.log (z : ℝ) := by
        have hfac : 0 ≤ 48 * C * (X : ℝ) := by positivity
        calc
          _ = (48 * C * (X : ℝ)) *
                (1 / Real.log (z : ℝ) ^ 2) +
              384 * C * (X : ℝ) / Real.log (z : ℝ) := by ring
          _ ≤ (48 * C * (X : ℝ)) *
                (2 / Real.log (z : ℝ)) +
              384 * C * (X : ℝ) / Real.log (z : ℝ) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hinv2 hfac) le_rfl
          _ = _ := by ring
  calc
    _ ≤ |dickmanThetaWeight X y| *
          (C * ((y : ℝ) / Real.log (y : ℝ) ^ (3 : ℕ))) +
        |dickmanThetaWeight X (z + 1)| *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) +
        ∑ m ∈ Finset.Ioc z (y - 1),
          |dickmanThetaWeight X (m + 1) - dickmanThetaWeight X m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ))) := hgeneric
    _ ≤ 8 * C * (X : ℝ) / Real.log (z : ℝ) +
        8 * C * (X : ℝ) / Real.log (z : ℝ) +
        480 * C * (X : ℝ) / Real.log (z : ℝ) := by
      exact add_le_add (add_le_add htermY htermZ) hvar
    _ = 496 * C * (X : ℝ) / Real.log (z : ℝ) := by ring
    _ ≤ 500 * C * (X : ℝ) / Real.log (z : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogzpos.le
      have hCX : 0 ≤ C * (X : ℝ) := by positivity
      nlinarith


/-- The actual prime sum in the finite largest-prime recurrence has the
Dickman antiderivative as its main term, with an explicit PNT plus Riemann
error. -/
theorem dickmanPrimeSum_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 < logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤
      500 * C * (X : ℝ) / Real.log (z : ℝ) +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by
  have hqweak : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6 := by
    intro t ht
    have h := hq t ht
    exact ⟨h.1.le, h.2⟩
  have hpnt := dickmanWeight_pnt_bound X hX hC hbound hX₀z hz hzy hqweak
  rw [primeThetaWeightedInterval_dickman,
    integerAbelMain_eq_sum_Ioc (dickmanThetaWeight X) hzy] at hpnt
  have hriemann := dickmanWeight_sum_integral_bound X hX hz hzy.le hqweak
  have hintegral := integral_dickmanContinuousWeight
    (X : ℝ) (z : ℝ) (y : ℝ)
    (by exact_mod_cast (show 1 < z by omega))
    (by exact_mod_cast hzy.le) hq
  rw [hintegral] at hriemann
  calc
    _ = |((∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) +
        ((∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m| +
        |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ))| := abs_add_le _ _
    _ ≤ _ := add_le_add hpnt hriemann


/-- One finite method-of-steps propagation: quotient-count errors, the
baseline error, and the proved prime-sum error add without any hidden loss. -/
theorem friableCount_step_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C E₀ : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 < logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6)
    (e : ℕ → ℝ)
    (hbase : |(friableCount X z : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ)| ≤ E₀)
    (hquot : ∀ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
      |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p) :
    |(friableCount X y : ℝ) -
        dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤
      E₀ + (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ)) := by
  let P := (y + 1).primesBelow \ (z + 1).primesBelow
  have hrecNat := friableCount_prime_interval X (Nat.succ_le_iff.mp hX) hzy.le
  have hrec : (friableCount X y : ℝ) = (friableCount X z : ℝ) +
      ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by
    exact_mod_cast hrecNat
  have hsum :
      |(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p| ≤
        ∑ p ∈ P, e p := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ P,
          |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P, e p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hquot p (by simpa [P] using hp)
  have hprime := dickmanPrimeSum_pnt_bound X hX hC hbound hX₀z hz hzy hq
  change |(∑ p ∈ P, dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤ _ at hprime
  rw [hrec]
  calc
    _ = |((friableCount X z : ℝ) -
          dickmanAntiderivative (X : ℝ) (z : ℝ)) +
        (((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
            ∑ p ∈ P, dickmanPrimeSummand X p) +
          ((∑ p ∈ P, dickmanPrimeSummand X p) -
            (dickmanAntiderivative (X : ℝ) (y : ℝ) -
              dickmanAntiderivative (X : ℝ) (z : ℝ))))| := by ring_nf
    _ ≤ |(friableCount X z : ℝ) -
          dickmanAntiderivative (X : ℝ) (z : ℝ)| +
        (|(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
            ∑ p ∈ P, dickmanPrimeSummand X p| +
          |(∑ p ∈ P, dickmanPrimeSummand X p) -
            (dickmanAntiderivative (X : ℝ) (y : ℝ) -
              dickmanAntiderivative (X : ℝ) (z : ℝ))|) := by
      exact (abs_add_le _ _).trans
        (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ E₀ + ((∑ p ∈ P, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ))) := by
      exact add_le_add hbase (add_le_add hsum hprime)
    _ = _ := by
      dsimp [P]
      ring


/-! ## Uniform floor stability for the recursive Dickman kernel -/

/-- Replacing a positive real quotient by its integer floor perturbs the
Dickman main term by an absolute constant, uniformly on the compact range
used by the four-mark induction. -/
theorem rho_floor_kernel_stability (A : ℕ) {r p : ℝ}
    (hA : 1 ≤ A) (hAr : (A : ℝ) ≤ r) (hrA : r < (A : ℝ) + 1)
    (hp : (2 : ℝ) ≤ p) (hb4 : Real.log r / Real.log p ≤ 4) :
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| ≤ 3 := by
  let a : ℝ := Real.log (A : ℝ) / Real.log p
  let b : ℝ := Real.log r / Real.log p
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hrpos : 0 < r := hApos.trans_le hAr
  have hppos : 0 < p := by linarith
  have hlogppos : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogp_half : (1 / 2 : ℝ) ≤ Real.log p := by
    have hmono : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp
    nlinarith [Real.log_two_gt_d9]
  have hlogAr : Real.log (A : ℝ) ≤ Real.log r :=
    Real.log_le_log hApos hAr
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right hlogAr hlogppos.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hA)) hlogppos.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5 : b ≤ 5 := by dsimp [b]; linarith
  have hrhoa0 : 0 ≤ rho a :=
    (rho_pos_on_zero_five ha0 (hab.trans hb5)).le
  have hrhob0 : 0 ≤ rho b := (rho_pos_on_zero_five hb0 hb5).le
  have hrhob1 : rho b ≤ 1 := rho_le_one_of_le_five hb5
  have hrho : |rho a - rho b| ≤ b - a := by
    rw [abs_sub_comm]
    exact rho_lipschitz_of_le_five hab hb5
  have hlogquot : Real.log r - Real.log (A : ℝ) ≤
      r / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hrpos hApos)
    rw [Real.log_div hrpos.ne' hApos.ne'] at h
    exact h
  have hscaled : (A : ℝ) *
      (Real.log r - Real.log (A : ℝ)) ≤ r - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogquot hApos.le
    calc
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
          (A : ℝ) * (r / (A : ℝ) - 1) := h
      _ = r - (A : ℝ) := by field_simp
  have hAdiff : (A : ℝ) * (b - a) ≤ 2 := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogppos.le
    have hfirst : (A : ℝ) * (b - a) ≤
        (r - (A : ℝ)) / Real.log p := by
      dsimp [a, b]
      convert hdiv using 1; ring
    have hsecond : (r - (A : ℝ)) / Real.log p ≤ 2 := by
      apply (div_le_iff₀ hlogppos).2
      nlinarith
    exact hfirst.trans hsecond
  have hgap0 : 0 ≤ r - (A : ℝ) := sub_nonneg.mpr hAr
  have hgap1 : r - (A : ℝ) ≤ 1 := by linarith
  calc
    _ = |(A : ℝ) * (rho a - rho b) +
          ((A : ℝ) - r) * rho b| := by dsimp [a, b]; congr 1; ring
    _ ≤ |(A : ℝ) * (rho a - rho b)| +
          |((A : ℝ) - r) * rho b| := abs_add_le _ _
    _ = (A : ℝ) * |rho a - rho b| +
          (r - (A : ℝ)) * rho b := by
      rw [abs_mul, abs_mul, abs_of_nonneg hApos.le,
        abs_of_nonpos (sub_nonpos.mpr hAr), abs_of_nonneg hrhob0]
      ring
    _ ≤ (A : ℝ) * (b - a) +
          (r - (A : ℝ)) * 1 := by gcongr
    _ ≤ 2 + 1 := add_le_add hAdiff (by simpa using hgap1)
    _ = 3 := by norm_num

/-- The integer quotient in the exact largest-prime recurrence and its real
Dickman model differ by at most three. -/
theorem dickmanPrimeSummand_floor_stability (X p : ℕ)
    (hp2 : 2 ≤ p) (hpX : p ≤ X)
    (hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5) :
    |((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p) -
        dickmanPrimeSummand X p| ≤ 3 := by
  have hp0 : 0 < p := by omega
  have hX0 : 0 < X := hp0.trans_le hpX
  have hA : 1 ≤ X / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    simpa using hpX
  have hAr : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) :=
    Nat.cast_div_le
  have hupperNat : X < (X / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_succ_self (X / p))
  have hrA : (X : ℝ) / (p : ℝ) < ((X / p : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hp0 : (0 : ℝ) < p)).2
    exact_mod_cast hupperNat
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogdiv :
      Real.log ((X : ℝ) / (p : ℝ)) =
        Real.log (X : ℝ) - Real.log (p : ℝ) := by
    rw [Real.log_div (by exact_mod_cast hX0.ne' : (X : ℝ) ≠ 0)
      (by exact_mod_cast hp0.ne' : (p : ℝ) ≠ 0)]
  have hb4 : Real.log ((X : ℝ) / (p : ℝ)) /
      Real.log (p : ℝ) ≤ 4 := by
    rw [hlogdiv]
    apply (div_le_iff₀ hlogp).2
    have hq := (div_le_iff₀ hlogp).mp hq5
    linarith
  have hcoord : Real.log ((X : ℝ) / (p : ℝ)) /
      Real.log (p : ℝ) =
        Real.log (X : ℝ) / Real.log (p : ℝ) - 1 := by
    rw [hlogdiv]
    field_simp
  have hstab := rho_floor_kernel_stability (X / p) hA hAr hrA
    (by exact_mod_cast hp2) hb4
  rw [hcoord] at hstab
  simpa only [dickmanU, dickmanPrimeSummand] using hstab


/-- Chebyshev test weight whose prime mass is `1 / (p log p)`. -/
noncomputable def invLogThetaWeight (m : ℕ) : ℝ :=
  1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2)

noncomputable def invLogContinuousWeight (t : ℝ) : ℝ :=
  1 / (t * Real.log t ^ 2)

noncomputable def invLogAntiderivative (t : ℝ) : ℝ :=
  -(1 / Real.log t)

theorem invLogContinuousWeight_nat (m : ℕ) :
    invLogContinuousWeight (m : ℝ) = invLogThetaWeight m := rfl

theorem hasDerivAt_invLogContinuousWeight {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invLogContinuousWeight
      (-(Real.log t + 2) / (t ^ 2 * Real.log t ^ 3)) t := by
  unfold invLogContinuousWeight
  have hlogsq : HasDerivAt (fun s : ℝ => Real.log s ^ 2)
      (2 * Real.log t / t) t := by
    convert (Real.hasDerivAt_log ht).pow 2 using 1
    field_simp [ht]
    ring
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s ^ 2)
      (Real.log t ^ 2 + 2 * Real.log t) t := by
    convert (hasDerivAt_id t).mul hlogsq using 1
    simp only [id_eq]
    field_simp [ht]
  have hden0 : t * Real.log t ^ 2 ≠ 0 :=
    mul_ne_zero ht (pow_ne_zero 2 hlog)
  have hraw := (hasDerivAt_const t (1 : ℝ)).div hden hden0
  convert hraw using 1
  field_simp [ht, hlog]
  ring

theorem invLog_deriv_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    |-(Real.log t + 2) / (t ^ 2 * Real.log t ^ 3)| ≤
      20 / (k : ℝ) ^ 2 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht2 : (2 : ℝ) ≤ t := hkR.trans ht
  have htpos : 0 < t := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
    have hmono : Real.log 2 ≤ Real.log t :=
      Real.log_le_log (by norm_num) ht2
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  have hpoly : (Real.log t + 2) / Real.log t ^ 3 ≤ 20 := by
    apply (div_le_iff₀ (pow_pos hlogpos 3)).2
    have hfac : 0 ≤ (2 * Real.log t - 1) *
        (10 * Real.log t ^ 2 + 5 * Real.log t + 2) := by
      apply mul_nonneg
      · linarith
      · nlinarith [sq_nonneg (Real.log t)]
    nlinarith
  rw [abs_div, abs_neg, abs_mul,
    abs_of_nonneg (sq_nonneg t), abs_of_pos (pow_pos hlogpos 3),
    abs_of_nonneg (by linarith : 0 ≤ Real.log t + 2)]
  calc
    (Real.log t + 2) / (t ^ 2 * Real.log t ^ 3) =
        ((Real.log t + 2) / Real.log t ^ 3) / t ^ 2 := by field_simp
    _ ≤ 20 / t ^ 2 := div_le_div_of_nonneg_right hpoly (sq_nonneg t)
    _ ≤ 20 / (k : ℝ) ^ 2 := by gcongr

theorem invLogWeight_cell_oscillation {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |invLogContinuousWeight s - invLogContinuousWeight t| ≤
      (20 / (k : ℝ) ^ 2) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ invLogContinuousWeight u := by
    have hu2 : (2 : ℝ) ≤ u := (by exact_mod_cast hk : (2 : ℝ) ≤ k).trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (hasDerivAt_invLogContinuousWeight hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv invLogContinuousWeight u‖ ≤ 20 / (k : ℝ) ^ 2 := by
    have hu2 : (2 : ℝ) ≤ u := (by exact_mod_cast hk : (2 : ℝ) ≤ k).trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(hasDerivAt_invLogContinuousWeight hu0 hlogu).deriv,
      Real.norm_eq_abs]
    exact invLog_deriv_bound hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem invLogThetaWeight_abs_le {m : ℕ} (hm : 2 ≤ m) :
    |invLogThetaWeight m| ≤ 4 / (m : ℝ) := by
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (m : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log
      · norm_num
      · exact_mod_cast hm
    nlinarith [Real.log_two_gt_d9]
  have hmpos : (0 : ℝ) < m := by positivity
  have hlogpos : 0 < Real.log (m : ℝ) := by linarith
  rw [invLogThetaWeight, abs_div, abs_one, abs_mul,
    abs_of_pos hmpos, abs_pow, abs_of_pos hlogpos]
  apply (div_le_div_iff₀ (mul_pos hmpos (sq_pos_of_pos hlogpos)) hmpos).2
  nlinarith [sq_nonneg (Real.log (m : ℝ) - 1 / 2)]

theorem invLogWeight_pnt_bound {C : ℝ} (hC : 0 ≤ C)
    {X₀ z Y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzY : z < Y)
    (hlogz : 1 ≤ Real.log (z : ℝ))
    (hlogY : Real.log (Y : ℝ) ≤ 5 * Real.log (z : ℝ)) :
    |primeThetaWeightedInterval invLogThetaWeight z Y -
        integerAbelMain invLogThetaWeight z Y| ≤
      128 * C / Real.log (z : ℝ) ^ 2 := by
  have hlogzpos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by norm_num) hlogz
  have hlogzY : Real.log (z : ℝ) ≤ Real.log (Y : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hzY.le
  have hgeneric := primeThetaWeightedInterval_pnt_bound
    invLogThetaWeight (A := (3 : ℝ)) hbound hX₀z hzY
  simp only [Real.rpow_ofNat] at hgeneric
  have htermY : |invLogThetaWeight Y| *
      (C * ((Y : ℝ) / Real.log (Y : ℝ) ^ (3 : ℕ))) ≤
      4 * C / Real.log (z : ℝ) ^ 2 := by
    have hY0 : (Y : ℝ) ≠ 0 := by
      exact_mod_cast (show Y ≠ 0 by omega)
    calc
      _ ≤ (4 / (Y : ℝ)) *
          (C * ((Y : ℝ) / Real.log (Y : ℝ) ^ 3)) := by
        gcongr
        exact invLogThetaWeight_abs_le (hz.trans hzY.le)
      _ = 4 * C / Real.log (Y : ℝ) ^ 3 := by field_simp [hY0]
      _ ≤ 4 * C / Real.log (z : ℝ) ^ 3 := by gcongr
      _ ≤ 4 * C / Real.log (z : ℝ) ^ 2 := by
        have hfac : 0 ≤ 4 * C := by positivity
        apply div_le_div_of_nonneg_left hfac (pow_pos hlogzpos 2)
        nlinarith [mul_le_mul_of_nonneg_left hlogz hlogzpos.le]
  have htermZ : |invLogThetaWeight (z + 1)| *
      (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) ≤
      4 * C / Real.log (z : ℝ) ^ 2 := by
    have hf := invLogThetaWeight_abs_le (m := z + 1) (by omega)
    have hf' : |invLogThetaWeight (z + 1)| ≤ 4 / (z : ℝ) :=
      hf.trans (by gcongr; omega)
    calc
      _ ≤ (4 / (z : ℝ)) *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ 3)) := by gcongr
      _ = 4 * C / Real.log (z : ℝ) ^ 3 := by field_simp
      _ ≤ 4 * C / Real.log (z : ℝ) ^ 2 := by
        have hfac : 0 ≤ 4 * C := by positivity
        apply div_le_div_of_nonneg_left hfac (pow_pos hlogzpos 2)
        nlinarith [mul_le_mul_of_nonneg_left hlogz hlogzpos.le]
  have hvar : (∑ m ∈ Finset.Ioc z (Y - 1),
      |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ)))) ≤
      120 * C / Real.log (z : ℝ) ^ 2 := by
    have hpoint : ∀ m ∈ Finset.Ioc z (Y - 1),
        |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) ≤
          (20 * C / Real.log (z : ℝ) ^ 3) * (1 / (m : ℝ)) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm2 : 2 ≤ m := hz.trans hm.1.le
      have hdiff : |invLogThetaWeight (m + 1) -
          invLogThetaWeight m| ≤ 20 / (m : ℝ) ^ 2 := by
        rw [← invLogContinuousWeight_nat,
          ← invLogContinuousWeight_nat]
        have hs : ((m + 1 : ℕ) : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
          constructor <;> norm_num
        have ht : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
          constructor <;> norm_num
        simpa using invLogWeight_cell_oscillation hm2 hs ht
      have hlogzm : Real.log (z : ℝ) ≤ Real.log (m : ℝ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hm.1.le
      have hlogmpos : 0 < Real.log (m : ℝ) := hlogzpos.trans_le hlogzm
      calc
        _ ≤ (20 / (m : ℝ) ^ 2) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) := by gcongr
        _ = (20 * C / Real.log (m : ℝ) ^ 3) * (1 / (m : ℝ)) := by
          field_simp
        _ ≤ (20 * C / Real.log (z : ℝ) ^ 3) * (1 / (m : ℝ)) := by
          gcongr
    have hsum : (∑ m ∈ Finset.Ioc z (Y - 1),
        |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3))) ≤
        (20 * C / Real.log (z : ℝ) ^ 3) *
          (∑ m ∈ Finset.Ioc z (Y - 1), 1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun m hm => hpoint m hm
    have hhar : (∑ m ∈ Finset.Ioc z (Y - 1), 1 / (m : ℝ)) ≤
        6 * Real.log (z : ℝ) := by
      calc
        _ ≤ 1 + Real.log (Y : ℝ) := by
          exact (harmonic_Ioc_le (z := z) (y := Y - 1)).trans (by
            have hlogsub : Real.log ((Y - 1 : ℕ) : ℝ) ≤
                Real.log (Y : ℝ) := by
              apply Real.log_le_log
              · exact_mod_cast (show 0 < Y - 1 by omega)
              · exact_mod_cast (Nat.sub_le Y 1)
            linarith)
        _ ≤ 6 * Real.log (z : ℝ) := by linarith
    calc
      _ ≤ (20 * C / Real.log (z : ℝ) ^ 3) *
          (∑ m ∈ Finset.Ioc z (Y - 1), 1 / (m : ℝ)) := hsum
      _ ≤ (20 * C / Real.log (z : ℝ) ^ 3) *
          (6 * Real.log (z : ℝ)) := by gcongr
      _ = 120 * C / Real.log (z : ℝ) ^ 2 := by field_simp; ring
  calc
    _ ≤ |invLogThetaWeight Y| *
          (C * ((Y : ℝ) / Real.log (Y : ℝ) ^ (3 : ℕ))) +
        |invLogThetaWeight (z + 1)| *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) +
        ∑ m ∈ Finset.Ioc z (Y - 1),
          |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ))) := hgeneric
    _ ≤ 4 * C / Real.log (z : ℝ) ^ 2 +
        4 * C / Real.log (z : ℝ) ^ 2 +
        120 * C / Real.log (z : ℝ) ^ 2 := by
      exact add_le_add (add_le_add htermY htermZ) hvar
    _ = 128 * C / Real.log (z : ℝ) ^ 2 := by ring

theorem hasDerivAt_invLogAntiderivative {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invLogAntiderivative
      (invLogContinuousWeight t) t := by
  unfold invLogAntiderivative invLogContinuousWeight
  have hraw := (hasDerivAt_const t (1 : ℝ)).div
    (Real.hasDerivAt_log ht) hlog
  convert hraw.neg using 1
  field_simp [ht, hlog]
  ring

theorem integral_invLogContinuousWeight {z Y : ℕ}
    (hz : 2 ≤ z) (hzY : z ≤ Y) :
    (∫ t in (z : ℝ)..(Y : ℝ), invLogContinuousWeight t) =
      1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ) := by
  have hcont : ContinuousOn invLogAntiderivative
      (Set.Icc (z : ℝ) (Y : ℝ)) := by
    intro t htI
    have ht2 : (2 : ℝ) ≤ t := (by exact_mod_cast hz : (2 : ℝ) ≤ z).trans htI.1
    have ht0 : t ≠ 0 := by linarith
    have hlogt : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (hasDerivAt_invLogAntiderivative ht0 hlogt).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable invLogContinuousWeight
      MeasureTheory.volume (z : ℝ) (Y : ℝ) := by
    have hcontW : ContinuousOn invLogContinuousWeight
        (Set.Icc (z : ℝ) (Y : ℝ)) := by
      intro t htI
      have ht2 : (2 : ℝ) ≤ t := (by exact_mod_cast hz : (2 : ℝ) ≤ z).trans htI.1
      have ht0 : t ≠ 0 := by linarith
      have hlogt : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      exact (hasDerivAt_invLogContinuousWeight ht0 hlogt).continuousAt.continuousWithinAt
    rw [← Set.uIcc_of_le (by exact_mod_cast hzY)] at hcontW
    exact hcontW.intervalIntegrable
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := invLogAntiderivative) (f' := invLogContinuousWeight)
    (by exact_mod_cast hzY) hcont
    (fun t htI => by
      have ht2 : (2 : ℝ) < t := (by exact_mod_cast hz : (2 : ℝ) ≤ z).trans_lt htI.1
      exact hasDerivAt_invLogAntiderivative (by linarith)
        (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)))
    hint
  rw [hfund]
  simp only [invLogAntiderivative]
  ring

theorem invLogWeight_sum_integral_bound {z Y : ℕ}
    (hz : 2 ≤ z) (hzY : z ≤ Y) :
    |(∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) -
        ∫ t in (z : ℝ)..(Y : ℝ), invLogContinuousWeight t| ≤
      40 / (z : ℝ) := by
  have hint : ∀ k ∈ Set.Ico z Y,
      IntervalIntegrable invLogContinuousWeight MeasureTheory.volume
        (k : ℝ) (k + 1 : ℕ) := by
    intro k hk
    rw [Set.mem_Ico] at hk
    have hk2 : 2 ≤ k := hz.trans hk.1
    have hcont : ContinuousOn invLogContinuousWeight
        (Set.Icc (k : ℝ) (k + 1 : ℕ)) := by
      intro t htI
      have ht2 : (2 : ℝ) ≤ t := (by exact_mod_cast hk2 : (2 : ℝ) ≤ k).trans htI.1
      have ht0 : t ≠ 0 := by linarith
      have hlogt : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      exact (hasDerivAt_invLogContinuousWeight ht0 hlogt).continuousAt.continuousWithinAt
    rw [← Set.uIcc_of_le (by norm_num : (k : ℝ) ≤ (k + 1 : ℕ))] at hcont
    exact hcont.intervalIntegrable
  have hosc : ∀ k ∈ Finset.Ico z Y,
      ∀ t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
        |invLogContinuousWeight ((k : ℝ) + 1) -
          invLogContinuousWeight t| ≤ 20 / (k : ℝ) ^ 2 := by
    intro k hk t htI
    rw [Finset.mem_Ico] at hk
    have hk2 : 2 ≤ k := hz.trans hk.1
    have hs : ((k + 1 : ℕ) : ℝ) ∈ Set.Icc (k : ℝ) (k + 1 : ℕ) := by
      constructor <;> norm_num
    have h := invLogWeight_cell_oscillation hk2 hs htI
    simp only [Nat.cast_add, Nat.cast_one] at h
    apply h.trans
    have htI' : (k : ℝ) ≤ t ∧ t ≤ (k : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using htI
    have hdist0 : 0 ≤ (k : ℝ) + 1 - t := by linarith [htI'.2]
    rw [abs_of_nonneg hdist0]
    have hdist1 : (k : ℝ) + 1 - t ≤ 1 := by linarith [htI'.1]
    calc
      _ ≤ (20 / (k : ℝ) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hdist1
          (div_nonneg (by norm_num) (sq_nonneg (k : ℝ)))
      _ = 20 / (k : ℝ) ^ 2 := by ring
  have hR := sum_integral_error_bound invLogContinuousWeight
    (fun k => 20 / (k : ℝ) ^ 2) hzY hint hosc
  simp only [invLogContinuousWeight_nat] at hR
  calc
    _ ≤ ∑ k ∈ Finset.Ico z Y, 20 / (k : ℝ) ^ 2 := hR
    _ = 20 * ∑ k ∈ Finset.Ico z Y, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 20 * (2 / (z : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ico_inv_sq_le (show 1 ≤ z by omega)) (by norm_num)
    _ = 40 / (z : ℝ) := by ring

noncomputable def primeInvLogSum (z Y : ℕ) : ℝ :=
  ∑ p ∈ (Y + 1).primesBelow \ (z + 1).primesBelow,
    1 / ((p : ℝ) * Real.log (p : ℝ))

theorem primeThetaWeightedInterval_invLog (z Y : ℕ) :
    primeThetaWeightedInterval invLogThetaWeight z Y =
      primeInvLogSum z Y := by
  rw [primeThetaWeightedInterval, primeInvLogSum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hpprime.pos) (by exact_mod_cast hpprime.ne_one)
  rw [invLogThetaWeight]
  field_simp [hlog]

theorem primeInvLogSum_contraction_of_bound {C : ℝ} (hC : 0 ≤ C)
    {X₀ z Y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzY : z < Y)
    (hlogz : 1 ≤ Real.log (z : ℝ))
    (hlogY : Real.log (Y : ℝ) ≤ 5 * Real.log (z : ℝ))
    (hsmall : 128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) ≤
      1 / (10 * Real.log (z : ℝ))) :
    primeInvLogSum z Y ≤ 9 / (10 * Real.log (z : ℝ)) := by
  have hlogzpos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by norm_num) hlogz
  have hlogzY : Real.log (z : ℝ) ≤ Real.log (Y : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hzY.le
  have hlogYpos : 0 < Real.log (Y : ℝ) := hlogzpos.trans_le hlogzY
  have hpnt := invLogWeight_pnt_bound hC hbound hX₀z hz hzY hlogz hlogY
  rw [primeThetaWeightedInterval_invLog,
    integerAbelMain_eq_sum_Ioc invLogThetaWeight hzY] at hpnt
  have hriemann := invLogWeight_sum_integral_bound hz hzY.le
  rw [integral_invLogContinuousWeight hz hzY.le] at hriemann
  have htotal : |primeInvLogSum z Y -
      (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ))| ≤
      128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) := by
    calc
      _ = |(primeInvLogSum z Y -
            ∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) +
          ((∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) -
            (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)))| := by ring_nf
      _ ≤ |primeInvLogSum z Y -
            ∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m| +
          |(∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) -
            (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ))| :=
        abs_add_le _ _
      _ ≤ _ := add_le_add hpnt hriemann
  have hmain : 1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ) ≤
      4 / (5 * Real.log (z : ℝ)) := by
    have hfrac : (1 / 5 : ℝ) ≤
        Real.log (z : ℝ) / Real.log (Y : ℝ) := by
      apply (le_div_iff₀ hlogYpos).2
      linarith
    calc
      1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ) =
          (1 - Real.log (z : ℝ) / Real.log (Y : ℝ)) /
            Real.log (z : ℝ) := by field_simp
      _ ≤ (4 / 5 : ℝ) / Real.log (z : ℝ) := by
        exact div_le_div_of_nonneg_right (by linarith) hlogzpos.le
      _ = 4 / (5 * Real.log (z : ℝ)) := by ring
  have hupper : primeInvLogSum z Y ≤
      (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)) +
        (128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ)) := by
    have hsigned := (le_abs_self (primeInvLogSum z Y -
      (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)))).trans htotal
    linarith
  calc
    primeInvLogSum z Y ≤
        (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)) +
          (128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ)) := hupper
    _ ≤ 4 / (5 * Real.log (z : ℝ)) +
          1 / (10 * Real.log (z : ℝ)) := add_le_add hmain hsmall
    _ = 9 / (10 * Real.log (z : ℝ)) := by ring

/-- The contraction estimate has an absolute lower threshold; all analytic
hypotheses are discharged from the medium-strength prime number theorem. -/
theorem exists_primeInvLogSum_contraction_threshold :
    ∃ Z₀ : ℕ, ∀ {z Y : ℕ}, Z₀ ≤ z → z < Y →
      Real.log (Y : ℝ) ≤ 5 * Real.log (z : ℝ) →
      primeInvLogSum z Y ≤ 9 / (10 * Real.log (z : ℝ)) := by
  obtain ⟨C, hCpos, X₀, hbound⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  have hlogTop : Filter.Tendsto (fun z : ℕ => Real.log (z : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Filter.Tendsto
      (fun z : ℕ => (Real.log (z : ℝ))⁻¹)
      Filter.atTop (nhds 0) := hlogTop.inv_tendsto_atTop
  have hlogdiv : Filter.Tendsto
      (fun z : ℕ => Real.log (z : ℝ) / (z : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hsmallT : Filter.Tendsto
      (fun z : ℕ =>
        128 * C * (Real.log (z : ℝ))⁻¹ +
          40 * (Real.log (z : ℝ) / (z : ℝ)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hinvlog).add
      (tendsto_const_nhds.mul hlogdiv) using 1
    norm_num
  have hsmallEvent : ∀ᶠ z : ℕ in Filter.atTop,
      128 * C * (Real.log (z : ℝ))⁻¹ +
          40 * (Real.log (z : ℝ) / (z : ℝ)) ≤ 1 / 10 := by
    have hlt := hsmallT.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))
    filter_upwards [hlt] with z hz
    exact hz.le
  have hlogEvent : ∀ᶠ z : ℕ in Filter.atTop,
      1 ≤ Real.log (z : ℝ) :=
    hlogTop.eventually (Filter.eventually_ge_atTop 1)
  have hall : ∀ᶠ z : ℕ in Filter.atTop,
      X₀ ≤ z ∧ 2 ≤ z ∧ 1 ≤ Real.log (z : ℝ) ∧
        128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) ≤
          1 / (10 * Real.log (z : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (max X₀ 2),
      hlogEvent, hsmallEvent] with z hzbase hlogz hscaled
    have hX₀z : X₀ ≤ z := (le_max_left X₀ 2).trans hzbase
    have hz2 : 2 ≤ z := (le_max_right X₀ 2).trans hzbase
    have hlogpos : 0 < Real.log (z : ℝ) :=
      lt_of_lt_of_le (by norm_num) hlogz
    have hmul :
        (128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ)) *
            Real.log (z : ℝ) ≤ 1 / 10 := by
      calc
        _ = 128 * C * (Real.log (z : ℝ))⁻¹ +
            40 * (Real.log (z : ℝ) / (z : ℝ)) := by
              field_simp [hlogpos.ne']
        _ ≤ 1 / 10 := hscaled
    have hsmall :
        128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) ≤
          (1 / 10) / Real.log (z : ℝ) :=
      (le_div_iff₀ hlogpos).2 hmul
    refine ⟨hX₀z, hz2, hlogz, ?_⟩
    convert hsmall using 1
    ring
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀, ?_⟩
  intro z Y hz hzY hlogY
  obtain ⟨hX₀z, hz2, hlogz, hsmall⟩ := hZ₀ z hz
  exact primeInvLogSum_contraction_of_bound hCpos.le hbound
    hX₀z hz2 hzY hlogz hlogY hsmall


/-- The Dickman integral remains valid when the upper endpoint lies on the
birth face `u = 1`; differentiability is only needed in the open interval. -/
theorem integral_dickmanContinuousWeight_closed_top (X z y : ℝ)
    (hz : 1 < z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 ≤ Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy.le] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    have ht1 : 1 < t := hz.trans_le ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlogne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have hqcont : ContinuousAt (fun s : ℝ => Real.log X / Real.log s) t :=
      continuousAt_const.div (Real.continuousAt_log ht0) hlogne
    exact (continuousAt_const.mul
      (continuous_rho.continuousAt.comp hqcont)).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy.le hcontA
  · intro t ht
    have htI : t ∈ Set.Icc z y := ⟨ht.1.le, ht.2.le⟩
    have hqt6 := (hq t htI).2
    have hlogt : 0 < Real.log t := Real.log_pos (hz.trans ht.1)
    have hlogy : 0 < Real.log y := Real.log_pos (hz.trans hzy)
    have hlogty : Real.log t < Real.log y :=
      Real.strictMonoOn_log (show t ∈ Set.Ioi 0 by
        exact hz.trans ht.1 |>.trans' (by norm_num))
        (show y ∈ Set.Ioi 0 by exact hz.trans hzy |>.trans' (by norm_num)) ht.2
    have hqy1 := (hq y ⟨hzy.le, le_rfl⟩).1
    have hlogX : 0 < Real.log X := by
      have h := (le_div_iff₀ hlogy).mp hqy1
      linarith
    have hqstrict : 1 < Real.log X / Real.log t := by
      have hdiv : Real.log X / Real.log y < Real.log X / Real.log t := by
        exact (div_lt_div_iff_of_pos_left hlogX hlogy hlogt).2 hlogty
      exact hqy1.trans_lt hdiv
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      hqstrict hqt6
  · exact hint

/-- Prime-sum approximation with the upper endpoint allowed on `u = 1`. -/
theorem dickmanPrimeSum_pnt_bound_closed_top (X : ℕ) (hX : 1 ≤ X)
    {C : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤
      500 * C * (X : ℝ) / Real.log (z : ℝ) +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by
  have hpnt := dickmanWeight_pnt_bound X hX hC hbound hX₀z hz hzy hq
  rw [primeThetaWeightedInterval_dickman,
    integerAbelMain_eq_sum_Ioc (dickmanThetaWeight X) hzy] at hpnt
  have hriemann := dickmanWeight_sum_integral_bound X hX hz hzy.le hq
  have hintegral := integral_dickmanContinuousWeight_closed_top
    (X : ℝ) (z : ℝ) (y : ℝ)
    (by exact_mod_cast (show 1 < z by omega))
    (by exact_mod_cast hzy) hq
  rw [hintegral] at hriemann
  calc
    _ = |((∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) +
        ((∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m| +
        |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ))| := abs_add_le _ _
    _ ≤ _ := add_le_add hpnt hriemann

/-- Reverse (complement) method-of-steps inequality.  It starts from an upper
cutoff and solves the exact recursion for the lower cutoff. -/
theorem friableCount_reverse_step_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C E₁ : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6)
    (e : ℕ → ℝ)
    (htop : |(friableCount X y : ℝ) -
        dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤ E₁)
    (hquot : ∀ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
      |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p) :
    |(friableCount X z : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ)| ≤
      E₁ + (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ)) := by
  let P := (y + 1).primesBelow \ (z + 1).primesBelow
  have hrecNat := friableCount_prime_interval X (Nat.succ_le_iff.mp hX) hzy.le
  have hrec : (friableCount X y : ℝ) = (friableCount X z : ℝ) +
      ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by
    exact_mod_cast hrecNat
  have hsum :
      |(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p| ≤
        ∑ p ∈ P, e p := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ P,
          |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P, e p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hquot p (by simpa [P] using hp)
  have hprime := dickmanPrimeSum_pnt_bound_closed_top
    X hX hC hbound hX₀z hz hzy hq
  change |(∑ p ∈ P, dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤ _ at hprime
  have hrearrange : (friableCount X z : ℝ) =
      (friableCount X y : ℝ) -
        ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by linarith
  rw [hrearrange]
  calc
    _ = |((friableCount X y : ℝ) -
          dickmanAntiderivative (X : ℝ) (y : ℝ)) -
        ((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p) -
        ((∑ p ∈ P, dickmanPrimeSummand X p) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(friableCount X y : ℝ) -
          dickmanAntiderivative (X : ℝ) (y : ℝ)| +
        (|(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
            ∑ p ∈ P, dickmanPrimeSummand X p| +
          |(∑ p ∈ P, dickmanPrimeSummand X p) -
            (dickmanAntiderivative (X : ℝ) (y : ℝ) -
              dickmanAntiderivative (X : ℝ) (z : ℝ))|) := by
      calc
        _ = |((friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)) +
            (-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
              ∑ p ∈ P, dickmanPrimeSummand X p) +
            -((∑ p ∈ P, dickmanPrimeSummand X p) -
              (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                dickmanAntiderivative (X : ℝ) (z : ℝ))))| := by ring_nf
        _ ≤ |(friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)| +
            |-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
                ∑ p ∈ P, dickmanPrimeSummand X p) +
              -((∑ p ∈ P, dickmanPrimeSummand X p) -
                (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                  dickmanAntiderivative (X : ℝ) (z : ℝ)))| := abs_add_le _ _
        _ ≤ |(friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)| +
            (|-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
                ∑ p ∈ P, dickmanPrimeSummand X p)| +
              |-((∑ p ∈ P, dickmanPrimeSummand X p) -
                (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                  dickmanAntiderivative (X : ℝ) (z : ℝ)))|) :=
          add_le_add le_rfl (abs_add_le _ _)
        _ = _ := by simp only [abs_neg]
    _ ≤ E₁ + ((∑ p ∈ P, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ))) := by
      exact add_le_add htop (add_le_add hsum hprime)
    _ = _ := by
      dsimp [P]
      ring

theorem friableCount_top_exact {X : ℕ} (hX : 2 ≤ X) :
    (friableCount X X : ℝ) = dickmanAntiderivative (X : ℝ) (X : ℝ) := by
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity)
      (by exact_mod_cast (show X ≠ 1 by omega))
  rw [friableCount_eq_self le_rfl, dickmanAntiderivative,
    div_self hlog, rho_one]
  ring

/-- The number of primes in `(z,Y]` has the elementary Chebyshev bound at
the exact scale needed to sum the uniform floor error. -/
theorem primeInterval_card_le (z Y : ℕ) (hz : 2 ≤ z) :
    (((Y + 1).primesBelow \ (z + 1).primesBelow).card : ℝ) ≤
      Real.log 4 * (Y : ℝ) / Real.log (z : ℝ) := by
  let P := (Y + 1).primesBelow \ (z + 1).primesBelow
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlower : (P.card : ℝ) * Real.log (z : ℝ) ≤
      ∑ p ∈ P, Real.log (p : ℝ) := by
    calc
      _ = ∑ p ∈ P, Real.log (z : ℝ) := by simp [Finset.sum_const]
      _ ≤ ∑ p ∈ P, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpout := (Finset.mem_sdiff.mp hp).2
        have hpz : z < p := by
          by_contra hnot
          apply hpout
          rw [Nat.mem_primesBelow]
          exact ⟨by omega,
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1⟩
        exact Real.log_le_log (by positivity) (by exact_mod_cast hpz.le)
  have hupper : (∑ p ∈ P, Real.log (p : ℝ)) ≤
      Real.log 4 * (Y : ℝ) := by
    calc
      _ ≤ ∑ p ∈ (Y + 1).primesBelow, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
        intro p hp hnot
        have hpprime := Nat.prime_of_mem_primesBelow hp
        exact Real.log_nonneg (by exact_mod_cast hpprime.one_le)
      _ = primeLogSumUpTo Y := rfl
      _ = Chebyshev.theta (Y : ℝ) := primeLogSumUpTo_eq_theta Y
      _ ≤ Real.log 4 * (Y : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
  apply (le_div_iff₀ hlogz).2
  exact hlower.trans hupper

/-- The endpoint Riemann error is eventually at most one copy of the natural
`X / log y` error scale, uniformly for `X ≤ y^5`. -/
theorem exists_dickmanRiemann_remainder_threshold :
    ∃ Y₀ : ℕ, ∀ {y X : ℕ}, Y₀ ≤ y → 2 ≤ y → 1 ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) ≤
        (X : ℝ) / Real.log (y : ℝ) := by
  have hlogdivReal : Filter.Tendsto
      (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogdiv : Filter.Tendsto
      (fun y : ℕ => Real.log (y : ℝ) / (y : ℝ))
      Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply, id_eq] using
      hlogdivReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlogsqdivReal : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (1 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlogsqdiv : Filter.Tendsto
      (fun y : ℕ => Real.log (y : ℝ) ^ 2 / (y : ℝ))
      Filter.atTop (nhds 0) := by
    simpa [Real.rpow_natCast, Real.rpow_one] using
      hlogsqdivReal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have htotal : Filter.Tendsto
      (fun y : ℕ =>
        12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)))
      Filter.atTop (nhds 0) := by
    have h12 : Filter.Tendsto (fun _ : ℕ => (12 : ℝ))
        Filter.atTop (nhds 12) := tendsto_const_nhds
    have h80 : Filter.Tendsto (fun _ : ℕ => (80 : ℝ))
        Filter.atTop (nhds 80) := tendsto_const_nhds
    convert (h12.mul hlogdiv).add (h80.mul hlogsqdiv) using 1
    norm_num
  have hevent : ∀ᶠ y : ℕ in Filter.atTop,
      12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) ≤ 1 := by
    have hlt := htotal.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with y hy
    exact hy.le
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨Y₀, ?_⟩
  intro y X hY₀y hy2 hX hlogX
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hypos : (0 : ℝ) < (y : ℝ) := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hscaled :
      2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ) ≤ 1 := by
    have hinside : 6 + 8 * Real.log (X : ℝ) ≤
        6 + 40 * Real.log (y : ℝ) := by linarith
    calc
      _ = (2 * Real.log (y : ℝ) / (y : ℝ)) *
          (6 + 8 * Real.log (X : ℝ)) := by ring
      _ ≤ (2 * Real.log (y : ℝ) / (y : ℝ)) *
          (6 + 40 * Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ = 2 * (6 + 40 * Real.log (y : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ) := by ring
      _ = 12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) := by ring
      _ ≤ 1 := hY₀ y hY₀y
  apply (le_div_iff₀ hlogy).2
  calc
    (2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ)) *
        Real.log (y : ℝ) =
      (X : ℝ) *
        (2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ)) := by ring
    _ ≤ (X : ℝ) * 1 := mul_le_mul_of_nonneg_left hscaled hXpos.le
    _ = (X : ℝ) := by ring

/-- Uniform finite de Bruijn estimate on the full four-mark coordinate
range.  This is a closed theorem: the PNT, contraction, and endpoint
thresholds are all chosen internally. -/
theorem exists_uniform_friableCount_dickman_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨C, hCpos, X₀, hbound⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  obtain ⟨Zc, hcontract⟩ := exists_primeInvLogSum_contraction_threshold
  obtain ⟨Zr, hriemann⟩ := exists_dickmanRiemann_remainder_threshold
  let K : ℝ := 10 * (500 * C + 3 * Real.log 4 + 1)
  let Y₀ : ℕ := max 2 (max X₀ (max Zc Zr))
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, Y₀, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      intro y hY₀y hyX hlogXy
      have hy2 : 2 ≤ y := (le_max_left 2 (max X₀ (max Zc Zr))).trans hY₀y
      have hypos : 0 < y := by omega
      have hX2 : 2 ≤ X := hy2.trans hyX
      have hXpos : 0 < X := by omega
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      by_cases hyXeq : y = X
      · subst y
        rw [friableCount_top_exact hX2]
        simp only [dickmanAntiderivative, dickmanU, sub_self, abs_zero]
        positivity
      · have hyXlt : y < X := lt_of_le_of_ne hyX hyXeq
        let P := (X + 1).primesBelow \ (y + 1).primesBelow
        let e : ℕ → ℝ := fun p =>
          K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) + 3
        have hX₀y : X₀ ≤ y :=
          (le_max_left X₀ (max Zc Zr)).trans
            ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y)
        have hZcy : Zc ≤ y :=
          (le_max_left Zc Zr).trans
            ((le_max_right X₀ (max Zc Zr)).trans
              ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y))
        have hZry : Zr ≤ y :=
          (le_max_right Zc Zr).trans
            ((le_max_right X₀ (max Zc Zr)).trans
              ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y))
        have hq : ∀ t ∈ Set.Icc (y : ℝ) (X : ℝ),
            1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6 := by
          intro t ht
          have ht1 : 1 < t :=
            (by exact_mod_cast (show 1 < y by omega) : (1 : ℝ) < y).trans_le ht.1
          have hlogt : 0 < Real.log t := Real.log_pos ht1
          have hlogtX : Real.log t ≤ Real.log (X : ℝ) := by
            apply Real.log_le_log (by linarith)
            exact ht.2
          have hlogyt : Real.log (y : ℝ) ≤ Real.log t := by
            apply Real.log_le_log (by positivity)
            exact ht.1
          constructor
          · dsimp [logRatio]
            apply (le_div_iff₀ hlogt).2
            simpa using hlogtX
          · dsimp [logRatio]
            apply (div_le_iff₀ hlogt).2
            linarith
        have hquot : ∀ p ∈ P,
            |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p := by
          intro p hpP
          have hpfull : p ∈ (X + 1).primesBelow \ (y + 1).primesBelow := by
            simpa [P] using hpP
          have hpprime : p.Prime :=
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpfull).1
          have hpX : p ≤ X := by
            have := (Nat.lt_of_mem_primesBelow
              (Finset.mem_sdiff.mp hpfull).1)
            omega
          have hyp : y < p := by
            have hpout := (Finset.mem_sdiff.mp hpfull).2
            by_contra hnot
            apply hpout
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, hpprime⟩
          have hp2 : 2 ≤ p := hpprime.two_le
          have hlogp : 0 < Real.log (p : ℝ) :=
            Real.log_pos (by exact_mod_cast hpprime.one_lt)
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5 := by
            apply (div_le_iff₀ hlogp).2
            linarith
          have hfloor := dickmanPrimeSummand_floor_stability X p hp2 hpX hq5
          have hApos : 1 ≤ X / p :=
            (Nat.le_div_iff_mul_le hpprime.pos).2 (by simpa using hpX)
          have hcount :
              |(friableCount (X / p) p : ℝ) -
                ((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p)| ≤
                K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) := by
            by_cases hpA : p ≤ X / p
            · have hAX : X / p < X := Nat.div_lt_self hXpos hpprime.one_lt
              have hlogAX : Real.log ((X / p : ℕ) : ℝ) ≤
                  Real.log (X : ℝ) := by
                apply Real.log_le_log (by exact_mod_cast hApos)
                exact_mod_cast Nat.div_le_self X p
              have hlogA5 : Real.log ((X / p : ℕ) : ℝ) ≤
                  5 * Real.log (p : ℝ) := by
                have := (div_le_iff₀ hlogp).mp hq5
                exact hlogAX.trans this
              exact ih (X / p) hAX (y := p)
                (hY₀y.trans hyp.le) hpA hlogA5
            · have hAp : X / p ≤ p := le_of_not_ge hpA
              rw [friableCount_eq_dickman_initial hApos hpprime.one_lt hAp,
                sub_self, abs_zero]
              positivity
          calc
            _ ≤ |(friableCount (X / p) p : ℝ) -
                  ((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p)| +
                |((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p) -
                  dickmanPrimeSummand X p| := by
              exact abs_sub_le _ _ _
            _ ≤ K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) + 3 :=
              add_le_add hcount hfloor
            _ = e p := rfl
        have htop : |(friableCount X X : ℝ) -
            dickmanAntiderivative (X : ℝ) (X : ℝ)| ≤ 0 := by
          rw [friableCount_top_exact hX2, sub_self, abs_zero]
        have hreverse := friableCount_reverse_step_pnt_bound
          X hXpos hCpos.le hbound hX₀y hy2 hyXlt hq e htop
          (fun p hp => hquot p (by simpa [P] using hp))
        have hsumA : (∑ p ∈ P,
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) ≤
            K * (X : ℝ) * primeInvLogSum y X := by
          rw [primeInvLogSum]
          calc
            _ ≤ ∑ p ∈ P,
                K * (X : ℝ) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              apply Finset.sum_le_sum
              intro p hpP
              have hpfull : p ∈ (X + 1).primesBelow \ (y + 1).primesBelow := by
                simpa [P] using hpP
              have hpprime : p.Prime :=
                Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpfull).1
              have hlogp : 0 < Real.log (p : ℝ) :=
                Real.log_pos (by exact_mod_cast hpprime.one_lt)
              have hcast : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) :=
                Nat.cast_div_le
              calc
                _ ≤ K * ((X : ℝ) / (p : ℝ)) / Real.log (p : ℝ) := by
                  gcongr
                _ = K * (X : ℝ) *
                    (1 / ((p : ℝ) * Real.log (p : ℝ))) := by field_simp
            _ = K * (X : ℝ) *
                (∑ p ∈ P, 1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              rw [Finset.mul_sum]
            _ = _ := by congr 2
        have hcontractYX : primeInvLogSum y X ≤
            9 / (10 * Real.log (y : ℝ)) :=
          hcontract hZcy hyXlt hlogXy
        have hsumAcontract : (∑ p ∈ P,
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) ≤
            (9 / 10 * K) * (X : ℝ) / Real.log (y : ℝ) := by
          calc
            _ ≤ K * (X : ℝ) * primeInvLogSum y X := hsumA
            _ ≤ K * (X : ℝ) * (9 / (10 * Real.log (y : ℝ))) := by
              gcongr
            _ = (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) := by ring
        have hcard := primeInterval_card_le y X hy2
        have hsume : (∑ p ∈ P, e p) ≤
            (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
              Real.log (y : ℝ) := by
          calc
            _ = (∑ p ∈ P,
                K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) +
                3 * (P.card : ℝ) := by
              simp only [e, Finset.sum_add_distrib, Finset.sum_const,
                nsmul_eq_mul]
              ring
            _ ≤ (9 / 10 * K) * (X : ℝ) / Real.log (y : ℝ) +
                3 * (Real.log 4 * (X : ℝ) / Real.log (y : ℝ)) :=
              add_le_add hsumAcontract (mul_le_mul_of_nonneg_left
                (by simpa [P] using hcard) (by norm_num))
            _ = (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
                Real.log (y : ℝ) := by ring
        have hR := hriemann hZry hy2 hXpos hlogXy
        have hreverse' :
            |(friableCount X y : ℝ) -
                dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤
              (9 / 10 * K + 3 * Real.log 4 + 500 * C + 1) *
                (X : ℝ) / Real.log (y : ℝ) := by
          calc
            _ ≤ 0 + (∑ p ∈ P, e p) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) /
                    (y : ℝ)) := by simpa [P] using hreverse
            _ ≤ (∑ p ∈ P, e p) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  (X : ℝ) / Real.log (y : ℝ)) := by
              simpa only [zero_add] using
                add_le_add le_rfl (add_le_add le_rfl hR)
            _ ≤ (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
                  Real.log (y : ℝ) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  (X : ℝ) / Real.log (y : ℝ)) :=
              add_le_add hsume le_rfl
            _ = (9 / 10 * K + 3 * Real.log 4 + 500 * C + 1) *
                (X : ℝ) / Real.log (y : ℝ) := by ring
        have hcoeff : 9 / 10 * K + 3 * Real.log 4 + 500 * C + 1 = K := by
          dsimp [K]
          ring
        rw [hcoeff] at hreverse'
        simpa only [dickmanAntiderivative] using hreverse'


/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower

/-- Uniform Dickman estimate with the exact initial face included. -/
theorem exists_uniform_friableCount_dickman_bound_all_faces :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₁, hmain⟩ :=
    exists_uniform_friableCount_dickman_bound
  refine ⟨K, hK, max 2 Y₁, ?_⟩
  intro X y hy hX hlog
  have hy2 : 2 ≤ y := (le_max_left 2 Y₁).trans hy
  have hY₁y : Y₁ ≤ y := (le_max_right 2 Y₁).trans hy
  by_cases hyX : y ≤ X
  · exact hmain hY₁y hyX hlog
  · have hXy : X ≤ y := le_of_not_ge hyX
    rw [friableCount_eq_dickman_initial hX (by omega) hXy,
      sub_self, abs_zero]
    positivity

/-- Paper-scale four-mark specialization.  The estimate is stronger than
needed: it holds for every positive divisor `d ≤ floor(y)^4`, without using
smoothness of `d`; smoothness is needed only when the exact marked-cell
reindexing is applied. -/
theorem friableCount_uniform_dickman_four_mark :
    ∃ K₄ : ℝ, 0 < K₄ ∧ ∃ N₀ : ℕ, ∀ {n d : ℕ},
      N₀ ≤ n → 0 < d → d ≤ (yNat n) ^ 4 →
      |(friableCount (n / d) (yNat n) : ℝ) -
          ((n / d : ℕ) : ℝ) * rho (dickmanU (n / d) (yNat n))| ≤
        K₄ * (n : ℝ) / ((d : ℝ) * L n) := by
  obtain ⟨K, hK, Y₀, hmain⟩ :=
    exists_uniform_friableCount_dickman_bound_all_faces
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hyEvent : ∀ᶠ n : ℕ in Filter.atTop,
      ((max Y₀ 2 : ℕ) : ℝ) ≤ y n :=
    hyTop.eventually (Filter.eventually_ge_atTop ((max Y₀ 2 : ℕ) : ℝ))
  obtain ⟨Ny, hNy⟩ := Filter.eventually_atTop.mp hyEvent
  obtain ⟨Nl, hNl⟩ :=
    Filter.eventually_atTop.mp eventually_one_fifth_L_le_log_yNat
  let N₀ : ℕ := max 2 (max Ny Nl)
  refine ⟨5 * K, by positivity, N₀, ?_⟩
  intro n d hN₀n hd hd4
  have hn2 : 2 ≤ n := (le_max_left 2 (max Ny Nl)).trans hN₀n
  have hNyn : Ny ≤ n :=
    (le_max_left Ny Nl).trans
      ((le_max_right 2 (max Ny Nl)).trans hN₀n)
  have hNln : Nl ≤ n :=
    (le_max_right Ny Nl).trans
      ((le_max_right 2 (max Ny Nl)).trans hN₀n)
  have hnpos : 0 < n := by omega
  have hYmax : max Y₀ 2 ≤ yNat n := Nat.le_floor (hNy n hNyn)
  have hY₀yNat : Y₀ ≤ yNat n := (le_max_left Y₀ 2).trans hYmax
  have hyNat2 : 2 ≤ yNat n := (le_max_right Y₀ 2).trans hYmax
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hlogyNat : 0 < Real.log (yNat n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hLpos : 0 < L n := L_pos (by omega)
  have hlogLower := hNl n hNln
  have hlogCoord : Real.log (n : ℝ) ≤
      5 * Real.log (yNat n : ℝ) := by
    dsimp [L] at hlogLower
    linarith
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hnpos))
  have hyPow : ((yNat n : ℕ) : ℝ) ^ 4 ≤ y n ^ 4 := by gcongr
  have hynPowLe : y n ^ 4 ≤ (n : ℝ) := by
    rw [y_pow_four]
    exact Real.rpow_le_self_of_one_le (by exact_mod_cast (show 1 ≤ n by omega))
      (by norm_num : (8 / 9 : ℝ) ≤ 1)
  have hdn : d ≤ n := by
    exact_mod_cast (show (d : ℝ) ≤ (n : ℝ) from
      (by
        calc
          (d : ℝ) ≤ ((yNat n) ^ 4 : ℕ) := by exact_mod_cast hd4
          _ = ((yNat n : ℕ) : ℝ) ^ 4 := by norm_num
          _ ≤ y n ^ 4 := hyPow
          _ ≤ (n : ℝ) := hynPowLe))
  have hXpos : 0 < n / d :=
    (Nat.le_div_iff_mul_le hd).2 (by simpa using hdn)
  have hXle : n / d ≤ n := Nat.div_le_self n d
  have hlogX : Real.log ((n / d : ℕ) : ℝ) ≤
      5 * Real.log (yNat n : ℝ) := by
    have hlogXn : Real.log ((n / d : ℕ) : ℝ) ≤ Real.log (n : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast hXpos)
      exact_mod_cast hXle
    exact hlogXn.trans hlogCoord
  have hraw := hmain hY₀yNat hXpos hlogX
  have hcastDiv : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hinvLog : 1 / Real.log (yNat n : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hlogyNat hLpos).2
    simpa only [one_mul] using hlogCoord
  calc
    _ ≤ K * ((n / d : ℕ) : ℝ) / Real.log (yNat n : ℝ) := hraw
    _ ≤ K * ((n : ℝ) / (d : ℝ)) /
        Real.log (yNat n : ℝ) := by gcongr
    _ = K * ((n : ℝ) / (d : ℝ)) *
        (1 / Real.log (yNat n : ℝ)) := by ring
    _ ≤ K * ((n : ℝ) / (d : ℝ)) * (5 / L n) := by gcongr
    _ = (5 * K) * (n : ℝ) / ((d : ℝ) * L n) := by ring


end Erdos390.Full.FriableAsymptotic
