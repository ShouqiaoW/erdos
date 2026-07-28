import Erdos390.WholePaper.StrongSafePrimeCounting
import Erdos390.WholePaper.UpperScale

/-!
# Safe prime counting in moving short intervals

This module extracts the short-interval consequence that is actually needed
for the bottom marker banks.  The proof does **not** subtract two copies of
the public `O(x / log(x)^2)` remainder for `pi`.  Such a subtraction would
leave an error on the same scale as the desired answer.

Instead, it subtracts the stronger audited estimates
`theta(x) - x = O(x / log(x)^2)`.  At asymptotically linear endpoints this
error is `o(n / log n)`.  The logarithmic weights on a prime interval are
then squeezed between the logarithms of its two endpoints.  Dividing those
weights out supplies the additional logarithm and gives an unweighted prime
count on the scale `n / (log n)^2`.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

noncomputable section

/-- The unweighted prime scale for intervals of length `n / log n`. -/
def shortIntervalPrimeScale (n : ℕ) : ℝ :=
  Erdos390.WholePaper.secondOrderScale n / Real.log (n : ℝ)

private theorem movingEndpoint_cast_tendsto_atTop
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto (fun n : ℕ ↦ (m n : ℝ)) atTop atTop := by
  have hratio :
      ∀ᶠ n : ℕ in atTop, a / 2 ≤ (m n : ℝ) / (n : ℝ) :=
    hm.eventually (eventually_ge_nhds (half_lt_self ha))
  have hbase :
      Tendsto (fun n : ℕ ↦ (a / 2) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (half_pos ha)
  apply tendsto_atTop_mono' atTop _ hbase
  filter_upwards [hratio, eventually_gt_atTop 0] with n hnRatio hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact (le_div_iff₀ hnR).mp hnRatio

/-- Logs at any asymptotically positive linear endpoint can be replaced by
`log n` in a multiplicative limit.  This is one side of the later explicit
logarithmic squeeze. -/
theorem movingEndpoint_log_ratio_tendsto_one
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / Real.log (m n : ℝ))
      atTop (nhds 1) := by
  let u : ℕ → ℝ := fun n ↦ (m n : ℝ) / (n : ℝ)
  have hu : Tendsto u atTop (nhds a) := hm
  have hlogu : Tendsto (fun n ↦ Real.log (u n)) atTop
      (nhds (Real.log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.comp hu
  have hlogn : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun n : ℕ ↦ Real.log (u n) / Real.log (n : ℝ))
      atTop (nhds 0) := by
    simpa using hlogu.div_atTop hlogn
  have hden : Tendsto
      (fun n : ℕ ↦ 1 + Real.log (u n) / Real.log (n : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hinv : Tendsto
      (fun n : ℕ ↦ 1 / (1 + Real.log (u n) / Real.log (n : ℝ)))
      atTop (nhds 1) := by
    have hnum : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    convert hnum.div hden (by norm_num : (1 : ℝ) ≠ 0) using 1
    norm_num
  apply hinv.congr'
  have huPos : ∀ᶠ n : ℕ in atTop, 0 < u n :=
    hu.eventually (eventually_gt_nhds ha)
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  filter_upwards [huPos, eventually_gt_atTop 1,
      hmTop.eventually (eventually_gt_atTop 1)] with n hun hn hmn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlogn : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogm : Real.log (m n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hmn)).ne'
  have humul : u n * (n : ℝ) = (m n : ℝ) := by
    dsimp [u]
    field_simp
  rw [← humul, Real.log_mul hun.ne' hnPos.ne']
  field_simp
  ring

private theorem movingEndpoint_div_log_sq_isLittleO_secondOrderScale
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    (fun n : ℕ ↦ (m n : ℝ) / Real.log (m n : ℝ) ^ 2) =o[atTop]
      Erdos390.WholePaper.secondOrderScale := by
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  have hlogRatio := movingEndpoint_log_ratio_tendsto_one ha hm
  have hinvLog : Tendsto
      (fun n : ℕ ↦ 1 / Real.log (m n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp hmTop).inv_tendsto_atTop
  have hratio0 : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / (n : ℝ)) *
          (Real.log (n : ℝ) / Real.log (m n : ℝ)) *
          (1 / Real.log (m n : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_one, mul_zero] using (hm.mul hlogRatio).mul hinvLog
  have hratio : Tendsto
      (fun n : ℕ ↦
        ((m n : ℝ) / Real.log (m n : ℝ) ^ 2) /
          Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds 0) := by
    apply hratio0.congr'
    filter_upwards [eventually_gt_atTop 1,
        hmTop.eventually (eventually_gt_atTop 1)] with n hn hmn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
    have hlogn : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hlogm : Real.log (m n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hmn)).ne'
    rw [Erdos390.WholePaper.secondOrderScale]
    field_simp
  apply (isLittleO_iff_tendsto' ?_).mpr hratio
  filter_upwards [Erdos390.WholePaper.eventually_secondOrderScale_pos] with
      n hscale hzero
  exact (hscale.ne' hzero).elim

/-- The audited quantitative estimate for `theta` is negligible on the
`n / log n` length scale at every asymptotically positive linear endpoint. -/
theorem theta_movingEndpoint_error_normalized_tendsto_zero
    {m : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a)) :
    Tendsto
      (fun n : ℕ ↦
        (Chebyshev.theta (m n : ℝ) - (m n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds 0) := by
  have hmTop := movingEndpoint_cast_tendsto_atTop ha hm
  have htheta0 :=
    (Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 2).comp_tendsto
      hmTop
  have htheta :
      (fun n : ℕ ↦ Chebyshev.theta (m n : ℝ) - (m n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (m n : ℝ) / Real.log (m n : ℝ) ^ 2) := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq,
      Real.rpow_two] using htheta0
  exact (htheta.trans_isLittleO
    (movingEndpoint_div_log_sq_isLittleO_secondOrderScale ha hm)).tendsto_div_nhds_zero

/-- Subtracting the two endpoint estimates gives the correctly normalized
`theta`-mass of a moving short interval. -/
theorem theta_shortMovingInterval_normalized_tendsto
    {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta)) :
    Tendsto
      (fun n : ℕ ↦
        (Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta) := by
  have hupperError :=
    theta_movingEndpoint_error_normalized_tendsto_zero ha hupper
  have hlowerError :=
    theta_movingEndpoint_error_normalized_tendsto_zero ha hlower
  have htotal := (hupperError.sub hlowerError).add hgap
  have htotal' : Tendsto
      (fun n : ℕ ↦
        (Chebyshev.theta (upper n : ℝ) - (upper n : ℝ)) /
            Erdos390.WholePaper.secondOrderScale n -
          (Chebyshev.theta (lower n : ℝ) - (lower n : ℝ)) /
            Erdos390.WholePaper.secondOrderScale n +
          ((upper n : ℝ) - (lower n : ℝ)) /
            Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta) := by
    simpa using htotal
  apply htotal'.congr'
  filter_upwards [Erdos390.WholePaper.eventually_secondOrderScale_pos] with
      n hscale
  have hscale0 : Erdos390.WholePaper.secondOrderScale n ≠ 0 := hscale.ne'
  field_simp
  ring

/-- Exact identification of the `theta` difference with the logarithmically
weighted primes in a natural half-open interval. -/
theorem theta_natCast_sub_eq_sum_prime_Ioc
    {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log (p : ℝ) := by
  classical
  let small : Finset ℕ := (Finset.Icc 0 a).filter Nat.Prime
  let large : Finset ℕ := (Finset.Icc 0 b).filter Nat.Prime
  have hsubset : small ⊆ large := by
    intro p hp
    simp only [small, large, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩
  have hdiff : large \ small = (Finset.Ioc a b).filter Nat.Prime := by
    ext p
    simp only [small, large, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨⟨_hp0, hpb⟩, hpPrime⟩, hpNotSmall⟩
      have hap : a < p := by
        by_contra hpa
        exact hpNotSmall ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hpa⟩, hpPrime⟩
      exact ⟨⟨hap, hpb⟩, hpPrime⟩
    · rintro ⟨⟨hap, hpb⟩, hpPrime⟩
      exact ⟨⟨⟨Nat.zero_le p, hpb⟩, hpPrime⟩, by
        intro hpSmall
        exact (not_le_of_gt hap) hpSmall.1.2⟩
  rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
  simp only [Nat.floor_natCast]
  change (∑ p ∈ large, Real.log (p : ℝ)) -
      ∑ p ∈ small, Real.log (p : ℝ) = _
  rw [← Finset.sum_sdiff hsubset]
  rw [hdiff]
  ring

/-- On a positive natural interval, the endpoint logarithms give the exact
upper and lower weights needed to squeeze its prime cardinality. -/
theorem prime_Ioc_log_weight_bounds
    {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log (a : ℝ) ≤
        Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) ∧
      Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) ≤
        (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log (b : ℝ) := by
  classical
  let primes := (Finset.Ioc a b).filter Nat.Prime
  have hlower :
      primes.card • Real.log (a : ℝ) ≤
        ∑ p ∈ primes, Real.log (p : ℝ) := by
    apply Finset.card_nsmul_le_sum
    intro p hp
    have hpIoc : a < p ∧ p ≤ b :=
      Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    apply Real.log_le_log (by exact_mod_cast ha)
    exact_mod_cast hpIoc.1.le
  have hupper :
      (∑ p ∈ primes, Real.log (p : ℝ)) ≤
        primes.card • Real.log (b : ℝ) := by
    apply Finset.sum_le_card_nsmul
    intro p hp
    have hpIoc : a < p ∧ p ≤ b :=
      Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1
    have hpPos : 0 < p := ha.trans hpIoc.1
    apply Real.log_le_log (by exact_mod_cast hpPos)
    exact_mod_cast hpIoc.2
  have hexact := theta_natCast_sub_eq_sum_prime_Ioc hab
  constructor
  · simpa only [primes, nsmul_eq_mul, hexact] using hlower
  · simpa only [primes, nsmul_eq_mul, hexact] using hupper

/-- The cardinality of a natural prime interval is the corresponding
difference of the totalized prime-counting function. -/
theorem prime_Ioc_card_eq_primeCounting_sub {a b : ℕ} (hab : a ≤ b) :
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

/-- Safe short-interval PNT at arbitrary moving endpoints.  The hypotheses
make the common linear location and the smaller `n / log n` endpoint gap
fully explicit; the conclusion counts actual primes in `(lower, upper]` on
the finer `n / (log n)^2` scale. -/
theorem prime_Ioc_shortMovingInterval_normalized_tendsto
    {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta))
    (horder : ∀ᶠ n : ℕ in atTop, lower n ≤ upper n) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          shortIntervalPrimeScale n)
      atTop (nhds delta) := by
  have htheta := theta_shortMovingInterval_normalized_tendsto
    ha hlower hupper hgap
  have hlogLower := movingEndpoint_log_ratio_tendsto_one ha hlower
  have hlogUpper := movingEndpoint_log_ratio_tendsto_one ha hupper
  have hlowerLimit := htheta.mul hlogUpper
  have hupperLimit := htheta.mul hlogLower
  have hlowerTop := movingEndpoint_cast_tendsto_atTop ha hlower
  have hupperTop := movingEndpoint_cast_tendsto_atTop ha hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [mul_one] using hlowerLimit)
    (by simpa only [mul_one] using hupperLimit)
  · filter_upwards [horder,
      Erdos390.WholePaper.eventually_secondOrderScale_pos,
      eventually_gt_atTop 1,
      hlowerTop.eventually (eventually_gt_atTop 1),
      hupperTop.eventually (eventually_gt_atTop 1)] with
      n hle hscale hn hlowerOne hupperOne
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    have hlogUpperPos : 0 < Real.log (upper n : ℝ) :=
      Real.log_pos (by exact_mod_cast hupperOne)
    have hbounds := prime_Ioc_log_weight_bounds
      (show 0 < lower n by exact_mod_cast (lt_trans zero_lt_one hlowerOne)) hle
    have hdenPos : 0 < Erdos390.WholePaper.secondOrderScale n /
        Real.log (n : ℝ) := div_pos hscale hlogn
    calc
      ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n) *
          (Real.log (n : ℝ) / Real.log (upper n : ℝ)) =
        ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Real.log (upper n : ℝ)) /
            (Erdos390.WholePaper.secondOrderScale n /
              Real.log (n : ℝ)) := by field_simp
      _ ≤ (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
            (Erdos390.WholePaper.secondOrderScale n /
              Real.log (n : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hdenPos.le
        exact (div_le_iff₀ hlogUpperPos).2 hbounds.2
      _ = (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
            shortIntervalPrimeScale n := rfl
  · filter_upwards [horder,
      Erdos390.WholePaper.eventually_secondOrderScale_pos,
      eventually_gt_atTop 1,
      hlowerTop.eventually (eventually_gt_atTop 1),
      hupperTop.eventually (eventually_gt_atTop 1)] with
      n hle hscale hn hlowerOne _hupperOne
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast hn)
    have hlogLowerPos : 0 < Real.log (lower n : ℝ) :=
      Real.log_pos (by exact_mod_cast hlowerOne)
    have hbounds := prime_Ioc_log_weight_bounds
      (show 0 < lower n by exact_mod_cast (lt_trans zero_lt_one hlowerOne)) hle
    have hdenPos : 0 < Erdos390.WholePaper.secondOrderScale n /
        Real.log (n : ℝ) := div_pos hscale hlogn
    calc
      (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          shortIntervalPrimeScale n =
        (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          (Erdos390.WholePaper.secondOrderScale n /
            Real.log (n : ℝ)) := rfl
      _ ≤ ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Real.log (lower n : ℝ)) /
            (Erdos390.WholePaper.secondOrderScale n /
              Real.log (n : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hdenPos.le
        exact (le_div_iff₀ hlogLowerPos).2 hbounds.1
      _ = ((Chebyshev.theta (upper n : ℝ) -
            Chebyshev.theta (lower n : ℝ)) /
          Erdos390.WholePaper.secondOrderScale n) *
            (Real.log (n : ℝ) / Real.log (lower n : ℝ)) := by field_simp

/-- Equivalent public form phrased as a difference of `Nat.primeCounting`.
The natural subtraction is harmless because endpoint order is an explicit
eventual hypothesis. -/
theorem primeCounting_sub_shortMovingInterval_normalized_tendsto
    {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        Erdos390.WholePaper.secondOrderScale n)
      atTop (nhds delta))
    (horder : ∀ᶠ n : ℕ in atTop, lower n ≤ upper n) :
    Tendsto
      (fun n : ℕ ↦
        ((Nat.primeCounting (upper n) -
            Nat.primeCounting (lower n) : ℕ) : ℝ) /
          shortIntervalPrimeScale n)
      atTop (nhds delta) := by
  apply (prime_Ioc_shortMovingInterval_normalized_tendsto
    ha hlower hupper hgap horder).congr'
  filter_upwards [horder] with n hle
  rw [prime_Ioc_card_eq_primeCounting_sub hle]

end

end Erdos390.WholePaper.SafePrimeCounting
