import Erdos536.PrimeSums

/-!
# Local exponential prime bands

This module packages the shrinking prime intervals used for the anchor
variables.  The lower endpoint is the canonical rounded endpoint
`ceil (exp (T * t))`.  The upper endpoint is obtained by multiplying the
lower endpoint by a fixed factor `exp h` and rounding upward.  Thus the
logarithmic span is asymptotic to `h`, or equivalently the normalized
span is `h / T`.

The main result says that the shifted reciprocal mass of this band,
multiplied by `T`, converges to `h / t`.  In particular, with
`h = c₀ * η`, it is eventually comparable to
`c₀ * (η / T) / t`.
-/

open scoped BigOperators Nat.Prime
open Filter Topology Set

noncomputable section

namespace Erdos536.LocalPrimeBand

open Erdos536.PrimeSums

/-- The lower integer endpoint for a local band at normalized location
`t`. -/
def localLowerEndpoint (T : ℕ) (t : ℝ) : ℕ :=
  expEndpoint t T

/-- The upper endpoint obtained by expanding the lower endpoint through
the fixed logarithmic span `h`. -/
def localUpperEndpoint (T : ℕ) (t h : ℝ) : ℕ :=
  ⌈Real.exp h * (localLowerEndpoint T t : ℝ)⌉₊

/-- The finite set of primes in the integer-endpoint local band. -/
def localPrimeBand (T : ℕ) (t h : ℝ) : Finset ℕ :=
  primesUpTo (localUpperEndpoint T t h) \
    primesUpTo (localLowerEndpoint T t)

/-- Reciprocal prime mass in the local band. -/
def localBandReciprocalMass (T : ℕ) (t h : ℝ) : ℝ :=
  fullReciprocalSum (localUpperEndpoint T t h) -
    fullReciprocalSum (localLowerEndpoint T t)

/-- Shifted reciprocal prime mass in the local band. -/
def localBandShiftedReciprocalMass
    (T : ℕ) (t h : ℝ) : ℝ :=
  fullShiftedReciprocalSum (localUpperEndpoint T t h) -
    fullShiftedReciprocalSum (localLowerEndpoint T t)

@[simp] theorem mem_localPrimeBand {T p : ℕ} {t h : ℝ} :
    p ∈ localPrimeBand T t h ↔
      p.Prime ∧ localLowerEndpoint T t < p ∧
        p ≤ localUpperEndpoint T t h := by
  constructor
  · intro hp
    have hpDiff := Finset.mem_sdiff.mp hp
    have hpUpper : p ≤ localUpperEndpoint T t h ∧ p.Prime := by
      simpa [primesUpTo, localPrimeBand] using hpDiff.1
    have hpNotLower : ¬p ≤ localLowerEndpoint T t := by
      intro hpLower
      apply hpDiff.2
      simp [primesUpTo, hpUpper.2, hpLower]
    exact ⟨hpUpper.2, lt_of_not_ge hpNotLower, hpUpper.1⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [primesUpTo, hpPrime, hpUpper]
    · intro hp
      have hpLe : p ≤ localLowerEndpoint T t := by
        simpa [primesUpTo, hpPrime] using hp
      omega

lemma localLowerEndpoint_pos (T : ℕ) (t : ℝ) :
    0 < localLowerEndpoint T t := by
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

lemma localLowerEndpoint_le_upper {T : ℕ} {t h : ℝ}
    (hh : 0 ≤ h) :
    localLowerEndpoint T t ≤ localUpperEndpoint T t h := by
  have hexp : (1 : ℝ) ≤ Real.exp h := by
    rw [Real.one_le_exp_iff]
    exact hh
  have hlower :
      (localLowerEndpoint T t : ℝ) ≤
        Real.exp h * (localLowerEndpoint T t : ℝ) := by
    exact le_mul_of_one_le_left
      (Nat.cast_nonneg _) hexp
  exact_mod_cast hlower.trans (Nat.le_ceil _)

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter,
    Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

/-- The shifted mass is literally the sum over `localPrimeBand`. -/
theorem localBandShiftedReciprocalMass_eq_sum
    {T : ℕ} {t h : ℝ} (hh : 0 ≤ h) :
    localBandShiftedReciprocalMass T t h =
      ∑ p ∈ localPrimeBand T t h, 1 / ((p : ℝ) + 1) := by
  have hsub := primesUpTo_mono
    (localLowerEndpoint_le_upper (T := T) (t := t) hh)
  simpa only [localBandShiftedReciprocalMass,
    fullShiftedReciprocalSum, localPrimeBand] using
    (Finset.sum_sdiff_eq_sub
      (f := fun p : ℕ => 1 / ((p : ℝ) + 1)) hsub).symm

theorem localBandShiftedReciprocalMass_nonneg
    {T : ℕ} {t h : ℝ} (hh : 0 ≤ h) :
    0 ≤ localBandShiftedReciprocalMass T t h := by
  rw [localBandShiftedReciprocalMass_eq_sum hh]
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- The ordinary reciprocal mass is literally the sum over
`localPrimeBand`. -/
theorem localBandReciprocalMass_eq_sum
    {T : ℕ} {t h : ℝ} (hh : 0 ≤ h) :
    localBandReciprocalMass T t h =
      ∑ p ∈ localPrimeBand T t h, 1 / (p : ℝ) := by
  have hsub := primesUpTo_mono
    (localLowerEndpoint_le_upper (T := T) (t := t) hh)
  simpa only [localBandReciprocalMass,
    fullReciprocalSum, localPrimeBand] using
    (Finset.sum_sdiff_eq_sub
      (f := fun p : ℕ => 1 / (p : ℝ)) hsub).symm

private lemma localUpper_ratio_nonneg_error
    (T : ℕ) (t h : ℝ) :
    0 ≤
      (localUpperEndpoint T t h : ℝ) /
          (localLowerEndpoint T t : ℝ) -
        Real.exp h := by
  have hbase :
      (0 : ℝ) < localLowerEndpoint T t := by
    exact_mod_cast localLowerEndpoint_pos T t
  have hceil :
      Real.exp h * (localLowerEndpoint T t : ℝ) ≤
        (localUpperEndpoint T t h : ℝ) :=
    Nat.le_ceil _
  apply sub_nonneg.mpr
  apply (le_div_iff₀ hbase).mpr
  simpa [mul_comm] using hceil

private lemma localUpper_ratio_error_le
    (T : ℕ) (t h : ℝ) :
    (localUpperEndpoint T t h : ℝ) /
          (localLowerEndpoint T t : ℝ) -
        Real.exp h <
      1 / (localLowerEndpoint T t : ℝ) := by
  have hbase :
      (0 : ℝ) < localLowerEndpoint T t := by
    exact_mod_cast localLowerEndpoint_pos T t
  have hceil :
      (localUpperEndpoint T t h : ℝ) <
        Real.exp h * (localLowerEndpoint T t : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  apply (sub_lt_iff_lt_add).2
  apply (div_lt_iff₀ hbase).2
  calc
    (localUpperEndpoint T t h : ℝ) <
        Real.exp h * (localLowerEndpoint T t : ℝ) + 1 :=
      hceil
    _ =
        (1 / (localLowerEndpoint T t : ℝ) +
          Real.exp h) *
            (localLowerEndpoint T t : ℝ) := by
      field_simp [ne_of_gt hbase]
      ring

lemma localUpper_ratio_tendsto {t h : ℝ} (ht : 0 < t) :
    Tendsto
      (fun T : ℕ =>
        (localUpperEndpoint T t h : ℝ) /
          (localLowerEndpoint T t : ℝ))
      atTop (𝓝 (Real.exp h)) := by
  have hbaseTop :
      Tendsto (fun T : ℕ =>
        (localLowerEndpoint T t : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_iff.mpr
      (expEndpoint_tendsto_atTop ht)
  have hinv :
      Tendsto
        (fun T : ℕ =>
          1 / (localLowerEndpoint T t : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hbaseTop
  have herr :
      Tendsto
        (fun T : ℕ =>
          (localUpperEndpoint T t h : ℝ) /
              (localLowerEndpoint T t : ℝ) -
            Real.exp h)
        atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall
        (fun T => localUpper_ratio_nonneg_error T t h)
    · exact Eventually.of_forall
        (fun T => (localUpper_ratio_error_le T t h).le)
    · exact hinv
  have hadd := herr.add_const (Real.exp h)
  convert hadd using 1 <;> simp

lemma localUpper_log_sub_lower_tendsto {t h : ℝ}
    (ht : 0 < t) :
    Tendsto
      (fun T : ℕ =>
        Real.log (localUpperEndpoint T t h : ℝ) -
          Real.log (localLowerEndpoint T t : ℝ))
      atTop (𝓝 h) := by
  have hratio :=
    (localUpper_ratio_tendsto (h := h) ht).log
      (Real.exp_ne_zero h)
  have heq :
      (fun T : ℕ =>
        Real.log
          ((localUpperEndpoint T t h : ℝ) /
            (localLowerEndpoint T t : ℝ))) =ᶠ[atTop]
      (fun T : ℕ =>
        Real.log (localUpperEndpoint T t h : ℝ) -
          Real.log (localLowerEndpoint T t : ℝ)) := by
    filter_upwards with T
    have hlower :
        (0 : ℝ) < localLowerEndpoint T t := by
      exact_mod_cast localLowerEndpoint_pos T t
    have hupper :
        (0 : ℝ) < localUpperEndpoint T t h := by
      exact_mod_cast
        (Nat.ceil_pos.mpr
          (mul_pos (Real.exp_pos h) hlower))
    rw [Real.log_div hupper.ne' hlower.ne']
  simpa only [Real.log_exp] using hratio.congr' heq

private lemma tendsto_natCast_div_lowerLog {t : ℝ}
    (ht : 0 < t) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) /
          Real.log (localLowerEndpoint T t : ℝ))
      atTop (𝓝 (1 / t)) := by
  have h :
      Tendsto
        (fun T : ℕ =>
          (1 : ℝ) /
            (Real.log (localLowerEndpoint T t : ℝ) /
              (T : ℝ)))
        atTop (𝓝 ((1 : ℝ) / t)) :=
    tendsto_const_nhds.div
      (expEndpoint_log_div_tendsto ht) ht.ne'
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (T : ℝ) ≠ 0 := by
    exact_mod_cast hT.ne'
  change
    1 /
        (Real.log (localLowerEndpoint T t : ℝ) /
          (T : ℝ)) =
      (T : ℝ) /
        Real.log (localLowerEndpoint T t : ℝ)
  field_simp [hTR]

private lemma localLogRelative_scaled_tendsto
    {t h : ℝ} (ht : 0 < t) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) *
          ((Real.log (localUpperEndpoint T t h : ℝ) -
              Real.log (localLowerEndpoint T t : ℝ)) /
            Real.log (localLowerEndpoint T t : ℝ)))
      atTop (𝓝 (h / t)) := by
  have hspan := localUpper_log_sub_lower_tendsto (h := h) ht
  have hscale := tendsto_natCast_div_lowerLog ht
  have hmul := hspan.mul hscale
  have heq :
      (fun T : ℕ =>
        (Real.log (localUpperEndpoint T t h : ℝ) -
            Real.log (localLowerEndpoint T t : ℝ)) *
          ((T : ℝ) /
            Real.log (localLowerEndpoint T t : ℝ))) =ᶠ[atTop]
      (fun T : ℕ =>
        (T : ℝ) *
          ((Real.log (localUpperEndpoint T t h : ℝ) -
              Real.log (localLowerEndpoint T t : ℝ)) /
            Real.log (localLowerEndpoint T t : ℝ))) := by
    filter_upwards with T
    ring
  have hout :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ) *
            ((Real.log (localUpperEndpoint T t h : ℝ) -
                Real.log (localLowerEndpoint T t : ℝ)) /
              Real.log (localLowerEndpoint T t : ℝ)))
        atTop (𝓝 (h * (1 / t))) :=
    hmul.congr' heq
  simpa only [div_eq_mul_inv, one_mul] using hout

private lemma localLogLogDifference_scaled_tendsto
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) *
          (Real.log
              (Real.log (localUpperEndpoint T t h : ℝ)) -
            Real.log
              (Real.log (localLowerEndpoint T t : ℝ))))
      atTop (𝓝 (h / t)) := by
  let g : ℕ → ℝ := fun T =>
    (Real.log (localUpperEndpoint T t h : ℝ) -
        Real.log (localLowerEndpoint T t : ℝ)) /
      Real.log (localLowerEndpoint T t : ℝ)
  have hg :
      Tendsto (fun T : ℕ => (T : ℝ) * g T)
        atTop (𝓝 (h / t)) := by
    simpa only [g] using
      localLogRelative_scaled_tendsto (h := h) ht
  have hlog := Real.tendsto_nat_mul_log_one_add_of_tendsto hg
  apply hlog.congr'
  filter_upwards [
    (expEndpoint_log_tendsto_atTop ht).eventually
      (eventually_gt_atTop (0 : ℝ))] with T hlowerLog
  have hmono :=
    localLowerEndpoint_le_upper (T := T) (t := t) hh
  have hlower :
      (0 : ℝ) < localLowerEndpoint T t := by
    exact_mod_cast localLowerEndpoint_pos T t
  have hupper :
      (0 : ℝ) < localUpperEndpoint T t h := by
    exact_mod_cast lt_of_lt_of_le
      (localLowerEndpoint_pos T t) hmono
  have hlogMono :
      Real.log (localLowerEndpoint T t : ℝ) ≤
        Real.log (localUpperEndpoint T t h : ℝ) :=
    Real.log_le_log hlower (by exact_mod_cast hmono)
  have hupperLog :
      0 < Real.log (localUpperEndpoint T t h : ℝ) :=
    lt_of_lt_of_le hlowerLog hlogMono
  change
    (T : ℝ) * Real.log (1 + g T) =
      (T : ℝ) *
        (Real.log
            (Real.log (localUpperEndpoint T t h : ℝ)) -
          Real.log
            (Real.log (localLowerEndpoint T t : ℝ)))
  congr 1
  have hinside :
      1 + g T =
        Real.log (localUpperEndpoint T t h : ℝ) /
          Real.log (localLowerEndpoint T t : ℝ) := by
    have hlowerLogNe :
        Real.log (localLowerEndpoint T t : ℝ) ≠ 0 := by
      simpa only [localLowerEndpoint] using hlowerLog.ne'
    apply (eq_div_iff hlowerLogNe).2
    dsimp [g]
    field_simp [hlowerLogNe]
    ring
  rw [hinside]
  simpa only [localLowerEndpoint] using
    (Real.log_div hupperLog.ne' hlowerLog.ne')

private lemma scaled_log_cube_error_tendsto_zero
    {t : ℝ} (ht : 0 < t) (C : ℝ) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) *
          (5 * C /
            Real.log (localLowerEndpoint T t : ℝ) ^ 3))
      atTop (𝓝 0) := by
  have hinvT :
      Tendsto (fun T : ℕ => 1 / (T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      tendsto_natCast_atTop_atTop
  have hinvT2 :
      Tendsto (fun T : ℕ => (1 / (T : ℝ)) ^ 2)
        atTop (𝓝 0) := by
    simpa using hinvT.pow 2
  have hlogDiv := expEndpoint_log_div_tendsto ht
  have hlogInvCube :
      Tendsto
        (fun T : ℕ =>
          (Real.log (localLowerEndpoint T t : ℝ) /
            (T : ℝ))⁻¹ ^ 3)
        atTop (𝓝 (t⁻¹ ^ 3)) := by
    exact (hlogDiv.inv₀ ht.ne').pow 3
  have hprod :=
    (hinvT2.mul hlogInvCube).const_mul (5 * C)
  have hprod' :
      Tendsto
        (fun T : ℕ =>
          5 * C *
            ((1 / (T : ℝ)) ^ 2 *
              (Real.log (localLowerEndpoint T t : ℝ) /
                (T : ℝ))⁻¹ ^ 3))
        atTop (𝓝 0) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hTR : (T : ℝ) ≠ 0 := by
    exact_mod_cast hT.ne'
  have hlowerLog : Real.log
      (localLowerEndpoint T t : ℝ) ≠ 0 := by
    have hlogpos :
        0 < Real.log (localLowerEndpoint T t : ℝ) := by
      have hTt : 0 < (T : ℝ) * t :=
        mul_pos (by exact_mod_cast hT) ht
      have hceil :
          Real.exp ((T : ℝ) * t) ≤
            (localLowerEndpoint T t : ℝ) :=
        Nat.le_ceil _
      have hone :
          (1 : ℝ) <
            (localLowerEndpoint T t : ℝ) := by
        calc
          (1 : ℝ) < Real.exp ((T : ℝ) * t) :=
            (Real.one_lt_exp_iff).2 hTt
          _ ≤ _ := hceil
      exact Real.log_pos hone
    exact hlogpos.ne'
  change
    5 * C *
        ((1 / (T : ℝ)) ^ 2 *
          (Real.log (localLowerEndpoint T t : ℝ) /
            (T : ℝ))⁻¹ ^ 3) =
      (T : ℝ) *
        (5 * C /
          Real.log (localLowerEndpoint T t : ℝ) ^ 3)
  field_simp [hTR, hlowerLog]

private lemma localReciprocalQuadratureError_scaled_tendsto_zero
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) *
          (localBandReciprocalMass T t h -
            (Real.log
                (Real.log (localUpperEndpoint T t h : ℝ)) -
              Real.log
                (Real.log (localLowerEndpoint T t : ℝ)))))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  have hupper := scaled_log_cube_error_tendsto_zero ht C
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero'
  · exact Eventually.of_forall (fun T => abs_nonneg _)
  · filter_upwards [
      (expEndpoint_tendsto_atTop ht).eventually
        (eventually_ge_atTop X₀)] with T hcut
    change
      |(T : ℝ) *
          (localBandReciprocalMass T t h -
            (Real.log
                (Real.log (localUpperEndpoint T t h : ℝ)) -
              Real.log
                (Real.log (localLowerEndpoint T t : ℝ))))| ≤
        (T : ℝ) *
          (5 * C /
            Real.log (localLowerEndpoint T t : ℝ) ^ 3)
    have hTnonneg : (0 : ℝ) ≤ T := by positivity
    have hbound :=
      hquad (localLowerEndpoint T t)
        (localUpperEndpoint T t h) hcut
        (localLowerEndpoint_le_upper
          (T := T) (t := t) hh)
    rw [abs_mul, abs_of_nonneg hTnonneg]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [localBandReciprocalMass] using hbound)
      hTnonneg
  · simpa only [abs_zero] using hupper

/-- The reciprocal mass of a local logarithmic cell has the expected
first-order size `h / (T*t)`. -/
theorem localBandReciprocalMass_scaled_tendsto
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) * localBandReciprocalMass T t h)
      atTop (𝓝 (h / t)) := by
  have herr :=
    localReciprocalQuadratureError_scaled_tendsto_zero ht hh
  have hmain :=
    localLogLogDifference_scaled_tendsto ht hh
  have hadd := herr.add hmain
  have heq :
      (fun T : ℕ =>
        (T : ℝ) *
            (localBandReciprocalMass T t h -
              (Real.log
                  (Real.log (localUpperEndpoint T t h : ℝ)) -
                Real.log
                  (Real.log (localLowerEndpoint T t : ℝ)))) +
          (T : ℝ) *
            (Real.log
                (Real.log (localUpperEndpoint T t h : ℝ)) -
              Real.log
                (Real.log (localLowerEndpoint T t : ℝ)))) =ᶠ[atTop]
      (fun T : ℕ =>
        (T : ℝ) * localBandReciprocalMass T t h) := by
    filter_upwards with T
    ring
  simpa only [zero_add] using hadd.congr' heq

private lemma natCast_div_localLower_tendsto_zero
    {t : ℝ} (ht : 0 < t) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) / (localLowerEndpoint T t : ℝ))
      atTop (𝓝 0) := by
  have hexp :
      Tendsto
        (fun x : ℝ =>
          x ^ (1 : ℝ) * Real.exp (-t * x))
        atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      1 t ht
  have hexpNat := hexp.comp tendsto_natCast_atTop_atTop
  have hupper :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ) * Real.exp (-t * (T : ℝ)))
        atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hexpNat
  apply squeeze_zero'
  · exact Eventually.of_forall (fun T => by positivity)
  · exact Eventually.of_forall (fun T => by
      have hbase :
          Real.exp ((T : ℝ) * t) ≤
            (localLowerEndpoint T t : ℝ) :=
        Nat.le_ceil _
      have hbasePos :
          (0 : ℝ) < localLowerEndpoint T t := by
        exact_mod_cast localLowerEndpoint_pos T t
      have hexpPos : 0 < Real.exp ((T : ℝ) * t) :=
        Real.exp_pos _
      calc
        (T : ℝ) / (localLowerEndpoint T t : ℝ) ≤
            (T : ℝ) / Real.exp ((T : ℝ) * t) := by
          exact div_le_div_of_nonneg_left
            (Nat.cast_nonneg T) hexpPos hbase
        _ = (T : ℝ) * Real.exp (-t * (T : ℝ)) := by
          rw [div_eq_mul_inv, ← Real.exp_neg]
          congr 2
          ring)
  · exact hupper

private lemma localShiftedDifference_scaled_tendsto_zero
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) *
          (localBandShiftedReciprocalMass T t h -
            localBandReciprocalMass T t h))
      atTop (𝓝 0) := by
  have hupper := natCast_div_localLower_tendsto_zero ht
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero'
  · exact Eventually.of_forall (fun T => abs_nonneg _)
  · exact Eventually.of_forall (fun T => by
      change
        |(T : ℝ) *
            (localBandShiftedReciprocalMass T t h -
              localBandReciprocalMass T t h)| ≤
          (T : ℝ) /
            (localLowerEndpoint T t : ℝ)
      have hTnonneg : (0 : ℝ) ≤ T := by positivity
      rw [abs_mul, abs_of_nonneg hTnonneg,
        abs_sub_comm]
      have hbound :=
        reciprocal_interval_sub_shifted_abs_le
          (localLowerEndpoint T t)
          (localUpperEndpoint T t h)
          (localLowerEndpoint_pos T t)
          (localLowerEndpoint_le_upper
            (T := T) (t := t) hh)
      have hbound' :
          |localBandReciprocalMass T t h -
              localBandShiftedReciprocalMass T t h| ≤
            1 / (localLowerEndpoint T t : ℝ) := by
        simpa only [localBandReciprocalMass,
          localBandShiftedReciprocalMass] using hbound
      exact mul_le_mul_of_nonneg_left
        (by simpa only [div_eq_mul_inv, one_mul] using hbound')
        hTnonneg)
  · simpa only [abs_zero, div_eq_mul_inv] using hupper

/-- The shifted reciprocal mass, which is the probability weight used by
the anchor construction, has the same local asymptotic. -/
theorem localBandShiftedReciprocalMass_scaled_tendsto
    {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) * localBandShiftedReciprocalMass T t h)
      atTop (𝓝 (h / t)) := by
  have hdiff :=
    localShiftedDifference_scaled_tendsto_zero ht hh
  have hmass :=
    localBandReciprocalMass_scaled_tendsto ht hh
  have hadd := hdiff.add hmass
  have heq :
      (fun T : ℕ =>
        (T : ℝ) *
            (localBandShiftedReciprocalMass T t h -
              localBandReciprocalMass T t h) +
          (T : ℝ) * localBandReciprocalMass T t h) =ᶠ[atTop]
      (fun T : ℕ =>
        (T : ℝ) *
          localBandShiftedReciprocalMass T t h) := by
    filter_upwards with T
    ring
  simpa only [zero_add] using hadd.congr' heq

/-- Compact-location form of the local band limit.  Writing
`w = η / T`, the band has normalized width `c₀*w` and shifted reciprocal
mass asymptotic to `c₀*w/t`. -/
theorem normalizedLocalBand_scaled_tendsto
    {r₀ t r₁ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ t)
    (_htr₁ : t ≤ r₁) (_hr₁ : r₁ < 1)
    (hc₀ : 0 < c₀) (hη : 0 < η) :
    Tendsto
      (fun T : ℕ =>
        (T : ℝ) *
          localBandShiftedReciprocalMass T t (c₀ * η))
      atTop (𝓝 (c₀ * η / t)) :=
  localBandShiftedReciprocalMass_scaled_tendsto
    (hr₀.trans_le hr₀t) (mul_nonneg hc₀.le hη.le)

/-- Eventual two-sided comparability on a fixed compact normalized
location.  This is the direct finite lower bound used to select anchor
primes. -/
theorem eventually_normalizedLocalBand_comparable
    {r₀ t r₁ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ t)
    (htr₁ : t ≤ r₁) (hr₁ : r₁ < 1)
    (hc₀ : 0 < c₀) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      c₀ * η / (2 * t) ≤
          (T : ℝ) *
            localBandShiftedReciprocalMass T t (c₀ * η) ∧
      (T : ℝ) *
            localBandShiftedReciprocalMass T t (c₀ * η) ≤
        2 * (c₀ * η / t) := by
  have ht : 0 < t := hr₀.trans_le hr₀t
  have hlim :=
    normalizedLocalBand_scaled_tendsto
      hr₀ hr₀t htr₁ hr₁ hc₀ hη
  have htarget : 0 < c₀ * η / t := by positivity
  have hball :
      Metric.ball (c₀ * η / t) (c₀ * η / (2 * t)) ∈
        𝓝 (c₀ * η / t) :=
    Metric.ball_mem_nhds _ (by positivity)
  have hev := hlim.eventually hball
  filter_upwards [hev] with T hT
  rw [Real.dist_eq, abs_lt] at hT
  have hradius :
      c₀ * η / (2 * t) = (c₀ * η / t) / 2 := by
    field_simp [ht.ne']
  rw [hradius] at hT ⊢
  constructor <;> linarith

/-- Unscaled lower bound in the customary `w = η/T` notation. -/
theorem eventually_normalizedLocalBand_lower
    {r₀ t r₁ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ t)
    (htr₁ : t ≤ r₁) (hr₁ : r₁ < 1)
    (hc₀ : 0 < c₀) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      c₀ * (η / (T : ℝ)) / (2 * t) ≤
        localBandShiftedReciprocalMass T t (c₀ * η) := by
  filter_upwards [
    eventually_normalizedLocalBand_comparable
      hr₀ hr₀t htr₁ hr₁ hc₀ hη,
    eventually_gt_atTop 0] with T hbound hT
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hlower := hbound.1
  calc
    c₀ * (η / (T : ℝ)) / (2 * t) =
        (c₀ * η / (2 * t)) / (T : ℝ) := by ring
    _ ≤ localBandShiftedReciprocalMass T t (c₀ * η) := by
      apply (div_le_iff₀ hTR).2
      simpa only [mul_comm] using hlower

end Erdos536.LocalPrimeBand
