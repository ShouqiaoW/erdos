import Erdos536.PrimeSums

/-!
# Prime-band time change

For a prime of size `p ≤ exp T`, put

`u = log p / T`,  `depth = -log u`.

A fixed depth cell `(r,s]` therefore corresponds to the exponential
prime band with normalized logarithmic coordinates
`[exp (-s), exp (-r))`.  Prime harmonic mass becomes Lebesgue mass in
the depth coordinate.

For the growing broad band we use the general lower endpoint `p > T`.
Its normalized logarithmic coordinate `log T / T` tends to zero, so its
depth horizon tends to infinity.  This choice avoids any rounding or
real-power bookkeeping while retaining exactly the asymptotic regime
needed by the categorical construction.
-/

open scoped BigOperators Nat.Prime
open Filter Topology Set

noncomputable section

namespace Erdos536.PrimeBandTimeChange

open Erdos536.PrimeSums

/-! ## Fixed depth cells -/

/-- Normalized logarithmic coordinate `u = log p / T`. -/
def normalizedLogCoordinate (T p : ℕ) : ℝ :=
  Real.log (p : ℝ) / (T : ℝ)

/-- Depth coordinate `-log u` associated with a prime. -/
def primeDepth (T p : ℕ) : ℝ :=
  -Real.log (normalizedLogCoordinate T p)

/-- The normalized logarithmic coordinate at depth `s`. -/
def depthCoordinate (s : ℝ) : ℝ :=
  Real.exp (-s)

/-- Primes whose depths lie in the fixed cell `(r,s]`, up to harmless
integer-endpoint conventions. -/
def depthPrimeBand (T : ℕ) (r s : ℝ) : Finset ℕ :=
  primesUpTo (expEndpoint (depthCoordinate r) T) \
    primesUpTo (expEndpoint (depthCoordinate s) T)

/-- Shifted reciprocal mass of a fixed depth cell. -/
def depthBandShiftedMass (T : ℕ) (r s : ℝ) : ℝ :=
  expBandShiftedReciprocalMass T
    (depthCoordinate s) (depthCoordinate r)

/-- One-label intensity when each prime is assigned to a specified one
of three labels with equal weight. -/
def depthBandOneThirdIntensity (T : ℕ) (r s : ℝ) : ℝ :=
  depthBandShiftedMass T r s / 3

lemma depthCoordinate_pos (s : ℝ) :
    0 < depthCoordinate s :=
  Real.exp_pos _

lemma depthCoordinate_antitone {r s : ℝ} (hrs : r ≤ s) :
    depthCoordinate s ≤ depthCoordinate r := by
  unfold depthCoordinate
  rw [Real.exp_le_exp]
  linarith

@[simp] theorem mem_depthPrimeBand {T p : ℕ} {r s : ℝ} :
    p ∈ depthPrimeBand T r s ↔
      p.Prime ∧ expEndpoint (depthCoordinate s) T < p ∧
        p ≤ expEndpoint (depthCoordinate r) T := by
  constructor
  · intro hp
    have hpDiff := Finset.mem_sdiff.mp hp
    have hpUpper :
        p ≤ expEndpoint (depthCoordinate r) T ∧ p.Prime := by
      simpa [depthPrimeBand, primesUpTo] using hpDiff.1
    have hpNotLower :
        ¬p ≤ expEndpoint (depthCoordinate s) T := by
      intro hpLower
      apply hpDiff.2
      simp [primesUpTo, hpUpper.2, hpLower]
    exact ⟨hpUpper.2, lt_of_not_ge hpNotLower, hpUpper.1⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [primesUpTo, hpPrime, hpUpper]
    · intro hp
      have hpLe : p ≤ expEndpoint (depthCoordinate s) T := by
        simpa [primesUpTo, hpPrime] using hp
      omega

theorem depthBandShiftedMass_eq_sum {T : ℕ} {r s : ℝ}
    (hrs : r ≤ s) :
    depthBandShiftedMass T r s =
      ∑ p ∈ depthPrimeBand T r s, 1 / ((p : ℝ) + 1) := by
  have hmono :=
    expEndpoint_mono (depthCoordinate_antitone hrs) T
  have hsub :
      primesUpTo (expEndpoint (depthCoordinate s) T) ⊆
        primesUpTo (expEndpoint (depthCoordinate r) T) := by
    intro p hp
    simp only [primesUpTo, Finset.mem_filter,
      Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hmono⟩, hp.2⟩
  simpa only [depthBandShiftedMass,
    expBandShiftedReciprocalMass,
    fullShiftedReciprocalSum, depthPrimeBand] using
    (Finset.sum_sdiff_eq_sub
      (f := fun p : ℕ => 1 / ((p : ℝ) + 1)) hsub).symm

/-- Prime harmonic mass is exactly Lebesgue length after the fixed
depth time change. -/
theorem depthBandShiftedMass_tendsto {r s : ℝ}
    (hrs : r ≤ s) :
    Tendsto (fun T : ℕ => depthBandShiftedMass T r s)
      atTop (𝓝 (s - r)) := by
  have h :=
    expBandShiftedReciprocalMass_tendsto
      (a := depthCoordinate s) (b := depthCoordinate r)
      (depthCoordinate_pos s) (depthCoordinate_antitone hrs)
  have hlimit :
      Real.log
          (depthCoordinate r / depthCoordinate s) =
        s - r := by
    unfold depthCoordinate
    rw [Real.log_div (Real.exp_ne_zero _)
      (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
    ring
  simpa only [depthBandShiftedMass, hlimit] using h

/-- A specified one of three equiprobable labels has intensity
`(s-r)/3` on the depth cell. -/
theorem depthBandOneThirdIntensity_tendsto {r s : ℝ}
    (hrs : r ≤ s) :
    Tendsto
      (fun T : ℕ => depthBandOneThirdIntensity T r s)
      atTop (𝓝 ((s - r) / 3)) := by
  exact (depthBandShiftedMass_tendsto hrs).div_const 3

/-! ## A growing broad band -/

/-- The broad band `T < p ≤ exp(T*a)`.  Its lower normalized
logarithmic coordinate is `log T / T`, which tends to zero. -/
def broadPrimeBand (T : ℕ) (a : ℝ) : Finset ℕ :=
  primesUpTo (expEndpoint a T) \ primesUpTo T

/-- The normalized first logarithmic moment with weight `1/p` on the
broad band. -/
def broadBandLogMoment (T : ℕ) (a : ℝ) : ℝ :=
  (fullLogReciprocalSum (expEndpoint a T) -
    fullLogReciprocalSum T) / (T : ℝ)

/-- The full logarithmic prime sum with the probability denominator
`p+1`. -/
def fullShiftedLogReciprocalSum (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y,
    Real.log (p : ℝ) / ((p : ℝ) + 1)

/-- The normalized shifted logarithmic moment on the broad band. -/
def broadBandShiftedLogMoment (T : ℕ) (a : ℝ) : ℝ :=
  (fullShiftedLogReciprocalSum (expEndpoint a T) -
    fullShiftedLogReciprocalSum T) / (T : ℝ)

@[simp] theorem mem_broadPrimeBand {T p : ℕ} {a : ℝ} :
    p ∈ broadPrimeBand T a ↔
      p.Prime ∧ T < p ∧ p ≤ expEndpoint a T := by
  constructor
  · intro hp
    have hpDiff := Finset.mem_sdiff.mp hp
    have hpUpper : p ≤ expEndpoint a T ∧ p.Prime := by
      simpa [broadPrimeBand, primesUpTo] using hpDiff.1
    have hpNotLower : ¬p ≤ T := by
      intro hpLower
      apply hpDiff.2
      simp [primesUpTo, hpUpper.2, hpLower]
    exact ⟨hpUpper.2, lt_of_not_ge hpNotLower, hpUpper.1⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [primesUpTo, hpPrime, hpUpper]
    · intro hp
      have hpLe : p ≤ T := by
        simpa [primesUpTo, hpPrime] using hp
      omega

private lemma eventually_nat_le_expEndpoint {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T : ℕ in atTop, T ≤ expEndpoint a T := by
  have hgrowth :
      Tendsto
        (fun x : ℝ => Real.exp (a * x) / x ^ (1 : ℝ))
        atTop atTop :=
    tendsto_exp_mul_div_rpow_atTop 1 a ha
  have hnat := hgrowth.comp tendsto_natCast_atTop_atTop
  filter_upwards [
    hnat.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_gt_atTop 0] with T hratio hT
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hexp :
      (T : ℝ) ≤ Real.exp ((T : ℝ) * a) := by
    have hratio' :
        (1 : ℝ) ≤
          Real.exp (a * (T : ℝ)) / (T : ℝ) := by
      simpa only [Function.comp_apply, Real.rpow_one] using hratio
    have h := (le_div_iff₀ hTR).mp hratio'
    calc
      (T : ℝ) ≤ Real.exp (a * (T : ℝ)) := by
        simpa only [one_mul, mul_one] using h
      _ = Real.exp ((T : ℝ) * a) := by
        congr 1
        ring
  exact_mod_cast hexp.trans (Nat.le_ceil _)

private lemma log_natCast_div_tendsto_zero :
    Tendsto (fun T : ℕ => Real.log (T : ℝ) / (T : ℝ))
      atTop (𝓝 0) := by
  have h :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop
  simpa only [id_eq, Function.comp_apply] using h

private lemma log_natCast_tendsto_atTop :
    Tendsto (fun T : ℕ => Real.log (T : ℝ))
      atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private lemma log_natCast_cube_tendsto_atTop :
    Tendsto (fun T : ℕ => Real.log (T : ℝ) ^ 3)
      atTop atTop := by
  simpa [Function.comp_def, Real.rpow_natCast] using
    (tendsto_rpow_atTop
      (by norm_num : (0 : ℝ) < 3)).comp
        log_natCast_tendsto_atTop

private lemma broadMainLogMoment_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℕ =>
        (Real.log (expEndpoint a T : ℝ) -
          Real.log (T : ℝ)) / (T : ℝ))
      atTop (𝓝 a) := by
  have hsub :=
    (expEndpoint_log_div_tendsto ha).sub
      log_natCast_div_tendsto_zero
  have heq :
      (fun T : ℕ =>
        Real.log (expEndpoint a T : ℝ) / (T : ℝ) -
          Real.log (T : ℝ) / (T : ℝ)) =ᶠ[atTop]
      (fun T : ℕ =>
        (Real.log (expEndpoint a T : ℝ) -
          Real.log (T : ℝ)) / (T : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hTR : (T : ℝ) ≠ 0 := by
      exact_mod_cast hT.ne'
    field_simp [hTR]
  simpa only [sub_zero] using hsub.congr' heq

/-- The unshifted normalized first log moment on the growing broad band
converges to its normalized-coordinate length. -/
theorem broadBandLogMoment_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℕ => broadBandLogMoment T a)
      atTop (𝓝 a) := by
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullLogReciprocalSum_interval_error_bound
  have hmain := broadMainLogMoment_tendsto ha
  have htwo :
      Tendsto (fun T : ℕ => (2 : ℝ) / (T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      tendsto_natCast_atTop_atTop
  have hinner :
      Tendsto
        (fun T : ℕ =>
          (2 + (Real.log (expEndpoint a T : ℝ) -
            Real.log (T : ℝ))) / (T : ℝ))
        atTop (𝓝 a) := by
    have hadd := htwo.add hmain
    have heq :
        (fun T : ℕ =>
          (2 : ℝ) / (T : ℝ) +
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ)) / (T : ℝ)) =ᶠ[atTop]
        (fun T : ℕ =>
          (2 + (Real.log (expEndpoint a T : ℝ) -
            Real.log (T : ℝ))) / (T : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with T hT
      have hTR : (T : ℝ) ≠ 0 := by
        exact_mod_cast hT.ne'
      field_simp [hTR]
    simpa only [zero_add] using hadd.congr' heq
  have hnum :
      Tendsto
        (fun T : ℕ =>
          C * ((2 +
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ)))
        atTop (𝓝 (C * a)) :=
    hinner.const_mul C
  have hupper :
      Tendsto
        (fun T : ℕ =>
          (C * ((2 +
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ))) /
            Real.log (T : ℝ) ^ 3)
        atTop (𝓝 0) :=
    hnum.div_atTop log_natCast_cube_tendsto_atTop
  have herr :
      Tendsto
        (fun T : ℕ =>
          (fullLogReciprocalSum (expEndpoint a T) -
            fullLogReciprocalSum T -
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ))
        atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    apply squeeze_zero'
    · exact Eventually.of_forall (fun T => abs_nonneg _)
    · filter_upwards [
        eventually_ge_atTop X₀,
        eventually_ge_atTop 2,
        eventually_nat_le_expEndpoint ha,
        eventually_gt_atTop 0] with T hcut hT2 hTY hT
      have hTR : (0 : ℝ) < T := by exact_mod_cast hT
      have hbound :=
        hquad T (expEndpoint a T) hcut hTY
      change
        |(fullLogReciprocalSum (expEndpoint a T) -
            fullLogReciprocalSum T -
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ)| ≤
          (C * ((2 +
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ))) /
            Real.log (T : ℝ) ^ 3
      rw [abs_div, abs_of_pos hTR]
      calc
        |fullLogReciprocalSum (expEndpoint a T) -
              fullLogReciprocalSum T -
              (Real.log (expEndpoint a T : ℝ) -
                Real.log (T : ℝ))| /
            (T : ℝ) ≤
          (C * (2 +
              (Real.log (expEndpoint a T : ℝ) -
                Real.log (T : ℝ))) /
              Real.log (T : ℝ) ^ 3) /
            (T : ℝ) :=
          div_le_div_of_nonneg_right hbound hTR.le
        _ =
          (C * ((2 +
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ))) /
            Real.log (T : ℝ) ^ 3 := by
          ring
    · simpa only [abs_zero] using hupper
  have hadd := herr.add hmain
  have heq :
      (fun T : ℕ =>
        (fullLogReciprocalSum (expEndpoint a T) -
            fullLogReciprocalSum T -
            (Real.log (expEndpoint a T : ℝ) -
              Real.log (T : ℝ))) / (T : ℝ) +
          (Real.log (expEndpoint a T : ℝ) -
            Real.log (T : ℝ)) / (T : ℝ)) =ᶠ[atTop]
      (fun T : ℕ => broadBandLogMoment T a) := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hTR : (T : ℝ) ≠ 0 := by
      exact_mod_cast hT.ne'
    simp only [broadBandLogMoment]
    field_simp [hTR]
    ring
  simpa only [zero_add] using hadd.congr' heq

/-! ## Shifted first moment and deep tails -/

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter,
    Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

theorem broadBandLogMoment_eq_sum {T : ℕ} {a : ℝ}
    (hTY : T ≤ expEndpoint a T) :
    broadBandLogMoment T a =
      (∑ p ∈ broadPrimeBand T a,
        Real.log (p : ℝ) / (p : ℝ)) / (T : ℝ) := by
  have hsub := primesUpTo_mono hTY
  have hsum :
      fullLogReciprocalSum (expEndpoint a T) -
          fullLogReciprocalSum T =
        ∑ p ∈ broadPrimeBand T a,
          Real.log (p : ℝ) / (p : ℝ) := by
    simpa only [fullLogReciprocalSum, broadPrimeBand] using
      (Finset.sum_sdiff_eq_sub
        (f := fun p : ℕ =>
          Real.log (p : ℝ) / (p : ℝ)) hsub).symm
  simp only [broadBandLogMoment, hsum]

theorem broadBandShiftedLogMoment_eq_sum {T : ℕ} {a : ℝ}
    (hTY : T ≤ expEndpoint a T) :
    broadBandShiftedLogMoment T a =
      (∑ p ∈ broadPrimeBand T a,
        Real.log (p : ℝ) / ((p : ℝ) + 1)) /
          (T : ℝ) := by
  have hsub := primesUpTo_mono hTY
  have hsum :
      fullShiftedLogReciprocalSum (expEndpoint a T) -
          fullShiftedLogReciprocalSum T =
        ∑ p ∈ broadPrimeBand T a,
          Real.log (p : ℝ) / ((p : ℝ) + 1) := by
    simpa only [fullShiftedLogReciprocalSum,
      broadPrimeBand] using
      (Finset.sum_sdiff_eq_sub
        (f := fun p : ℕ =>
          Real.log (p : ℝ) / ((p : ℝ) + 1)) hsub).symm
  simp only [broadBandShiftedLogMoment, hsum]

private lemma log_reciprocal_sub_shifted_nonneg
    {p : ℕ} (hp : p.Prime) :
    0 ≤ Real.log (p : ℝ) / (p : ℝ) -
      Real.log (p : ℝ) / ((p : ℝ) + 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hlog : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hinv :
      1 / ((p : ℝ) + 1) ≤ 1 / (p : ℝ) :=
    one_div_le_one_div_of_le hpR (by linarith)
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact sub_nonneg.mpr
    (mul_le_mul_of_nonneg_left
      (by simpa only [div_eq_mul_inv, one_mul] using hinv) hlog)

private lemma reciprocal_sub_shifted_le_square
    {p : ℕ} (hp : p.Prime) :
    1 / (p : ℝ) - 1 / ((p : ℝ) + 1) ≤
      1 / (p : ℝ) ^ 2 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  field_simp [hpR.ne', hpR1.ne']
  nlinarith

private lemma log_reciprocal_sub_shifted_le
    {p Y : ℕ} (hp : p.Prime) (hpY : p ≤ Y) :
    Real.log (p : ℝ) / (p : ℝ) -
        Real.log (p : ℝ) / ((p : ℝ) + 1) ≤
      Real.log (Y : ℝ) * (1 / (p : ℝ) ^ 2) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hYR : (0 : ℝ) < Y := by
    exact_mod_cast hp.pos.trans_le hpY
  have hlogp : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hOneY : 1 ≤ Y := hp.one_le.trans hpY
  have hlogY : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hOneY)
  have hlog :
      Real.log (p : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hpR (by exact_mod_cast hpY)
  have hdelta :=
    reciprocal_sub_shifted_le_square hp
  have hdeltaNonneg :
      0 ≤ 1 / (p : ℝ) -
        1 / ((p : ℝ) + 1) := by
    have hpR1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le hpR (by linarith)
  calc
    Real.log (p : ℝ) / (p : ℝ) -
        Real.log (p : ℝ) / ((p : ℝ) + 1) =
      Real.log (p : ℝ) *
        (1 / (p : ℝ) -
          1 / ((p : ℝ) + 1)) := by ring
    _ ≤ Real.log (Y : ℝ) *
        (1 / (p : ℝ) ^ 2) :=
      mul_le_mul hlog hdelta hdeltaNonneg
        (by positivity)

private theorem broad_log_shift_difference_numerator_bounds
    (T Y : ℕ) (hT : 1 ≤ T) (hTY : T ≤ Y) :
    0 ≤
        (fullLogReciprocalSum Y -
          fullLogReciprocalSum T) -
        (fullShiftedLogReciprocalSum Y -
          fullShiftedLogReciprocalSum T) ∧
      (fullLogReciprocalSum Y -
          fullLogReciprocalSum T) -
        (fullShiftedLogReciprocalSum Y -
          fullShiftedLogReciprocalSum T) ≤
        Real.log (Y : ℝ) / (T : ℝ) := by
  have hsub := primesUpTo_mono hTY
  have hrec :
      fullLogReciprocalSum Y -
          fullLogReciprocalSum T =
        ∑ p ∈ primesUpTo Y \ primesUpTo T,
          Real.log (p : ℝ) / (p : ℝ) := by
    simpa only [fullLogReciprocalSum] using
      (Finset.sum_sdiff_eq_sub
        (f := fun p : ℕ =>
          Real.log (p : ℝ) / (p : ℝ)) hsub).symm
  have hshift :
      fullShiftedLogReciprocalSum Y -
          fullShiftedLogReciprocalSum T =
        ∑ p ∈ primesUpTo Y \ primesUpTo T,
          Real.log (p : ℝ) / ((p : ℝ) + 1) := by
    simpa only [fullShiftedLogReciprocalSum] using
      (Finset.sum_sdiff_eq_sub
        (f := fun p : ℕ =>
          Real.log (p : ℝ) / ((p : ℝ) + 1)) hsub).symm
  rw [hrec, hshift, ← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro p hpMem
    apply log_reciprocal_sub_shifted_nonneg
    have hpY' : p ≤ Y ∧ p.Prime := by
      simpa [primesUpTo] using
        (Finset.mem_sdiff.mp hpMem).1
    exact hpY'.2
  · calc
      (∑ p ∈ primesUpTo Y \ primesUpTo T,
          (Real.log (p : ℝ) / (p : ℝ) -
            Real.log (p : ℝ) / ((p : ℝ) + 1))) ≤
          ∑ p ∈ primesUpTo Y \ primesUpTo T,
            Real.log (Y : ℝ) *
              (1 / (p : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro p hpMem
        have hpY' : p ≤ Y ∧ p.Prime := by
          simpa [primesUpTo] using
            (Finset.mem_sdiff.mp hpMem).1
        exact log_reciprocal_sub_shifted_le
          hpY'.2 hpY'.1
      _ = Real.log (Y : ℝ) *
          reciprocalSquareSumBetween T Y := by
        rw [reciprocalSquareSumBetween,
          Finset.mul_sum]
      _ ≤ Real.log (Y : ℝ) * (1 / (T : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
          (reciprocalSquareSumBetween_le T Y hT)
        exact Real.log_natCast_nonneg Y
      _ = Real.log (Y : ℝ) / (T : ℝ) := by
        ring

private lemma broad_log_shift_upper_tendsto_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℕ =>
        Real.log (expEndpoint a T : ℝ) / (T : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hlog := expEndpoint_log_div_tendsto ha
  have hinv :
      Tendsto (fun T : ℕ => 1 / (T : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      tendsto_natCast_atTop_atTop
  have hmul := hlog.mul hinv
  have heq :
      (fun T : ℕ =>
        Real.log (expEndpoint a T : ℝ) / (T : ℝ) *
          (1 / (T : ℝ))) =ᶠ[atTop]
      (fun T : ℕ =>
        Real.log (expEndpoint a T : ℝ) / (T : ℝ) ^ 2) := by
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hTR : (T : ℝ) ≠ 0 := by
      exact_mod_cast hT.ne'
    field_simp [hTR]
  simpa only [mul_zero] using hmul.congr' heq

private theorem broadBandLogMoment_sub_shifted_tendsto_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℕ =>
        broadBandLogMoment T a -
          broadBandShiftedLogMoment T a)
      atTop (𝓝 0) := by
  have hupper := broad_log_shift_upper_tendsto_zero ha
  apply squeeze_zero'
  · filter_upwards [
      eventually_ge_atTop 1,
      eventually_nat_le_expEndpoint ha,
      eventually_gt_atTop 0] with T hT1 hTY hT
    have hbounds :=
      broad_log_shift_difference_numerator_bounds
        T (expEndpoint a T) hT1 hTY
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    dsimp [broadBandLogMoment,
      broadBandShiftedLogMoment]
    apply sub_nonneg.mpr
    apply (div_le_div_iff_of_pos_right hTR).2
    linarith [hbounds.1]
  · filter_upwards [
      eventually_ge_atTop 1,
      eventually_nat_le_expEndpoint ha,
      eventually_gt_atTop 0] with T hT1 hTY hT
    have hbounds :=
      broad_log_shift_difference_numerator_bounds
        T (expEndpoint a T) hT1 hTY
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    dsimp [broadBandLogMoment,
      broadBandShiftedLogMoment]
    calc
      (fullLogReciprocalSum (expEndpoint a T) -
            fullLogReciprocalSum T) / (T : ℝ) -
          (fullShiftedLogReciprocalSum (expEndpoint a T) -
            fullShiftedLogReciprocalSum T) / (T : ℝ) =
        ((fullLogReciprocalSum (expEndpoint a T) -
            fullLogReciprocalSum T) -
          (fullShiftedLogReciprocalSum (expEndpoint a T) -
            fullShiftedLogReciprocalSum T)) / (T : ℝ) := by
          ring
      _ ≤
          (Real.log (expEndpoint a T : ℝ) / (T : ℝ)) /
            (T : ℝ) :=
        div_le_div_of_nonneg_right hbounds.2 hTR.le
      _ =
          Real.log (expEndpoint a T : ℝ) / (T : ℝ) ^ 2 := by
        ring
  · exact hupper

/-- The probability denominator `p+1` has the same broad-band first
moment as `p`. -/
theorem broadBandShiftedLogMoment_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun T : ℕ => broadBandShiftedLogMoment T a)
      atTop (𝓝 a) := by
  have hdiff :=
    broadBandLogMoment_sub_shifted_tendsto_zero ha
  have hmain := broadBandLogMoment_tendsto ha
  have hsub := hmain.sub hdiff
  have heq :
      (fun T : ℕ =>
        broadBandLogMoment T a -
          (broadBandLogMoment T a -
            broadBandShiftedLogMoment T a)) =ᶠ[atTop]
      (fun T : ℕ => broadBandShiftedLogMoment T a) :=
    Eventually.of_forall (fun _ => by ring)
  simpa only [sub_zero] using hsub.congr' heq

/-- Deep-tail first moment: among broad-band primes with
`log p / T ≤ exp (-R)`, the shifted normalized logarithmic mass tends
to `exp (-R)`. -/
theorem deepTailShiftedLogMoment_tendsto (R : ℝ) :
    Tendsto
      (fun T : ℕ =>
        broadBandShiftedLogMoment T (depthCoordinate R))
      atTop (𝓝 (depthCoordinate R)) :=
  broadBandShiftedLogMoment_tendsto (depthCoordinate_pos R)

/-- Sum-facing form of the deep-tail moment. -/
theorem deepTailShiftedLogMoment_eq_sum {T : ℕ} (R : ℝ)
    (hT : T ≤ expEndpoint (depthCoordinate R) T) :
    broadBandShiftedLogMoment T (depthCoordinate R) =
      (∑ p ∈ broadPrimeBand T (depthCoordinate R),
        Real.log (p : ℝ) / ((p : ℝ) + 1)) /
          (T : ℝ) :=
  broadBandShiftedLogMoment_eq_sum hT

/-- Eventual epsilon-form of the deep-tail bound. -/
theorem eventually_deepTailShiftedLogMoment_le
    (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℕ in atTop,
      broadBandShiftedLogMoment T (depthCoordinate R) ≤
        depthCoordinate R + ε := by
  have hev :=
    (deepTailShiftedLogMoment_tendsto R).eventually
      (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  exact hev.mono (fun _ h => h.le)

/-! ## Compatibility of fixed cells with the growing band -/

theorem eventually_depthPrimeBand_subset_broad
    {r s : ℝ} (hr : 0 ≤ r) (_hrs : r ≤ s) :
    ∀ᶠ T : ℕ in atTop,
      depthPrimeBand T r s ⊆ broadPrimeBand T 1 := by
  have hlower :=
    eventually_nat_le_expEndpoint (depthCoordinate_pos s)
  have hupperCoord : depthCoordinate r ≤ 1 := by
    unfold depthCoordinate
    rw [Real.exp_le_one_iff]
    linarith
  filter_upwards [hlower] with T hT
  intro p hp
  have hp' := mem_depthPrimeBand.mp hp
  apply Finset.mem_sdiff.mpr
  constructor
  · have hpTop :
        p ≤ expEndpoint (1 : ℝ) T :=
      hp'.2.2.trans (expEndpoint_mono hupperCoord T)
    simp [primesUpTo, hp'.1, hpTop]
  · intro hpLow
    have hpLeT : p ≤ T := by
      simpa [primesUpTo, hp'.1] using hpLow
    omega

end Erdos536.PrimeBandTimeChange
