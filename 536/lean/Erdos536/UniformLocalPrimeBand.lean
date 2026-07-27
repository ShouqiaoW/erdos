import Erdos536.LocalPrimeBand

/-!
# Uniform shrinking prime-band lower bounds

The pointwise local-band limit is not sufficient for an adaptive anchor:
its center is revealed by the other coordinates and can vary across a
compact interval.  This file records a quantitative lower bound whose
scale threshold is uniform over every center in that interval.
-/

open Filter Topology Set

noncomputable section

namespace Erdos536.LocalPrimeBand

open Erdos536.PrimeSums

theorem localLowerEndpoint_log_lower
    (T : ℕ) (t : ℝ) :
    (T : ℝ) * t ≤
      Real.log (localLowerEndpoint T t : ℝ) := by
  have hApos :
      (0 : ℝ) < localLowerEndpoint T t := by
    exact_mod_cast localLowerEndpoint_pos T t
  rw [Real.le_log_iff_exp_le hApos]
  exact_mod_cast (Nat.le_ceil (Real.exp ((T : ℝ) * t)))

theorem localLowerEndpoint_log_upper
    (T : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.log (localLowerEndpoint T t : ℝ) <
      (T : ℝ) * t + 1 := by
  have hApos :
      (0 : ℝ) < localLowerEndpoint T t := by
    exact_mod_cast localLowerEndpoint_pos T t
  have hexpone : 1 ≤ Real.exp ((T : ℝ) * t) := by
    exact Real.one_le_exp (mul_nonneg (Nat.cast_nonneg T) ht)
  have hceil :
      (localLowerEndpoint T t : ℝ) <
        Real.exp ((T : ℝ) * t) + 1 := by
    exact_mod_cast
      (Nat.ceil_lt_add_one (Real.exp_nonneg ((T : ℝ) * t)))
  have htwo :
      (localLowerEndpoint T t : ℝ) <
        2 * Real.exp ((T : ℝ) * t) := by
    calc
      (localLowerEndpoint T t : ℝ) <
          Real.exp ((T : ℝ) * t) + 1 := hceil
      _ ≤ Real.exp ((T : ℝ) * t) +
          Real.exp ((T : ℝ) * t) := by linarith
      _ = 2 * Real.exp ((T : ℝ) * t) := by ring
  have hlog :=
    Real.log_lt_log hApos htwo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (Real.exp_ne_zero _), Real.log_exp] at hlog
  linarith [Real.log_two_lt_d9]

/-- Quantitative lower bound before choosing a uniform scale threshold.
The two error terms are respectively the harmonic quadrature error and
the replacement of `1/p` by `1/(p+1)`. -/
theorem localBandShiftedReciprocalMass_lower_quantitative
    {T X₀ : ℕ} {r₀ t r₁ h C : ℝ}
    (hT : 0 < T)
    (hr₀ : 0 < r₀) (hr₀t : r₀ ≤ t) (htr₁ : t ≤ r₁)
    (hh : 0 < h) (hC : 0 ≤ C)
    (hcut : X₀ ≤ localLowerEndpoint T t)
    (hTr₁ : 1 ≤ (T : ℝ) * r₁)
    (hhlog : h ≤ Real.log (localLowerEndpoint T t : ℝ))
    (hquad : ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3) :
    h / (4 * (T : ℝ) * r₁) -
          5 * C / ((T : ℝ) * r₀) ^ 3 -
          1 / (localLowerEndpoint T t : ℝ) ≤
      localBandShiftedReciprocalMass T t h := by
  let A := localLowerEndpoint T t
  let Y := localUpperEndpoint T t h
  have ht : 0 < t := hr₀.trans_le hr₀t
  have hr₁ : 0 < r₁ := ht.trans_le htr₁
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hAposN : 0 < A := localLowerEndpoint_pos T t
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAposN
  have hAY : A ≤ Y :=
    localLowerEndpoint_le_upper (T := T) (t := t) hh.le
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast hAposN.trans_le hAY
  have hloglower :
      (T : ℝ) * r₀ ≤ Real.log (A : ℝ) := by
    calc
      (T : ℝ) * r₀ ≤ (T : ℝ) * t :=
        mul_le_mul_of_nonneg_left hr₀t hTR.le
      _ ≤ Real.log (A : ℝ) :=
        localLowerEndpoint_log_lower T t
  have hlogApos : 0 < Real.log (A : ℝ) :=
    (mul_pos hTR hr₀).trans_le hloglower
  have hlogupper :
      Real.log (A : ℝ) ≤ 2 * (T : ℝ) * r₁ := by
    have hbase :=
      localLowerEndpoint_log_upper T ht.le
    dsimp [A] at hbase ⊢
    have htupper :
        (T : ℝ) * t ≤ (T : ℝ) * r₁ :=
      mul_le_mul_of_nonneg_left htr₁ hTR.le
    nlinarith
  have hlogYlower :
      h + Real.log (A : ℝ) ≤ Real.log (Y : ℝ) := by
    have hceil :
        Real.exp h * (A : ℝ) ≤ (Y : ℝ) := by
      exact_mod_cast
        (Nat.le_ceil
          (Real.exp h * (localLowerEndpoint T t : ℝ)))
    calc
      h + Real.log (A : ℝ) =
          Real.log (Real.exp h * (A : ℝ)) := by
        rw [Real.log_mul (Real.exp_ne_zero _) hApos.ne',
          Real.log_exp]
      _ ≤ Real.log (Y : ℝ) :=
        Real.log_le_log (mul_pos (Real.exp_pos h) hApos) hceil
  have hprofile :
      h / (2 * Real.log (A : ℝ)) ≤
        Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) := by
    let x := h / Real.log (A : ℝ)
    have hx0 : 0 ≤ x := div_nonneg hh.le hlogApos.le
    have hx1 : x ≤ 1 := by
      dsimp [x]
      exact (div_le_one hlogApos).2 hhlog
    have hxden : 0 < x + 2 := by linarith
    have hfrac : x / 2 ≤ 2 * x / (x + 2) := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hxden).2
      nlinarith [sq_nonneg x]
    have hlogone :
        2 * x / (x + 2) ≤ Real.log (1 + x) :=
      Real.le_log_one_add_of_nonneg hx0
    have hrewrite :
        Real.log (1 + x) =
          Real.log (h + Real.log (A : ℝ)) -
            Real.log (Real.log (A : ℝ)) := by
      have hsum : 0 < h + Real.log (A : ℝ) := by positivity
      rw [← Real.log_div hsum.ne' hlogApos.ne']
      congr 1
      dsimp [x]
      field_simp [hlogApos.ne']
      ring
    have houter :
        Real.log (h + Real.log (A : ℝ)) ≤
          Real.log (Real.log (Y : ℝ)) :=
      Real.log_le_log
        (add_pos hh hlogApos)
        hlogYlower
    calc
      h / (2 * Real.log (A : ℝ)) = x / 2 := by
        dsimp [x]
        ring
      _ ≤ 2 * x / (x + 2) := hfrac
      _ ≤ Real.log (1 + x) := hlogone
      _ = Real.log (h + Real.log (A : ℝ)) -
          Real.log (Real.log (A : ℝ)) := hrewrite
      _ ≤ Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) :=
        sub_le_sub_right houter _
  have hmain :
      h / (4 * (T : ℝ) * r₁) ≤
        Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) := by
    calc
      h / (4 * (T : ℝ) * r₁) ≤
          h / (2 * Real.log (A : ℝ)) := by
        apply div_le_div_of_nonneg_left hh.le
          (mul_pos (by norm_num) hlogApos)
        nlinarith
      _ ≤ _ := hprofile
  have hquadrature := hquad A Y hcut hAY
  have hmass :
      Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) -
          5 * C / Real.log (A : ℝ) ^ 3 ≤
        localBandReciprocalMass T t h := by
    dsimp [localBandReciprocalMass, A, Y]
    rw [abs_le] at hquadrature
    linarith
  have hshiftRaw :=
    reciprocal_interval_sub_shifted_abs_le A Y hAposN hAY
  have hshift :
      localBandReciprocalMass T t h - 1 / (A : ℝ) ≤
        localBandShiftedReciprocalMass T t h := by
    dsimp [localBandReciprocalMass,
      localBandShiftedReciprocalMass, A, Y]
    rw [abs_le] at hshiftRaw
    linarith
  have herror :
      5 * C / Real.log (A : ℝ) ^ 3 ≤
        5 * C / ((T : ℝ) * r₀) ^ 3 := by
    have hdenpos : 0 < (T : ℝ) * r₀ := mul_pos hTR hr₀
    gcongr
  calc
    h / (4 * (T : ℝ) * r₁) -
          5 * C / ((T : ℝ) * r₀) ^ 3 -
          1 / (A : ℝ) ≤
        (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ))) -
          5 * C / Real.log (A : ℝ) ^ 3 -
          1 / (A : ℝ) := by
      gcongr
    _ ≤ localBandReciprocalMass T t h - 1 / (A : ℝ) := by
      linarith
    _ ≤ localBandShiftedReciprocalMass T t h := hshift

/-- Uniform compact-center lower bound for adaptive anchors. -/
theorem eventually_uniform_normalizedLocalBand_lower
    {r₀ r₁ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hr₀r₁ : r₀ ≤ r₁)
    (hc₀ : 0 < c₀) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ t : ℝ, r₀ ≤ t → t ≤ r₁ →
      c₀ * (η / (T : ℝ)) / (8 * r₁) ≤
        localBandShiftedReciprocalMass T t (c₀ * η) := by
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  have hr₁ : 0 < r₁ := hr₀.trans_le hr₀r₁
  have hh : 0 < c₀ * η := mul_pos hc₀ hη
  have hfirst :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ) *
            (5 * C / (((T : ℝ) * r₀) ^ 3)))
        atTop (𝓝 0) := by
    have hpow :
        Tendsto (fun T : ℕ => (T : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        tendsto_natCast_atTop_atTop
    have hlim :
        Tendsto
          (fun T : ℕ => (5 * C / r₀ ^ 3) / (T : ℝ) ^ 2)
          atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hpow
    convert hlim using 1
    · funext T
      by_cases hT : T = 0
      · subst T
        simp
      · have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT
        field_simp [hTR, hr₀.ne']
  have hsecond :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ) * Real.exp (-((T : ℝ) * r₀)))
        atTop (𝓝 0) := by
    have hlim :=
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        1 r₀ hr₀).comp tendsto_natCast_atTop_atTop
    convert hlim using 1
    · funext T
      simp only [Function.comp_apply, Real.rpow_one]
      congr 2
      ring
  have herrlim :
      Tendsto
        (fun T : ℕ =>
          (T : ℝ) *
            (5 * C / (((T : ℝ) * r₀) ^ 3) +
              Real.exp (-((T : ℝ) * r₀))))
        atTop (𝓝 0) := by
    simpa only [mul_add, zero_add] using hfirst.add hsecond
  have herrEventually :
      ∀ᶠ T : ℕ in atTop,
        (T : ℝ) *
            (5 * C / (((T : ℝ) * r₀) ^ 3) +
              Real.exp (-((T : ℝ) * r₀))) <
          c₀ * η / (8 * r₁) := by
    exact herrlim.eventually
      (Iio_mem_nhds (by positivity :
        (0 : ℝ) < c₀ * η / (8 * r₁)))
  have hcutEventually :
      ∀ᶠ T : ℕ in atTop,
        X₀ ≤ localLowerEndpoint T r₀ := by
    exact (expEndpoint_tendsto_atTop hr₀).eventually
      (eventually_ge_atTop X₀)
  have hlarge :
      ∀ᶠ T : ℕ in atTop,
        0 < T ∧
        c₀ * η ≤ (T : ℝ) * r₀ ∧
        1 ≤ (T : ℝ) * r₁ := by
    filter_upwards [
      eventually_gt_atTop 0,
      (tendsto_natCast_atTop_atTop.const_mul_atTop hr₀).eventually
        (eventually_ge_atTop (c₀ * η)),
      (tendsto_natCast_atTop_atTop.const_mul_atTop hr₁).eventually
        (eventually_ge_atTop 1)] with T hT hhT hT₁
    simpa only [mul_comm] using ⟨hT, hhT, hT₁⟩
  filter_upwards [herrEventually, hcutEventually, hlarge] with
      T herr hcutT hlargeT
  intro t hr₀t htr₁
  have ht : 0 < t := hr₀.trans_le hr₀t
  have hcut :
      X₀ ≤ localLowerEndpoint T t := by
    exact hcutT.trans
      (expEndpoint_mono hr₀t T)
  have hloglower :=
    localLowerEndpoint_log_lower T t
  have hhlog :
      c₀ * η ≤
        Real.log (localLowerEndpoint T t : ℝ) := by
    calc
      c₀ * η ≤ (T : ℝ) * r₀ := hlargeT.2.1
      _ ≤ (T : ℝ) * t :=
        mul_le_mul_of_nonneg_left hr₀t (Nat.cast_nonneg T)
      _ ≤ _ := hloglower
  have hpoint :=
    localBandShiftedReciprocalMass_lower_quantitative
      hlargeT.1 hr₀ hr₀t htr₁ hh hC.le hcut
      hlargeT.2.2 hhlog hquad
  have hAexp :
      Real.exp ((T : ℝ) * r₀) ≤
        (localLowerEndpoint T t : ℝ) := by
    calc
      Real.exp ((T : ℝ) * r₀) ≤
          Real.exp ((T : ℝ) * t) := by
        rw [Real.exp_le_exp]
        exact mul_le_mul_of_nonneg_left hr₀t (Nat.cast_nonneg T)
      _ ≤ (localLowerEndpoint T t : ℝ) := by
        exact_mod_cast
          (Nat.le_ceil (Real.exp ((T : ℝ) * t)))
  have hAinv :
      1 / (localLowerEndpoint T t : ℝ) ≤
        Real.exp (-((T : ℝ) * r₀)) := by
    have hApos :
        (0 : ℝ) < localLowerEndpoint T t := by
      exact_mod_cast localLowerEndpoint_pos T t
    have hexppos := Real.exp_pos ((T : ℝ) * r₀)
    calc
      1 / (localLowerEndpoint T t : ℝ) ≤
          1 / Real.exp ((T : ℝ) * r₀) :=
        one_div_le_one_div_of_le hexppos hAexp
      _ = Real.exp (-((T : ℝ) * r₀)) := by
        rw [one_div, ← Real.exp_neg]
  have hTR : (0 : ℝ) < T := by exact_mod_cast hlargeT.1
  have herr' :
      5 * C / (((T : ℝ) * r₀) ^ 3) +
          1 / (localLowerEndpoint T t : ℝ) ≤
        c₀ * η / (8 * (T : ℝ) * r₁) := by
    have hraw :
        5 * C / (((T : ℝ) * r₀) ^ 3) +
            Real.exp (-((T : ℝ) * r₀)) <
          (c₀ * η / (8 * r₁)) / (T : ℝ) := by
      apply (lt_div_iff₀ hTR).2
      simpa only [mul_comm] using herr
    calc
      5 * C / (((T : ℝ) * r₀) ^ 3) +
            1 / (localLowerEndpoint T t : ℝ) ≤
          5 * C / (((T : ℝ) * r₀) ^ 3) +
            Real.exp (-((T : ℝ) * r₀)) :=
        add_le_add_right hAinv _
      _ ≤ c₀ * η / (8 * (T : ℝ) * r₁) := by
        rw [show
          c₀ * η / (8 * (T : ℝ) * r₁) =
            (c₀ * η / (8 * r₁)) / (T : ℝ) by ring]
        exact hraw.le
  calc
    c₀ * (η / (T : ℝ)) / (8 * r₁) =
        c₀ * η / (8 * (T : ℝ) * r₁) := by ring
    _ ≤ c₀ * η / (4 * (T : ℝ) * r₁) -
          5 * C / (((T : ℝ) * r₀) ^ 3) -
          1 / (localLowerEndpoint T t : ℝ) := by
      have hdouble :
          c₀ * η / (4 * (T : ℝ) * r₁) =
            2 * (c₀ * η / (8 * (T : ℝ) * r₁)) := by
        ring
      rw [hdouble]
      linarith
    _ ≤ localBandShiftedReciprocalMass T t (c₀ * η) :=
      hpoint

/-- Matching compact-center upper bound.  The harmless `+1` absorbs all
rounding and uniform quadrature errors; for fixed `η` this is still a
constant multiple of `η / T`. -/
theorem eventually_uniform_normalizedLocalBand_upper
    {r₀ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hc₀ : 0 < c₀) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ t : ℝ, r₀ ≤ t →
      localBandShiftedReciprocalMass T t (c₀ * η) ≤
        (Real.log (Real.exp (c₀ * η) + 1) + 1) /
          ((T : ℝ) * r₀) := by
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  have hh : 0 < c₀ * η := mul_pos hc₀ hη
  have hcutEventually :
      ∀ᶠ T : ℕ in atTop,
        X₀ ≤ localLowerEndpoint T r₀ :=
    (expEndpoint_tendsto_atTop hr₀).eventually
      (eventually_ge_atTop X₀)
  have hsquare :
      Tendsto (fun T : ℕ => ((T : ℝ) * r₀) ^ 2)
        atTop atTop := by
    have hlinear :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hr₀
    have hpow := (tendsto_pow_atTop
      (by norm_num : (2 : ℕ) ≠ 0)).comp hlinear
    simpa only [mul_comm] using hpow
  have herrorEventually :
      ∀ᶠ T : ℕ in atTop,
        5 * C ≤ ((T : ℝ) * r₀) ^ 2 :=
    hsquare.eventually (eventually_ge_atTop (5 * C))
  filter_upwards [
      hcutEventually, herrorEventually, eventually_gt_atTop 0] with
      T hcutT herrorT hT
  intro t hr₀t
  let A := localLowerEndpoint T t
  let Y := localUpperEndpoint T t (c₀ * η)
  have ht : 0 < t := hr₀.trans_le hr₀t
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hAposN : 0 < A := localLowerEndpoint_pos T t
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAposN
  have hAY : A ≤ Y :=
    localLowerEndpoint_le_upper
      (T := T) (t := t) hh.le
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast hAposN.trans_le hAY
  have hcut :
      X₀ ≤ A := by
    exact hcutT.trans (expEndpoint_mono hr₀t T)
  have hloglower :
      (T : ℝ) * r₀ ≤ Real.log (A : ℝ) := by
    calc
      (T : ℝ) * r₀ ≤ (T : ℝ) * t :=
        mul_le_mul_of_nonneg_left hr₀t hTR.le
      _ ≤ Real.log (A : ℝ) :=
        localLowerEndpoint_log_lower T t
  have hlogApos : 0 < Real.log (A : ℝ) :=
    (mul_pos hTR hr₀).trans_le hloglower
  have hYupper :
      (Y : ℝ) <
        (Real.exp (c₀ * η) + 1) * (A : ℝ) := by
    have hceil :
        (Y : ℝ) <
          Real.exp (c₀ * η) * (A : ℝ) + 1 := by
      exact_mod_cast
        (Nat.ceil_lt_add_one
          (mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg A)))
    have hAone : (1 : ℝ) ≤ A := by
      exact_mod_cast hAposN
    calc
      (Y : ℝ) <
          Real.exp (c₀ * η) * (A : ℝ) + 1 := hceil
      _ ≤ (Real.exp (c₀ * η) + 1) * (A : ℝ) := by
        nlinarith
  have hlogYupper :
      Real.log (Y : ℝ) - Real.log (A : ℝ) ≤
        Real.log (Real.exp (c₀ * η) + 1) := by
    have hfactor :
        0 < Real.exp (c₀ * η) + 1 := by positivity
    have hlog :=
      Real.log_lt_log hYpos hYupper
    rw [Real.log_mul hfactor.ne' hApos.ne'] at hlog
    linarith
  have hdepthMain :
      Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) ≤
        Real.log (Real.exp (c₀ * η) + 1) /
          ((T : ℝ) * r₀) := by
    have hlogYpos :
        0 < Real.log (Y : ℝ) := by
      exact hlogApos.trans_le
        (Real.log_le_log hApos (by exact_mod_cast hAY))
    have hbasic :=
      Real.log_le_sub_one_of_pos
        (div_pos hlogYpos hlogApos)
    have hratio :
        Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) ≤
          (Real.log (Y : ℝ) -
            Real.log (A : ℝ)) /
              Real.log (A : ℝ) := by
      rw [← Real.log_div hlogYpos.ne' hlogApos.ne']
      calc
        Real.log
            (Real.log (Y : ℝ) / Real.log (A : ℝ)) ≤
            Real.log (Y : ℝ) / Real.log (A : ℝ) - 1 :=
          hbasic
        _ = (Real.log (Y : ℝ) - Real.log (A : ℝ)) /
            Real.log (A : ℝ) := by
          field_simp [hlogApos.ne']
    have hfactorlog :
        0 ≤ Real.log (Real.exp (c₀ * η) + 1) := by
      exact Real.log_nonneg (by
        linarith [Real.exp_pos (c₀ * η)])
    calc
      Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) ≤
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) /
            Real.log (A : ℝ) := hratio
      _ ≤ Real.log (Real.exp (c₀ * η) + 1) /
            Real.log (A : ℝ) := by
        exact div_le_div_of_nonneg_right hlogYupper hlogApos.le
      _ ≤ Real.log (Real.exp (c₀ * η) + 1) /
            ((T : ℝ) * r₀) := by
        exact div_le_div_of_nonneg_left hfactorlog
          (mul_pos hTR hr₀) hloglower
  have hquadrature := hquad A Y hcut hAY
  have herror :
      5 * C / Real.log (A : ℝ) ^ 3 ≤
        1 / ((T : ℝ) * r₀) := by
    have hx : 0 < (T : ℝ) * r₀ := mul_pos hTR hr₀
    have hlogcube :
        ((T : ℝ) * r₀) ^ 3 ≤
          Real.log (A : ℝ) ^ 3 :=
      pow_le_pow_left₀ hx.le hloglower 3
    calc
      5 * C / Real.log (A : ℝ) ^ 3 ≤
          5 * C / (((T : ℝ) * r₀) ^ 3) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hC.le)
          (pow_pos hx 3) hlogcube
      _ ≤ 1 / ((T : ℝ) * r₀) := by
        apply (div_le_iff₀ (pow_pos hx 3)).2
        calc
          5 * C ≤ ((T : ℝ) * r₀) ^ 2 := herrorT
          _ = 1 / ((T : ℝ) * r₀) *
              ((T : ℝ) * r₀) ^ 3 := by
            field_simp [hx.ne']
  have hunshifted :
      localBandReciprocalMass T t (c₀ * η) ≤
        Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) +
          5 * C / Real.log (A : ℝ) ^ 3 := by
    dsimp [localBandReciprocalMass, A, Y]
    rw [abs_le] at hquadrature
    linarith
  have hshifted :
      localBandShiftedReciprocalMass T t (c₀ * η) ≤
        localBandReciprocalMass T t (c₀ * η) := by
    rw [localBandShiftedReciprocalMass_eq_sum hh.le,
      localBandReciprocalMass_eq_sum hh.le]
    apply Finset.sum_le_sum
    intro p hp
    have hpR : (0 : ℝ) < p := by
      exact_mod_cast (mem_localPrimeBand.mp hp).1.pos
    exact one_div_le_one_div_of_le hpR (by linarith)
  calc
    localBandShiftedReciprocalMass T t (c₀ * η) ≤
        localBandReciprocalMass T t (c₀ * η) := hshifted
    _ ≤ Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) +
        5 * C / Real.log (A : ℝ) ^ 3 := hunshifted
    _ ≤ Real.log (Real.exp (c₀ * η) + 1) /
          ((T : ℝ) * r₀) +
        1 / ((T : ℝ) * r₀) :=
      add_le_add hdepthMain herror
    _ = (Real.log (Real.exp (c₀ * η) + 1) + 1) /
          ((T : ℝ) * r₀) := by ring

end Erdos536.LocalPrimeBand
