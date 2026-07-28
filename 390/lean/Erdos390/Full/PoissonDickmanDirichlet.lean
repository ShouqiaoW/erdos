import Erdos390.Full.ConditionedPoissonLimit
import Erdos390.Full.FirstFailure

/-!
# A Dirichlet-form route for the Poisson--Dickman covariance kernel

This file isolates the deterministic part of the proposed kernel argument.
For a test function written as `f(t) = t * q(t)`, the covariance quadratic
form is exactly a symmetric Dirichlet energy.  The identity uses only the
Dickman averaging equation already proved in `ConditionedPoissonLimit`; it
does not use a conditional probability measure on the zero-probability
fibre.

The file also closes the sign of the Dirichlet kernel from the delay equation.
It formalizes the classical first-failure proof that the negative logarithmic
derivative of the Dickman function is strictly increasing on the required
range, turns this into the four-point log-concavity inequality, and hence
proves strict negativity of the covariance kernel in the open square.
-/

open Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.PoissonDickmanDirichlet

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit

/-! ## Dickman log-concavity from a first-failure argument -/

/-- The negative logarithmic derivative dictated by the Dickman delay
equation.  On the positive range it is `-rho' / rho`. -/
def dickmanLogSlope (u : ℝ) : ℝ :=
  rho (u - 1) / (u * rho u)

/-- The right-hand side in the differential recurrence for the logarithmic
slope.  On `(2,5)` this is literally `dickmanLogSlope'`.  Keeping it as a
continuous algebraic expression lets the compact first-failure argument
include the endpoint `u = 2` without assigning an endpoint derivative. -/
def slopeGrowth (u : ℝ) : ℝ :=
  dickmanLogSlope u *
    (dickmanLogSlope u - dickmanLogSlope (u - 1) - 1 / u)

lemma dickmanLogSlope_pos {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    0 < dickmanLogSlope u := by
  unfold dickmanLogSlope
  exact div_pos
    (rho_pos_on_zero_five (by linarith) (by linarith))
    (mul_pos (by linarith) (rho_pos_on_zero_five (by linarith) hu5))

/-- Exact differential recurrence for the Dickman logarithmic slope.  Thus
strict log-concavity is equivalent to proving that the final parenthesis is
positive.  This identity is an unconditional step toward the first-failure
argument; it does not assume monotonicity of the slope. -/
lemma hasDerivAt_dickmanLogSlope {u : ℝ} (hu2 : 2 < u) (hu5 : u < 5) :
    HasDerivAt dickmanLogSlope
      (dickmanLogSlope u *
        (dickmanLogSlope u - dickmanLogSlope (u - 1) - 1 / u)) u := by
  have hu1 : 1 < u := by linarith
  have hu6 : u ≤ 6 := by linarith
  have hum1 : 1 < u - 1 := by linarith
  have hum1_le6 : u - 1 ≤ 6 := by linarith
  have hshift : HasDerivAt (fun x : ℝ => x - 1) 1 u := by
    simpa using (hasDerivAt_id u).sub_const 1
  have hnum : HasDerivAt (fun x : ℝ => rho (x - 1))
      (-rho (u - 2) / (u - 1)) u := by
    have h := (hasDerivAt_rho hum1 hum1_le6).comp u hshift
    simp only [Function.comp_def] at h
    ring_nf at h ⊢
    exact h
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun x : ℝ => x * rho x)
      (rho u + u * (-rho (u - 1) / u)) u := by
    simpa [id] using (hasDerivAt_id u).mul (hasDerivAt_rho hu1 hu6)
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) hu5.le
  have hrum1 : 0 < rho (u - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hrum2 : 0 < rho (u - 2) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hum10 : u - 1 ≠ 0 := ne_of_gt (by linarith)
  have hden0 : u * rho u ≠ 0 := mul_ne_zero hu0 (ne_of_gt hru)
  have hraw := hnum.div hden hden0
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  field_simp [hu0, hum10, ne_of_gt hru, ne_of_gt hrum1, ne_of_gt hrum2]
  ring

lemma continuousOn_slopeGrowth_Icc :
    ContinuousOn slopeGrowth (Icc (2 : ℝ) (9 / 2 : ℝ)) := by
  unfold slopeGrowth dickmanLogSlope
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact (continuous_id.mul continuous_rho).continuousOn
    · intro x hx
      exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
        (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
          (by norm_num at hx ⊢; linarith [hx.2])))
  · apply ContinuousOn.sub
    · apply ContinuousOn.sub
      · apply ContinuousOn.div
        · exact (continuous_rho.comp
            (continuous_id.sub continuous_const)).continuousOn
        · exact (continuous_id.mul continuous_rho).continuousOn
        · intro x hx
          exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
            (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
              (by norm_num at hx ⊢; linarith [hx.2])))
      · apply ContinuousOn.div
        · exact (continuous_rho.comp
            ((continuous_id.sub continuous_const).sub continuous_const)).continuousOn
        · exact ((continuous_id.sub continuous_const).mul
            (continuous_rho.comp
              (continuous_id.sub continuous_const))).continuousOn
        · intro x hx
          exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
            (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
              (by norm_num at hx ⊢; linarith [hx.2])))
    · exact continuous_const.continuousOn.div continuous_id.continuousOn
        (fun x hx => ne_of_gt (by linarith [hx.1]))

/-- The unit piece of the delay integral.  This is the exact finite-interval
identity used below; in particular, no differentiation under an integral
sign is needed in the first-failure step. -/
lemma rho_delay_unitIntegral {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    (∫ t in (0 : ℝ)..1, rho (u - t - 1) / (u - t)) =
      rho (u - 1) - rho u := by
  let g : ℝ → ℝ := fun x => rho (x - 1) / x
  have hcont : ContinuousOn g (Icc (1 : ℝ) u) := by
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact continuous_id.continuousOn
    · intro x hx
      exact ne_of_gt (by linarith [hx.1])
  have hsub₁ : Icc (1 : ℝ) (u - 1) ⊆ Icc (1 : ℝ) u := by
    intro x hx
    exact ⟨hx.1, by linarith [hx.2]⟩
  have hsub₂ : Icc (u - 1) u ⊆ Icc (1 : ℝ) u := by
    intro x hx
    exact ⟨by linarith [hx.1, hu2], hx.2⟩
  have hg₁ : IntervalIntegrable g volume (1 : ℝ) (u - 1) := by
    have hc := hcont.mono hsub₁
    rw [← uIcc_of_le (by linarith [hu2])] at hc
    exact hc.intervalIntegrable
  have hg₂ : IntervalIntegrable g volume (u - 1) u := by
    have hc := hcont.mono hsub₂
    rw [← uIcc_of_le (by linarith)] at hc
    exact hc.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals hg₁ hg₂
  have hu := rho_integral_eq (x := u) (by linarith [hu2]) hu5
  have hum := rho_integral_eq (x := u - 1)
    (by linarith [hu2]) (by linarith [hu5])
  have hpiece : (∫ x in (u - 1)..u, g x) = rho (u - 1) - rho u := by
    dsimp [g] at hadd hu hum ⊢
    linarith
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) g u
  rw [hcomp]
  simpa [g, sub_sub] using hpiece

/-- The normalized unit average in the Dickman equation. -/
lemma rho_ratio_average {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    (∫ t in (0 : ℝ)..1, rho (u - t) / rho (u - 1)) =
      (u * rho u) / rho (u - 1) := by
  have havg := rho_average_eq (x := u) (by linarith) hu5
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) rho u
  have hshift :
      (∫ t in (0 : ℝ)..1, rho (u - t)) = u * rho u := by
    rw [hcomp]
    simpa using havg.symm
  rw [intervalIntegral.integral_div, hshift]

/-- Exact algebraic form of the first-failure step.  It replaces the
derivative of Tao's nested denominator by a unit-delay integral whose sign
is read directly from earlier values of the logarithmic slope. -/
lemma neg_slopeGrowth_div_sq_eq_integral {u : ℝ}
    (hu2 : 2 < u) (hu5 : u ≤ 5) :
    -slopeGrowth u / dickmanLogSlope u ^ 2 =
      ∫ t in (0 : ℝ)..1,
        (rho (u - t) / rho (u - 1)) *
          (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)) := by
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) hu5
  have hrum1 : 0 < rho (u - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hrum2 : 0 < rho (u - 2) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hum10 : u - 1 ≠ 0 := ne_of_gt (by linarith)
  let R : ℝ → ℝ := fun t => rho (u - t) / rho (u - 1)
  let D : ℝ → ℝ := fun t => rho (u - t - 1) / (u - t) / rho (u - 1)
  have hRcont : Continuous R := by
    dsimp [R]
    exact (continuous_rho.comp
      (continuous_const.sub continuous_id)).div_const _
  have hDcont : ContinuousOn D (Icc (0 : ℝ) 1) := by
    dsimp [D]
    apply ContinuousOn.div_const
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        ((continuous_const.sub continuous_id).sub continuous_const)).continuousOn
    · exact (continuous_const.sub continuous_id).continuousOn
    · intro t ht
      exact ne_of_gt (by linarith [ht.2, hu2])
  have hRint : IntervalIntegrable R volume (0 : ℝ) 1 :=
    hRcont.intervalIntegrable 0 1
  have hDint : IntervalIntegrable D volume (0 : ℝ) 1 := by
    rw [← uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hDcont
    exact hDcont.intervalIntegrable
  have hpoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      R t * (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)) =
        dickmanLogSlope (u - 1) * R t - D t := by
    have hut0 : u - t ≠ 0 := ne_of_gt (by linarith [ht.2, hu2])
    have hrut : 0 < rho (u - t) :=
      rho_pos_on_zero_five (by linarith [ht.2, hu2]) (by linarith [ht.1, hu5])
    dsimp [R, D]
    unfold dickmanLogSlope
    field_simp [hu0, hum10, hut0, ne_of_gt hru, ne_of_gt hrum1,
      ne_of_gt hrum2, ne_of_gt hrut]
  rw [show (∫ t in (0 : ℝ)..1,
      R t * (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t))) =
        ∫ t in (0 : ℝ)..1, dickmanLogSlope (u - 1) * R t - D t by
      apply intervalIntegral.integral_congr
      intro t ht
      exact hpoint t (by
        simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)]
  rw [intervalIntegral.integral_sub
    (hRint.const_mul (dickmanLogSlope (u - 1))) hDint]
  rw [intervalIntegral.integral_const_mul]
  change -slopeGrowth u / dickmanLogSlope u ^ 2 =
    dickmanLogSlope (u - 1) *
        (∫ t in (0 : ℝ)..1, rho (u - t) / rho (u - 1)) -
      ∫ t in (0 : ℝ)..1, rho (u - t - 1) / (u - t) / rho (u - 1)
  rw [rho_ratio_average hu2.le hu5]
  rw [intervalIntegral.integral_div,
    rho_delay_unitIntegral hu2.le hu5]
  unfold slopeGrowth dickmanLogSlope
  field_simp [hu0, hum10, ne_of_gt hru, ne_of_gt hrum1, ne_of_gt hrum2]
  ring

/-- The exact reciprocal-average identity used in the classical
first-failure proof of Dickman log-concavity. -/
lemma dickmanLogSlope_reciprocal_average {u : ℝ} (hu2 : 2 ≤ u) (hu5 : u ≤ 5) :
    dickmanLogSlope u =
      1 / (∫ t in (0 : ℝ)..1, rho (u - t) / rho (u - 1)) := by
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) hu5
  have hrum1 : 0 < rho (u - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  rw [rho_ratio_average hu2 hu5]
  unfold dickmanLogSlope
  field_simp [hu0, ne_of_gt hru, ne_of_gt hrum1]

lemma continuousOn_dickmanLogSlope_open :
    ContinuousOn dickmanLogSlope (Ioo (1 : ℝ) 5) := by
  unfold dickmanLogSlope
  apply ContinuousOn.div
  · exact (continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn
  · exact (continuous_id.mul continuous_rho).continuousOn
  · intro x hx
    exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1]) hx.2.le))

lemma continuousOn_dickmanLogSlope_one_to_nine_halves :
    ContinuousOn dickmanLogSlope (Icc (1 : ℝ) (9 / 2 : ℝ)) := by
  unfold dickmanLogSlope
  apply ContinuousOn.div
  · exact (continuous_rho.comp
      (continuous_id.sub continuous_const)).continuousOn
  · exact (continuous_id.mul continuous_rho).continuousOn
  · intro x hx
    exact mul_ne_zero (ne_of_gt (by linarith [hx.1]))
      (ne_of_gt (rho_pos_on_zero_five (by linarith [hx.1])
        (by norm_num at hx ⊢; linarith [hx.2])))

/-- On the first nonconstant Dickman interval the numerator of the slope is
still `1`, so the derivative has this simpler exact form. -/
lemma hasDerivAt_dickmanLogSlope_one_two {u : ℝ}
    (hu1 : 1 < u) (hu2 : u < 2) :
    HasDerivAt dickmanLogSlope
      (dickmanLogSlope u * (dickmanLogSlope u - 1 / u)) u := by
  have heq : (fun z : ℝ => rho (z - 1)) =ᶠ[nhds u] (fun _ => (1 : ℝ)) := by
    filter_upwards [Iio_mem_nhds hu2] with z hz
    have hz' : z < 2 := by simpa only [mem_Iio] using hz
    exact rho_eq_one_of_le_one (by linarith [hz'])
  have hnum : HasDerivAt (fun z : ℝ => rho (z - 1)) 0 u := by
    simpa using (hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq heq
  have hu0 : u ≠ 0 := ne_of_gt (by linarith)
  have hden : HasDerivAt (fun z : ℝ => z * rho z)
      (rho u + u * (-rho (u - 1) / u)) u := by
    simpa [id] using (hasDerivAt_id u).mul
      (hasDerivAt_rho hu1 (by linarith))
  have hru : 0 < rho u := rho_pos_on_zero_five (by linarith) (by linarith)
  have hrum1 : rho (u - 1) = 1 := rho_eq_one_of_le_one (by linarith)
  have hden0 : u * rho u ≠ 0 := mul_ne_zero hu0 (ne_of_gt hru)
  have hraw := hnum.div hden hden0
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  rw [hrum1]
  field_simp [hu0, ne_of_gt hru]
  ring

lemma rho_two_eq_one_sub_log_two : rho 2 = 1 - Real.log 2 := by
  have h := rho_integral_eq (x := (2 : ℝ)) (by norm_num) (by norm_num)
  have hint : (∫ t in (1 : ℝ)..2, rho (t - 1) / t) = Real.log 2 := by
    calc
      (∫ t in (1 : ℝ)..2, rho (t - 1) / t) =
          ∫ t in (1 : ℝ)..2, 1 / t := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htmem : t ∈ Icc (1 : ℝ) 2 := by
          simpa [uIcc_of_le (show (1 : ℝ) ≤ 2 by norm_num)] using ht
        change rho (t - 1) / t = 1 / t
        rw [rho_eq_one_of_le_one (by linarith [htmem.2])]
      _ = Real.log 2 := by
        rw [integral_one_div_of_pos (by norm_num) (by norm_num)]
        simp
  linarith

/-- The logarithmic slope is already strictly increasing on `[1,2]`. -/
lemma strictMonoOn_dickmanLogSlope_one_two :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) 2) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (1 : ℝ) 2)
    (continuousOn_dickmanLogSlope_one_to_nine_halves.mono (by
      intro x hx
      exact ⟨hx.1, by norm_num at hx ⊢; linarith [hx.2]⟩))
  intro x hx
  rw [interior_Icc] at hx
  have hderiv := hasDerivAt_dickmanLogSlope_one_two hx.1 hx.2
  rw [hderiv.deriv]
  have hrho : 0 < rho x :=
    rho_pos_on_zero_five (by linarith [hx.1]) (by linarith [hx.2])
  have hrho_lt : rho x < 1 := by
    have hanti := strictAntiOn_rhoGlobal_Ici_one
      (show (1 : ℝ) ∈ Ici 1 by simp)
      (show x ∈ Ici 1 by simpa using hx.1.le) hx.1
    rw [rhoGlobal_eq_one_of_le_one le_rfl,
      rhoGlobal_eq_rho (by linarith [hx.2])] at hanti
    exact hanti
  have hxpos : 0 < x := by linarith [hx.1]
  have hdenpos : 0 < x * rho x := mul_pos hxpos hrho
  have hdenlt : x * rho x < x := by nlinarith
  have hslope_gt : 1 / x < dickmanLogSlope x := by
    unfold dickmanLogSlope
    rw [rho_eq_one_of_le_one (by linarith [hx.2])]
    exact one_div_lt_one_div_of_lt hdenpos hdenlt
  have hslope_pos : 0 < dickmanLogSlope x := by
    unfold dickmanLogSlope
    rw [rho_eq_one_of_le_one (by linarith [hx.2])]
    exact div_pos zero_lt_one (mul_pos hxpos hrho)
  exact mul_pos hslope_pos (sub_pos.mpr hslope_gt)

lemma slopeGrowth_two_pos : 0 < slopeGrowth 2 := by
  have hrho2 : 0 < rho 2 := rho_pos_on_zero_five (by norm_num) (by norm_num)
  have hrho2lt : rho 2 < 1 / 3 := by
    rw [rho_two_eq_one_sub_log_two]
    have hlog := Real.log_two_gt_d9
    norm_num at hlog ⊢
    nlinarith [hlog]
  unfold slopeGrowth dickmanLogSlope
  norm_num [rho_one, rho_zero]
  field_simp [ne_of_gt hrho2]
  nlinarith

/-- Positive recurrence growth after `2` propagates strict monotonicity of
the logarithmic slope from the explicit base interval `[1,2]`. -/
lemma strictMonoOn_dickmanLogSlope_of_growth_pos {x : ℝ}
    (hx2 : 2 ≤ x) (hx9 : x ≤ 9 / 2)
    (hgrowth : ∀ z ∈ Ioo (2 : ℝ) x, 0 < slopeGrowth z) :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) x) := by
  have hupper : StrictMonoOn dickmanLogSlope (Icc (2 : ℝ) x) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (2 : ℝ) x)
    · exact continuousOn_dickmanLogSlope_one_to_nine_halves.mono (by
        intro z hz
        exact ⟨by linarith [hz.1], by linarith [hz.2, hx9]⟩)
    · intro z hz
      rw [interior_Icc] at hz
      have hderiv := hasDerivAt_dickmanLogSlope hz.1
        (by norm_num at hx9 ⊢; linarith [hz.2, hx9])
      rw [hderiv.deriv]
      exact hgrowth z hz
  intro a ha b hb hab
  by_cases hb2 : b ≤ 2
  · exact strictMonoOn_dickmanLogSlope_one_two
      ⟨ha.1, hab.le.trans hb2⟩ ⟨by linarith [ha.1], hb2⟩ hab
  by_cases ha2 : 2 ≤ a
  · exact hupper ⟨ha2, ha.2⟩ ⟨by linarith [hb2], hb.2⟩ hab
  · have hleft := strictMonoOn_dickmanLogSlope_one_two
      (show a ∈ Icc (1 : ℝ) 2 from ⟨ha.1, le_of_not_ge ha2⟩)
      (show (2 : ℝ) ∈ Icc (1 : ℝ) 2 by norm_num)
      (lt_of_not_ge ha2)
    have hright := hupper
      (show (2 : ℝ) ∈ Icc 2 x from ⟨le_rfl, hx2⟩)
      (show b ∈ Icc 2 x from ⟨le_of_not_ge hb2, hb.2⟩)
      (lt_of_not_ge hb2)
    exact hleft.trans hright

/-- Strict positivity of the Dickman log-slope growth on the whole range
needed by the covariance kernel.  The proof uses the compact first-failure
principle and the exact algebraic integral identity above. -/
theorem slopeGrowth_pos_on_two_nine_halves :
    ∀ u ∈ Icc (2 : ℝ) (9 / 2 : ℝ), 0 < slopeGrowth u := by
  apply FirstFailure.positiveOn_Icc_of_positive_at_first_failure
    slopeGrowth continuousOn_slopeGrowth_Icc
  intro u hu hprev
  rcases hu.1.eq_or_lt with rfl | hu2
  · exact slopeGrowth_two_pos
  · have hmono : StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) u) :=
      strictMonoOn_dickmanLogSlope_of_growth_pos hu.1 hu.2 (by
        intro z hz
        exact hprev z ⟨hz.1.le, hz.2.le⟩ hz.2)
    let H : ℝ → ℝ := fun t =>
      -((rho (u - t) / rho (u - 1)) *
        (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t)))
    have hRcont : Continuous (fun t : ℝ => rho (u - t) / rho (u - 1)) :=
      (continuous_rho.comp
        (continuous_const.sub continuous_id)).div_const _
    have hfcomp : ContinuousOn (fun t : ℝ => dickmanLogSlope (u - t))
        (Icc (0 : ℝ) 1) := by
      apply continuousOn_dickmanLogSlope_open.comp
        (continuous_const.sub continuous_id).continuousOn
      intro t ht
      change 1 < u - t ∧ u - t < 5
      exact ⟨by linarith [hu2, ht.2], by
        norm_num at hu ⊢
        linarith [hu.2, ht.1]⟩
    have hHcont : ContinuousOn H (Icc (0 : ℝ) 1) := by
      dsimp [H]
      exact (hRcont.continuousOn.mul
        (continuous_const.continuousOn.sub hfcomp)).neg
    have hHnonneg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ H t := by
      have hratio : 0 < rho (u - t) / rho (u - 1) :=
        div_pos
          (rho_pos_on_zero_five (by linarith [hu2, ht.2])
            (by norm_num at hu ⊢; linarith [hu.2, ht.1]))
          (rho_pos_on_zero_five (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
      have hslope : dickmanLogSlope (u - 1) ≤ dickmanLogSlope (u - t) :=
        hmono.monotoneOn
          ⟨by linarith [hu2], by linarith⟩
          ⟨by linarith [hu2, ht.2], by linarith [ht.1]⟩
          (by linarith [ht.2])
      dsimp [H]
      exact neg_nonneg.mpr
        (mul_nonpos_of_nonneg_of_nonpos hratio.le (sub_nonpos.mpr hslope))
    have hHhalf : 0 < H (1 / 2 : ℝ) := by
      have hratio : 0 < rho (u - (1 / 2 : ℝ)) / rho (u - 1) :=
        div_pos
          (rho_pos_on_zero_five (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
          (rho_pos_on_zero_five (by linarith [hu2])
            (by norm_num at hu ⊢; linarith [hu.2]))
      have hslope : dickmanLogSlope (u - 1) <
          dickmanLogSlope (u - (1 / 2 : ℝ)) :=
        hmono
          ⟨by linarith [hu2], by linarith⟩
          ⟨by linarith [hu2], by linarith⟩
          (by norm_num)
      dsimp [H]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hratio (sub_neg.mpr hslope))
    have hHIntegral : 0 < ∫ t in (0 : ℝ)..1, H t := by
      apply intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
        hHcont
      · intro t ht
        exact hHnonneg t ⟨ht.1.le, ht.2⟩
      · exact ⟨(1 / 2 : ℝ), by norm_num, hHhalf⟩
    have hintegralNeg :
        (∫ t in (0 : ℝ)..1,
          (rho (u - t) / rho (u - 1)) *
            (dickmanLogSlope (u - 1) - dickmanLogSlope (u - t))) < 0 := by
      dsimp [H] at hHIntegral
      rw [intervalIntegral.integral_neg] at hHIntegral
      linarith
    have hid := neg_slopeGrowth_div_sq_eq_integral hu2
      (by norm_num at hu ⊢; linarith [hu.2])
    have hquot : -slopeGrowth u / dickmanLogSlope u ^ 2 < 0 := by
      rw [hid]
      exact hintegralNeg
    have hslopePos : 0 < dickmanLogSlope u :=
      dickmanLogSlope_pos hu2.le (by norm_num at hu ⊢; linarith [hu.2])
    have hden : 0 < dickmanLogSlope u ^ 2 := sq_pos_of_pos hslopePos
    have hnum : -slopeGrowth u < 0 := by
      rcases (div_neg_iff.mp hquot) with hbad | hgood
      · exact False.elim ((not_lt_of_ge hden.le) hbad.2)
      · exact hgood.1
    linarith

theorem strictMonoOn_dickmanLogSlope_one_nine_halves :
    StrictMonoOn dickmanLogSlope (Icc (1 : ℝ) (9 / 2 : ℝ)) := by
  apply strictMonoOn_dickmanLogSlope_of_growth_pos (by norm_num) le_rfl
  intro z hz
  exact slopeGrowth_pos_on_two_nine_halves z ⟨hz.1.le, hz.2.le⟩

lemma hasDerivAt_log_rho_eq_neg_slope {x : ℝ} (hx1 : 1 < x) (hx5 : x < 5) :
    HasDerivAt (fun z : ℝ => Real.log (rho z)) (-dickmanLogSlope x) x := by
  have hrho : 0 < rho x :=
    rho_pos_on_zero_five (by linarith) hx5.le
  have hraw := (hasDerivAt_rho hx1 (by linarith)).log (ne_of_gt hrho)
  apply hraw.congr_deriv
  unfold dickmanLogSlope
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  field_simp [hx0, ne_of_gt hrho]

/-- Fundamental-theorem form of the logarithmic derivative, on the entire
range used by the one- and two-point Dickman translates. -/
lemma log_rho_sub_eq_neg_slopeIntegral {a b : ℝ}
    (ha : 1 < a) (hab : a ≤ b) (hb : b < 5) :
    Real.log (rho b) - Real.log (rho a) =
      -(∫ x in a..b, dickmanLogSlope x) := by
  have hcontLog : ContinuousOn (fun x : ℝ => Real.log (rho x)) (Icc a b) := by
    apply ContinuousOn.log continuous_rho.continuousOn
    intro x hx
    exact ne_of_gt (rho_pos_on_zero_five
      (by linarith [ha, hx.1]) (by linarith [hb, hx.2]))
  have hcontSlope : ContinuousOn (fun x : ℝ => -dickmanLogSlope x)
      (Icc a b) :=
    (continuousOn_dickmanLogSlope_open.mono (by
      intro x hx
      exact ⟨by linarith [ha, hx.1], by linarith [hb, hx.2]⟩)).neg
  have hFTC :
      (∫ x in a..b, -dickmanLogSlope x) =
        Real.log (rho b) - Real.log (rho a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcontLog
    · intro x hx
      exact hasDerivAt_log_rho_eq_neg_slope
        (by linarith [ha, hx.1]) (by linarith [hb, hx.2])
    · exact hcontSlope.intervalIntegrable_of_Icc hab
  rw [intervalIntegral.integral_neg] at hFTC
  linarith

private lemma slopeIntegral_shift_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) ≤
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t ≤ U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hmono : ∀ x ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x hx
    · exact hxsmem x hx
    · linarith [hs.1]
  have hint := intervalIntegral.integral_mono_on (μ := volume) hab
    (hcont₁.intervalIntegrable_of_Icc hab)
    (hcont₂.intervalIntegrable_of_Icc hab) hmono
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  ring

private lemma slopeIntegral_shift_lt {s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    (∫ x in (U - s - t)..(U - s), dickmanLogSlope x) <
      ∫ x in (U - t)..U, dickmanLogSlope x := by
  have hab : U - s - t < U - s := by linarith [ht.1]
  have hxmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.1, hx.2]
  have hxsmem (x : ℝ) (hx : x ∈ Icc (U - s - t) (U - s)) :
      x + s ∈ Icc (1 : ℝ) (9 / 2 : ℝ) := by
    constructor
    · norm_num [U] at hs ht hx ⊢
      linarith [ht.2, hx.1]
    · norm_num [U] at hs ht hx ⊢
      linarith [hs.2, hx.2]
  have hcont₁ : ContinuousOn dickmanLogSlope (Icc (U - s - t) (U - s)) :=
    continuousOn_dickmanLogSlope_one_to_nine_halves.mono hxmem
  have hcont₂ : ContinuousOn (fun x : ℝ => dickmanLogSlope (x + s))
      (Icc (U - s - t) (U - s)) := by
    apply continuousOn_dickmanLogSlope_one_to_nine_halves.comp
      (continuous_id.add continuous_const).continuousOn
    exact hxsmem
  have hle : ∀ x ∈ Ioc (U - s - t) (U - s),
      dickmanLogSlope x ≤ dickmanLogSlope (x + s) := by
    intro x hx
    apply strictMonoOn_dickmanLogSlope_one_nine_halves.monotoneOn
    · exact hxmem x ⟨hx.1.le, hx.2⟩
    · exact hxsmem x ⟨hx.1.le, hx.2⟩
    · linarith [hs.1]
  have hexists : ∃ c ∈ Icc (U - s - t) (U - s),
      dickmanLogSlope c < dickmanLogSlope (c + s) := by
    refine ⟨U - s - t, left_mem_Icc.mpr hab.le, ?_⟩
    apply strictMonoOn_dickmanLogSlope_one_nine_halves
    · exact hxmem _ (left_mem_Icc.mpr hab.le)
    · exact hxsmem _ (left_mem_Icc.mpr hab.le)
    · linarith [hs.1]
  have hint := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    hab hcont₁ hcont₂ hle hexists
  rw [intervalIntegral.integral_comp_add_right] at hint
  convert hint using 1
  ring

lemma log_rho_four_point_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) ≤
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := slopeIntegral_shift_le hs ht
  linarith

lemma log_rho_four_point_lt {s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Real.log (rho (U - s - t)) + Real.log (rho U) <
      Real.log (rho (U - s)) + Real.log (rho (U - t)) := by
  have h₁ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - s - t) (b := U - s)
    (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
    (by linarith [ht.1])
    (by norm_num [U] at hs ⊢; linarith [hs.1])
  have h₂ := log_rho_sub_eq_neg_slopeIntegral
    (a := U - t) (b := U)
    (by norm_num [U] at ht ⊢; linarith [ht.2])
    (by linarith [ht.1]) (by norm_num [U])
  have hint := slopeIntegral_shift_lt hs ht
  linarith

lemma rho_four_point_le {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    rho (U - s - t) * rho U ≤ rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := rho_U_pos
  have hc : 0 < rho (U - s) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_le_exp.mpr (log_rho_four_point_le hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h

lemma rho_four_point_lt {s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    rho (U - s - t) * rho U < rho (U - s) * rho (U - t) := by
  have ha : 0 < rho (U - s - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ht ⊢; linarith [hs.2, ht.2])
      (by norm_num [U] at hs ht ⊢; linarith [hs.1, ht.1])
  have hb : 0 < rho U := rho_U_pos
  have hc : 0 < rho (U - s) :=
    rho_pos_on_zero_five
      (by norm_num [U] at hs ⊢; linarith [hs.2])
      (by norm_num [U] at hs ⊢; linarith [hs.1])
  have hd : 0 < rho (U - t) :=
    rho_pos_on_zero_five
      (by norm_num [U] at ht ⊢; linarith [ht.2])
      (by norm_num [U] at ht ⊢; linarith [ht.1])
  have h := Real.exp_lt_exp.mpr (log_rho_four_point_lt hs ht)
  rw [Real.exp_add, Real.exp_add, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hc, Real.exp_log hd] at h
  exact h

/-- The covariance defect is nonpositive on the closed physical square.
This is now an unconditional theorem, obtained from the proved Dickman
log-concavity rather than supplied as an analytic premise. -/
theorem covarianceKernel_nonpos {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernel s t ≤ 0 := by
  have hprod := rho_four_point_le hs ht
  have hU : 0 < rho U := rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_le_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_nonpos.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ ≤ (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]

/-- The defect is strictly negative when both marked sizes are interior. -/
theorem covarianceKernel_neg {s t : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    covarianceKernel s t < 0 := by
  have hprod := rho_four_point_lt hs ht
  have hU : 0 < rho U := rho_U_pos
  have hden : 0 < rho U * rho U := mul_pos hU hU
  have hscaled := (div_lt_div_iff_of_pos_right hden).2 hprod
  unfold covarianceKernel F
  apply sub_neg.mpr
  calc
    rho (U - (s + t)) / rho U =
        (rho (U - s - t) * rho U) / (rho U * rho U) := by
      rw [show U - (s + t) = U - s - t by ring]
      field_simp [ne_of_gt hU]
    _ < (rho (U - s) * rho (U - t)) / (rho U * rho U) := hscaled
    _ = rho (U - s) / rho U * (rho (U - t) / rho U) := by
      field_simp [ne_of_gt hU]

/-- On every compact square strictly inside the physical square, strict
kernel negativity has a quantitative uniform margin. -/
theorem exists_truncated_covarianceKernel_gap {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ s ∈ Icc epsilon (1 - epsilon),
        ∀ t ∈ Icc epsilon (1 - epsilon),
          kappa ≤ -covarianceKernel s t := by
  let S : Set (ℝ × ℝ) :=
    Icc epsilon (1 - epsilon) ×ˢ Icc epsilon (1 - epsilon)
  have hnonempty : S.Nonempty := by
    refine ⟨(epsilon, epsilon), ?_⟩
    exact ⟨⟨le_rfl, by linarith⟩, ⟨le_rfl, by linarith⟩⟩
  have hcompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn
      (fun z : ℝ × ℝ => -covarianceKernel z.1 z.2) S :=
    ConditionedPoissonLimit.continuous_covarianceKernel.neg.continuousOn
  obtain ⟨z, hzS, hzmin⟩ := hcompact.exists_isMinOn hnonempty hcont
  let kappa : ℝ := -covarianceKernel z.1 z.2
  have hzopen₁ : z.1 ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hepsilon.trans_le hzS.1.1, by linarith [hzS.1.2, hepsilon]⟩
  have hzopen₂ : z.2 ∈ Ioo (0 : ℝ) 1 := by
    exact ⟨hepsilon.trans_le hzS.2.1, by linarith [hzS.2.2, hepsilon]⟩
  have hkappa : 0 < kappa := by
    dsimp only [kappa]
    exact neg_pos.mpr (covarianceKernel_neg hzopen₁ hzopen₂)
  refine ⟨kappa, hkappa, ?_⟩
  intro s hs t ht
  change -covarianceKernel z.1 z.2 ≤ -covarianceKernel s t
  exact hzmin (show (s, t) ∈ S from ⟨hs, ht⟩)

/-- Ratio form of the logarithmic-slope integral.  This is the nontrivial
calculus identity behind the exponential denominator in the first-failure
argument. -/
lemma rho_ratio_eq_exp_neg_slopeIntegral {u t : ℝ}
    (hu2 : 2 < u) (hu5 : u < 5) (ht : t ∈ Icc (0 : ℝ) 1) :
    rho (u - t) / rho (u - 1) =
      Real.exp (-∫ s in t..1, dickmanLogSlope (u - s)) := by
  have hab : u - 1 ≤ u - t := by linarith [ht.2]
  have hsegment : Icc (u - 1) (u - t) ⊆ Ioo (1 : ℝ) 5 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2, hu2, hu5, ht.1]
  have hcontLog : ContinuousOn (fun x : ℝ => Real.log (rho x))
      (Icc (u - 1) (u - t)) := by
    apply ContinuousOn.log continuous_rho.continuousOn
    intro x hx
    exact ne_of_gt (rho_pos_on_zero_five
      (by have := hsegment hx; linarith [this.1])
      (by have := hsegment hx; linarith [this.2]))
  have hcontSlope : ContinuousOn (fun x : ℝ => -dickmanLogSlope x)
      (Icc (u - 1) (u - t)) :=
    (continuousOn_dickmanLogSlope_open.mono hsegment).neg
  have hFTC :
      (∫ x in (u - 1)..(u - t), -dickmanLogSlope x) =
        Real.log (rho (u - t)) - Real.log (rho (u - 1)) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcontLog
    · intro x hx
      exact hasDerivAt_log_rho_eq_neg_slope
        (by have := hsegment ⟨hx.1.le, hx.2.le⟩; exact this.1)
        (by have := hsegment ⟨hx.1.le, hx.2.le⟩; exact this.2)
    · exact hcontSlope.intervalIntegrable_of_Icc hab
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := t) (b := (1 : ℝ)) dickmanLogSlope u
  have hlog :
      Real.log (rho (u - t)) - Real.log (rho (u - 1)) =
        -∫ s in t..1, dickmanLogSlope (u - s) := by
    rw [intervalIntegral.integral_neg] at hFTC
    rw [hcomp]
    linarith
  have hposTop : 0 < rho (u - t) :=
    rho_pos_on_zero_five (by linarith [hu2, ht.2]) (by linarith [hu5, ht.1])
  have hposBot : 0 < rho (u - 1) :=
    rho_pos_on_zero_five (by linarith [hu2]) (by linarith [hu5])
  calc
    rho (u - t) / rho (u - 1) =
        Real.exp (Real.log (rho (u - t)) - Real.log (rho (u - 1))) := by
      rw [Real.exp_sub, Real.exp_log hposTop, Real.exp_log hposBot]
    _ = Real.exp (-∫ s in t..1, dickmanLogSlope (u - s)) := by
      rw [hlog]

/-- The exact nested-integral identity used by Tao/Hildebrand's
first-failure proof.  What remains for strict log-concavity is to formalize
the differentiation of this denominator and the first-failure argument. -/
lemma dickmanLogSlope_nestedIntegral {u : ℝ} (hu2 : 2 < u) (hu5 : u < 5) :
    dickmanLogSlope u =
      1 / (∫ t in (0 : ℝ)..1,
        Real.exp (-∫ s in t..1, dickmanLogSlope (u - s))) := by
  rw [dickmanLogSlope_reciprocal_average hu2.le hu5.le]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := by
    simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  exact rho_ratio_eq_exp_neg_slopeIntegral hu2 hu5 htIcc

/-- The covariance quadratic form after writing the original test function as
`f(t) = t * q(t)`. -/
def conjugatedQuadratic (q : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, F t * t * q t ^ 2) +
    ∫ s in (0 : ℝ)..1,
      ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s * q t

/-- The symmetric energy associated with the negative covariance kernel. -/
def dirichletEnergy (q : ℝ → ℝ) : ℝ :=
  -(1 / 2 : ℝ) *
    ∫ s in (0 : ℝ)..1,
      ∫ t in (0 : ℝ)..1,
        covarianceKernel s t * (q s - q t) ^ 2

/-- The manifestly nonnegative version of the energy integrand, once the
kernel is known to be nonpositive. -/
def positiveDirichletIntegral (q : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    ∫ t in (0 : ℝ)..1,
      -covarianceKernel s t * (q s - q t) ^ 2

private def positiveDirichletInner (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    -covarianceKernel s t * (q s - q t) ^ 2

private def leftDiagonal (q : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s ^ 2

private def rightDiagonal (q : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    ∫ t in (0 : ℝ)..1, covarianceKernel s t * q t ^ 2

private def crossTerm (q : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s * q t

private def differenceSquareTerm (q : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1,
    ∫ t in (0 : ℝ)..1, covarianceKernel s t * (q s - q t) ^ 2

private lemma continuous_F_global : Continuous F := by
  exact ConditionedPoissonLimit.continuous_F

private lemma continuous_uncurry_kernel :
    Continuous (Function.uncurry covarianceKernel) := by
  exact ConditionedPoissonLimit.continuous_covarianceKernel

private lemma continuous_uncurry_kernel_mul_left_sq (q : ℝ → ℝ)
    (hq : Continuous q) :
    Continuous (Function.uncurry
      (fun s t : ℝ => covarianceKernel s t * q s ^ 2)) := by
  exact continuous_uncurry_kernel.mul
    ((hq.comp continuous_fst).pow 2)

private lemma continuous_uncurry_kernel_mul_right_sq (q : ℝ → ℝ)
    (hq : Continuous q) :
    Continuous (Function.uncurry
      (fun s t : ℝ => covarianceKernel s t * q t ^ 2)) := by
  exact continuous_uncurry_kernel.mul
    ((hq.comp continuous_snd).pow 2)

private lemma continuous_uncurry_kernel_mul_cross (q : ℝ → ℝ)
    (hq : Continuous q) :
    Continuous (Function.uncurry
      (fun s t : ℝ => covarianceKernel s t * q s * q t)) := by
  exact (continuous_uncurry_kernel.mul (hq.comp continuous_fst)).mul
    (hq.comp continuous_snd)

private lemma continuous_uncurry_positiveDirichletIntegrand
    (q : ℝ → ℝ) (hq : Continuous q) :
    Continuous (Function.uncurry (fun s t : ℝ =>
      -covarianceKernel s t * (q s - q t) ^ 2)) := by
  exact continuous_uncurry_kernel.neg.mul
    (((hq.comp continuous_fst).sub (hq.comp continuous_snd)).pow 2)

private lemma continuous_positiveDirichletInner (q : ℝ → ℝ)
    (hq : Continuous q) : Continuous (positiveDirichletInner q) := by
  unfold positiveDirichletInner
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := (0 : ℝ)) (b₀ := 1)
  exact continuous_uncurry_positiveDirichletIntegrand q hq

private lemma integrableOn_unitSquare_of_continuous
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    IntegrableOn g (Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1) := by
  apply (hg.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
  exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self

private lemma integrable_restricted_unitSquare_of_continuous
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) :
    Integrable g
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod
        (volume.restrict (Ioc (0 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  exact integrableOn_unitSquare_of_continuous hg

private lemma double_intervalIntegral_swap_of_continuous
    {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g s t) =
      ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..1, g s t := by
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integral_integral_swap
    (integrable_restricted_unitSquare_of_continuous hg)

private lemma double_intervalIntegral_eq_prod_of_continuous
    {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g s t) =
      ∫ z, g z.1 z.2 ∂
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod
          (volume.restrict (Ioc (0 : ℝ) 1))) := by
  simp_rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact integral_integral
    (integrable_restricted_unitSquare_of_continuous hg)

private lemma double_intervalIntegral_add_of_continuous
    {g k : ℝ → ℝ → ℝ}
    (hg : Continuous (Function.uncurry g))
    (hk : Continuous (Function.uncurry k)) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g s t + k s t) =
      (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g s t) +
        ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, k s t := by
  let μ := (volume.restrict (Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Ioc (0 : ℝ) 1))
  have hgInt : Integrable (Function.uncurry g) μ :=
    integrable_restricted_unitSquare_of_continuous hg
  have hkInt : Integrable (Function.uncurry k) μ :=
    integrable_restricted_unitSquare_of_continuous hk
  have hadd : Continuous (Function.uncurry
      (fun s t : ℝ => g s t + k s t)) := by
    simpa [Function.uncurry] using hg.add hk
  rw [double_intervalIntegral_eq_prod_of_continuous hadd,
    double_intervalIntegral_eq_prod_of_continuous hg,
    double_intervalIntegral_eq_prod_of_continuous hk]
  exact integral_add hgInt hkInt

private lemma double_intervalIntegral_const_mul_of_continuous
    (c : ℝ) {g : ℝ → ℝ → ℝ}
    (hg : Continuous (Function.uncurry g)) :
    (∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, c * g s t) =
      c * ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, g s t := by
  rw [double_intervalIntegral_eq_prod_of_continuous
      (continuous_const.mul hg),
    double_intervalIntegral_eq_prod_of_continuous hg]
  exact integral_const_mul c _

private lemma leftDiagonal_eq_neg_onePoint (q : ℝ → ℝ) :
    leftDiagonal q = -(∫ s in (0 : ℝ)..1, F s * s * q s ^ 2) := by
  unfold leftDiagonal
  calc
    (∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s ^ 2) =
        ∫ s in (0 : ℝ)..1, -(F s * s * q s ^ 2) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hsIcc : s ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
          calc
            (∫ t in (0 : ℝ)..1, covarianceKernel s t * q s ^ 2) =
                q s ^ 2 * ∫ t in (0 : ℝ)..1, covarianceKernel s t := by
                  rw [← intervalIntegral.integral_const_mul]
                  apply intervalIntegral.integral_congr
                  intro t ht
                  ring
            _ = q s ^ 2 * (-s * F s) := by
              rw [integral_covarianceKernel s hsIcc]
            _ = -(F s * s * q s ^ 2) := by ring
    _ = -(∫ s in (0 : ℝ)..1, F s * s * q s ^ 2) := by
      rw [intervalIntegral.integral_neg]

private lemma rightDiagonal_eq_leftDiagonal (q : ℝ → ℝ)
    (hq : Continuous q) : rightDiagonal q = leftDiagonal q := by
  unfold rightDiagonal leftDiagonal
  calc
    (∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1, covarianceKernel s t * q t ^ 2) =
        ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..1, covarianceKernel s t * q t ^ 2 :=
      double_intervalIntegral_swap_of_continuous
        (continuous_uncurry_kernel_mul_right_sq q hq)
    _ = ∫ t in (0 : ℝ)..1,
          ∫ s in (0 : ℝ)..1, covarianceKernel t s * q t ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply intervalIntegral.integral_congr
      intro s hs
      change covarianceKernel s t * q t ^ 2 = covarianceKernel t s * q t ^ 2
      rw [covarianceKernel_comm s t]

private lemma differenceSquareTerm_expansion (q : ℝ → ℝ)
    (hq : Continuous q) :
    differenceSquareTerm q =
      leftDiagonal q + rightDiagonal q - 2 * crossTerm q := by
  have hleft := continuous_uncurry_kernel_mul_left_sq q hq
  have hright := continuous_uncurry_kernel_mul_right_sq q hq
  have hcross := continuous_uncurry_kernel_mul_cross q hq
  unfold differenceSquareTerm leftDiagonal rightDiagonal crossTerm
  calc
    (∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1,
          covarianceKernel s t * (q s - q t) ^ 2) =
        ∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            (covarianceKernel s t * q s ^ 2 +
              (covarianceKernel s t * q t ^ 2 +
                (-2 : ℝ) * (covarianceKernel s t * q s * q t))) := by
      apply intervalIntegral.integral_congr
      intro s hs
      apply intervalIntegral.integral_congr
      intro t ht
      ring
    _ =
        (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s ^ 2) +
        ((∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1, covarianceKernel s t * q t ^ 2) +
        (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            (-2 : ℝ) * (covarianceKernel s t * q s * q t))) := by
      rw [double_intervalIntegral_add_of_continuous hleft
        (hright.add (continuous_const.mul hcross))]
      rw [double_intervalIntegral_add_of_continuous hright
        (continuous_const.mul hcross)]
    _ =
        (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s ^ 2) +
        (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1, covarianceKernel s t * q t ^ 2) -
        2 * (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1, covarianceKernel s t * q s * q t) := by
      rw [double_intervalIntegral_const_mul_of_continuous (-2) hcross]
      ring

/-- Exact Dirichlet representation of the Poisson--Dickman covariance form.

This is the unconditional algebraic core of the Dirichlet route.  Its only
analytic inputs are continuity (for Fubini) and the already proved row-sum
identity `integral_covarianceKernel`. -/
theorem conjugatedQuadratic_eq_dirichletEnergy (q : ℝ → ℝ)
    (hq : Continuous q) :
    conjugatedQuadratic q = dirichletEnergy q := by
  have hleft := leftDiagonal_eq_neg_onePoint q
  have hright := rightDiagonal_eq_leftDiagonal q hq
  have hexpansion := differenceSquareTerm_expansion q hq
  change
    (∫ s in (0 : ℝ)..1, F s * s * q s ^ 2) + crossTerm q =
      -(1 / 2 : ℝ) * differenceSquareTerm q
  rw [hexpansion, hright, hleft]
  ring

lemma dirichletEnergy_eq_half_positiveDirichletIntegral (q : ℝ → ℝ) :
    dirichletEnergy q = (1 / 2 : ℝ) * positiveDirichletIntegral q := by
  have hneg : positiveDirichletIntegral q = -differenceSquareTerm q := by
    unfold positiveDirichletIntegral differenceSquareTerm
    calc
      (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            -covarianceKernel s t * (q s - q t) ^ 2) =
          ∫ s in (0 : ℝ)..1,
            -(∫ t in (0 : ℝ)..1,
              covarianceKernel s t * (q s - q t) ^ 2) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change
          (∫ t in (0 : ℝ)..1,
            -covarianceKernel s t * (q s - q t) ^ 2) =
          -(∫ t in (0 : ℝ)..1,
            covarianceKernel s t * (q s - q t) ^ 2)
        calc
          (∫ t in (0 : ℝ)..1,
              -covarianceKernel s t * (q s - q t) ^ 2) =
              ∫ t in (0 : ℝ)..1,
                -(covarianceKernel s t * (q s - q t) ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
          _ = -(∫ t in (0 : ℝ)..1,
              covarianceKernel s t * (q s - q t) ^ 2) := by
            rw [intervalIntegral.integral_neg]
      _ = -(∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1,
            covarianceKernel s t * (q s - q t) ^ 2) := by
        rw [intervalIntegral.integral_neg]
  change -(1 / 2 : ℝ) * differenceSquareTerm q =
    (1 / 2 : ℝ) * positiveDirichletIntegral q
  rw [hneg]
  ring

/-- Abstract sign-to-energy implication, retained as a reusable deterministic
lemma.  The required sign has been proved above for the Dickman kernel. -/
theorem dirichletEnergy_nonneg_of_kernel_nonpos (q : ℝ → ℝ)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      covarianceKernel s t ≤ 0) :
    0 ≤ dirichletEnergy q := by
  have hinner (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (∫ t in (0 : ℝ)..1,
        covarianceKernel s t * (q s - q t) ^ 2) ≤ 0 := by
    have hnonneg :
        0 ≤ ∫ t in (0 : ℝ)..1,
          -(covarianceKernel s t * (q s - q t) ^ 2) := by
      apply intervalIntegral.integral_nonneg
        (show (0 : ℝ) ≤ 1 by norm_num)
      intro t ht
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (hK s hs t ht) (sq_nonneg _))
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  have hdouble :
      (∫ s in (0 : ℝ)..1,
        ∫ t in (0 : ℝ)..1,
          covarianceKernel s t * (q s - q t) ^ 2) ≤ 0 := by
    have hnonneg :
        0 ≤ ∫ s in (0 : ℝ)..1,
          -(∫ t in (0 : ℝ)..1,
            covarianceKernel s t * (q s - q t) ^ 2) := by
      apply intervalIntegral.integral_nonneg
        (show (0 : ℝ) ≤ 1 by norm_num)
      intro s hs
      exact neg_nonneg.mpr (hinner s hs)
    rw [intervalIntegral.integral_neg] at hnonneg
    linarith
  unfold dirichletEnergy
  nlinarith

/-- Abstract positive-semidefiniteness implication from a kernel sign. -/
theorem conjugatedQuadratic_nonneg_of_kernel_nonpos (q : ℝ → ℝ)
    (hq : Continuous q)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      covarianceKernel s t ≤ 0) :
    0 ≤ conjugatedQuadratic q := by
  rw [conjugatedQuadratic_eq_dirichletEnergy q hq]
  exact dirichletEnergy_nonneg_of_kernel_nonpos q hK

/-- Under strict negativity of the kernel in the open square, any genuine
variation of `q` at two interior points gives strictly positive energy. -/
theorem dirichletEnergy_pos_of_interior_ne_of_kernel_sign (q : ℝ → ℝ)
    (hq : Continuous q)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      covarianceKernel s t ≤ 0)
    (hKstrict : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1,
      covarianceKernel s t < 0)
    {a b : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : q a ≠ q b) :
    0 < dirichletEnergy q := by
  have hpoint_nonneg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      0 ≤ -covarianceKernel s t * (q s - q t) ^ 2 := by
    exact mul_nonneg (neg_nonneg.mpr (hK s hs t ht)) (sq_nonneg _)
  have hinner_nonneg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      0 ≤ positiveDirichletInner q s := by
    unfold positiveDirichletInner
    apply intervalIntegral.integral_nonneg
      (show (0 : ℝ) ≤ 1 by norm_num)
    intro t ht
    exact hpoint_nonneg s hs t ht
  have hpoint_pos :
      0 < -covarianceKernel a b * (q a - q b) ^ 2 := by
    have hkernel : 0 < -covarianceKernel a b :=
      neg_pos.mpr (hKstrict a ha b hb)
    have hsq : 0 < (q a - q b) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
    exact mul_pos hkernel hsq
  have hinner_pos : 0 < positiveDirichletInner q a := by
    unfold positiveDirichletInner
    apply intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
    · exact (continuous_uncurry_positiveDirichletIntegrand q hq).comp
        (continuous_const.prodMk continuous_id) |>.continuousOn
    · intro t ht
      exact hpoint_nonneg a ⟨ha.1.le, ha.2.le⟩ t ⟨ht.1.le, ht.2⟩
    · exact ⟨b, ⟨hb.1.le, hb.2.le⟩, hpoint_pos⟩
  have hdouble_pos : 0 < positiveDirichletIntegral q := by
    change 0 < ∫ s in (0 : ℝ)..1, positiveDirichletInner q s
    apply intervalIntegral.integral_pos (show (0 : ℝ) < 1 by norm_num)
    · exact (continuous_positiveDirichletInner q hq).continuousOn
    · intro s hs
      exact hinner_nonneg s ⟨hs.1.le, hs.2⟩
    · exact ⟨a, ⟨ha.1.le, ha.2.le⟩, hinner_pos⟩
  rw [dirichletEnergy_eq_half_positiveDirichletIntegral]
  positivity

/-- Abstract kernel characterization assuming the closed and open kernel
signs.  Its unconditional Dickman specialization is stated below. -/
theorem dirichletEnergy_eq_zero_iff_constantOn_of_kernel_sign (q : ℝ → ℝ)
    (hq : Continuous q)
    (hK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      covarianceKernel s t ≤ 0)
    (hKstrict : ∀ s ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Ioo (0 : ℝ) 1,
      covarianceKernel s t < 0) :
    dirichletEnergy q = 0 ↔
      ∃ lambda : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, q t = lambda := by
  constructor
  · intro hzero
    let c : ℝ := (1 : ℝ) / 2
    have hc : c ∈ Ioo (0 : ℝ) 1 := by norm_num [c]
    have hinterior : Set.EqOn q (fun _ : ℝ => q c) (Ioo (0 : ℝ) 1) := by
      intro t ht
      by_contra hne
      have hpos := dirichletEnergy_pos_of_interior_ne_of_kernel_sign
        q hq hK hKstrict ht hc hne
      linarith
    have hclosed : Set.EqOn q (fun _ : ℝ => q c) (Icc (0 : ℝ) 1) := by
      apply hinterior.of_subset_closure hq.continuousOn continuousOn_const
        Ioo_subset_Icc_self
      rw [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)]
    exact ⟨q c, hclosed⟩
  · rintro ⟨lambda, hconstant⟩
    rw [dirichletEnergy_eq_half_positiveDirichletIntegral]
    have hzero : positiveDirichletIntegral q = 0 := by
      unfold positiveDirichletIntegral
      calc
        (∫ s in (0 : ℝ)..1,
            ∫ t in (0 : ℝ)..1,
              -covarianceKernel s t * (q s - q t) ^ 2) =
            ∫ _s in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hsIcc : s ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hs
          calc
            (∫ t in (0 : ℝ)..1,
                -covarianceKernel s t * (q s - q t) ^ 2) =
                ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              have htIcc : t ∈ Icc (0 : ℝ) 1 := by
                simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
              change -covarianceKernel s t * (q s - q t) ^ 2 = 0
              rw [hconstant s hsIcc, hconstant t htIcc]
              simp
            _ = 0 := by simp
        _ = 0 := by simp
    rw [hzero]
    ring

/-! ## Unconditional covariance consequences -/

theorem dirichletEnergy_nonneg (q : ℝ → ℝ) :
    0 ≤ dirichletEnergy q :=
  dirichletEnergy_nonneg_of_kernel_nonpos q
    (fun s hs t ht => @covarianceKernel_nonpos s t hs ht)

theorem conjugatedQuadratic_nonneg (q : ℝ → ℝ) (hq : Continuous q) :
    0 ≤ conjugatedQuadratic q :=
  conjugatedQuadratic_nonneg_of_kernel_nonpos q hq
    (fun s hs t ht => @covarianceKernel_nonpos s t hs ht)

theorem dirichletEnergy_pos_of_interior_ne (q : ℝ → ℝ)
    (hq : Continuous q) {a b : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hb : b ∈ Ioo (0 : ℝ) 1)
    (hab : q a ≠ q b) :
    0 < dirichletEnergy q :=
  dirichletEnergy_pos_of_interior_ne_of_kernel_sign q hq
    (fun s hs t ht => @covarianceKernel_nonpos s t hs ht)
    (fun s hs t ht => @covarianceKernel_neg s t hs ht) ha hb hab

theorem dirichletEnergy_eq_zero_iff_constantOn (q : ℝ → ℝ)
    (hq : Continuous q) :
    dirichletEnergy q = 0 ↔
      ∃ lambda : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, q t = lambda :=
  dirichletEnergy_eq_zero_iff_constantOn_of_kernel_sign q hq
    (fun s hs t ht => @covarianceKernel_nonpos s t hs ht)
    (fun s hs t ht => @covarianceKernel_neg s t hs ht)

/-- Continuous conjugated covariance tests have exactly the scale direction
as their nullspace: `q` is constant, so the original test `t * q t` is a
constant multiple of `t`. -/
theorem conjugatedQuadratic_eq_zero_iff_constantOn (q : ℝ → ℝ)
    (hq : Continuous q) :
    conjugatedQuadratic q = 0 ↔
      ∃ lambda : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, q t = lambda := by
  rw [conjugatedQuadratic_eq_dirichletEnergy q hq]
  exact dirichletEnergy_eq_zero_iff_constantOn q hq

/-- Pairwise variation on a compact square separated from the singular
endpoint.  It is invariant under adding a constant to `q`, hence is a
literal quotient seminorm for the scale-null direction. -/
def truncatedPairVariation (epsilon : ℝ) (q : ℝ → ℝ) : ℝ :=
  ∫ s in epsilon..(1 - epsilon),
    ∫ t in epsilon..(1 - epsilon), (q s - q t) ^ 2

/-- Quantitative compact-interior quotient gap.  For every fixed cutoff away
from `0` and `1`, the full Dickman Dirichlet energy uniformly controls the
pairwise-variation quotient seminorm on the truncated interval.  No spectral
gap or kernel-sign premise is supplied as an argument. -/
theorem exists_truncated_dirichlet_quotient_gap {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ q : ℝ → ℝ, Continuous q →
      gamma * truncatedPairVariation epsilon q ≤ dirichletEnergy q := by
  obtain ⟨kappa, hkappa, hkernel⟩ :=
    exists_truncated_covarianceKernel_gap hepsilon hhalf
  let a : ℝ := epsilon
  let b : ℝ := 1 - epsilon
  have h0a : 0 ≤ a := by dsimp [a]; exact hepsilon.le
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  refine ⟨kappa / 2, half_pos hkappa, ?_⟩
  intro q hq
  let V : ℝ → ℝ → ℝ := fun s t => (q s - q t) ^ 2
  let G : ℝ → ℝ → ℝ := fun s t =>
    -covarianceKernel s t * (q s - q t) ^ 2
  have hVcont : Continuous (Function.uncurry V) := by
    dsimp only [V]
    exact (((hq.comp continuous_fst).sub (hq.comp continuous_snd)).pow 2)
  have hGcont : Continuous (Function.uncurry G) := by
    dsimp only [G]
    exact continuous_uncurry_positiveDirichletIntegrand q hq
  have hVinnerCont : Continuous (fun s : ℝ => ∫ t in a..b, V s t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := a) (b₀ := b)
    exact hVcont
  have hGinnerLocalCont : Continuous (fun s : ℝ => ∫ t in a..b, G s t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := a) (b₀ := b)
    exact hGcont
  have hGinnerFullCont : Continuous (fun s : ℝ => ∫ t in (0 : ℝ)..1, G s t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := (0 : ℝ)) (b₀ := 1)
    exact hGcont
  have hpoint_nonneg (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ G s t := by
    dsimp only [G]
    exact mul_nonneg
      (neg_nonneg.mpr (@covarianceKernel_nonpos s t hs ht)) (sq_nonneg _)
  have hinnerCompare (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ t in a..b, kappa * V s t) ≤ ∫ t in a..b, G s t := by
    have hleft : IntervalIntegrable (fun t : ℝ => kappa * V s t) volume a b :=
      (continuous_const.mul
        (hVcont.comp (continuous_const.prodMk continuous_id)))
        |>.intervalIntegrable a b
    have hright : IntervalIntegrable (fun t : ℝ => G s t) volume a b :=
      (hGcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b
    apply intervalIntegral.integral_mono_on hab hleft hright
    intro t ht
    have hs' : s ∈ Icc epsilon (1 - epsilon) := by simpa [a, b] using hs
    have ht' : t ∈ Icc epsilon (1 - epsilon) := by simpa [a, b] using ht
    dsimp only [V, G]
    exact mul_le_mul_of_nonneg_right (hkernel s hs' t ht') (sq_nonneg _)
  have hscaled :
      kappa * truncatedPairVariation epsilon q =
        ∫ s in a..b, ∫ t in a..b, kappa * V s t := by
    unfold truncatedPairVariation
    change kappa * (∫ s in a..b, ∫ t in a..b, V s t) = _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    change kappa * (∫ t in a..b, V s t) = ∫ t in a..b, kappa * V s t
    rw [intervalIntegral.integral_const_mul]
  have hlocalCompare :
      (∫ s in a..b, ∫ t in a..b, kappa * V s t) ≤
        ∫ s in a..b, ∫ t in a..b, G s t := by
    have hleftCont : Continuous
        (fun s : ℝ => ∫ t in a..b, kappa * V s t) := by
      simpa only [intervalIntegral.integral_const_mul] using
        continuous_const.mul hVinnerCont
    apply intervalIntegral.integral_mono_on hab
      (hleftCont.intervalIntegrable a b)
      (hGinnerLocalCont.intervalIntegrable a b)
    exact hinnerCompare
  have hlocalToFullInner (s : ℝ) (hs : s ∈ Icc a b) :
      (∫ t in a..b, G s t) ≤ ∫ t in (0 : ℝ)..1, G s t := by
    have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] fun t => G s t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have hs01 : s ∈ Icc (0 : ℝ) 1 :=
        ⟨h0a.trans hs.1, hs.2.trans hb1⟩
      exact hpoint_nonneg s hs01 t ⟨ht.1.le, ht.2⟩
    exact intervalIntegral.integral_mono_interval h0a hab hb1 hnonneg
      ((hGcont.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1)
  have hmiddle :
      (∫ s in a..b, ∫ t in a..b, G s t) ≤
        ∫ s in a..b, ∫ t in (0 : ℝ)..1, G s t := by
    apply intervalIntegral.integral_mono_on hab
      (hGinnerLocalCont.intervalIntegrable a b)
      (hGinnerFullCont.intervalIntegrable a b)
    exact hlocalToFullInner
  have hfullInnerNonneg :
      0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
        fun s => ∫ t in (0 : ℝ)..1, G s t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    apply intervalIntegral.integral_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    intro t ht
    exact hpoint_nonneg s ⟨hs.1.le, hs.2⟩ t ht
  have houter :
      (∫ s in a..b, ∫ t in (0 : ℝ)..1, G s t) ≤
        ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, G s t :=
    intervalIntegral.integral_mono_interval h0a hab hb1 hfullInnerNonneg
      (hGinnerFullCont.intervalIntegrable 0 1)
  have htotal :
      kappa * truncatedPairVariation epsilon q ≤ positiveDirichletIntegral q := by
    unfold positiveDirichletIntegral
    change kappa * truncatedPairVariation epsilon q ≤
      ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, G s t
    rw [hscaled]
    exact hlocalCompare.trans (hmiddle.trans houter)
  rw [dirichletEnergy_eq_half_positiveDirichletIntegral]
  calc
    kappa / 2 * truncatedPairVariation epsilon q =
        (1 / 2 : ℝ) * (kappa * truncatedPairVariation epsilon q) := by ring
    _ ≤ (1 / 2 : ℝ) * positiveDirichletIntegral q :=
      mul_le_mul_of_nonneg_left htotal (by norm_num)

end Erdos390.Full.PoissonDickmanDirichlet
