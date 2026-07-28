import Erdos390.WholePaper.RoughSaiasNormalization
import Erdos390.WholePaper.RoughSaiasRightAbel

/-!
# The compact Dickman kernel for the de Bruijn signed functional

This file isolates the only nonsmooth point in the integration-by-parts
identification of the Saias normal form.  The repository's finite Dickman
function is `1` to the left of the first face, so its right derivative as a
function of the Stieltjes variable is zero when the logarithmic coordinate
is exactly `1`.  This is different at one point from
`roughSaiasDickmanDerivative`, whose value at `1` is the *Dickman-coordinate*
right limit `-1`.

The open-face representative below has value zero at that corner.  It gives
an honest right derivative for the Stieltjes test function; changing it back
to `roughSaiasDickmanDerivative` later is an almost-everywhere, one-point
change.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- Zero on the closed initial face, and the Dickman delay derivative on
the open noninitial faces.  In particular its value at `1` is zero. -/
noncomputable def roughSaiasOpenFaceDickmanDerivative (u : ℝ) : ℝ :=
  if u ≤ 1 then 0 else -rho (u - 1) / u

@[simp]
theorem roughSaiasOpenFaceDickmanDerivative_of_le_one
    {u : ℝ} (hu : u ≤ 1) :
    roughSaiasOpenFaceDickmanDerivative u = 0 := by
  simp [roughSaiasOpenFaceDickmanDerivative, hu]

theorem roughSaiasOpenFaceDickmanDerivative_of_one_lt
    {u : ℝ} (hu : 1 < u) :
    roughSaiasOpenFaceDickmanDerivative u = -rho (u - 1) / u := by
  simp [roughSaiasOpenFaceDickmanDerivative, not_le.mpr hu]

@[simp]
theorem roughSaiasOpenFaceDickmanDerivative_one :
    roughSaiasOpenFaceDickmanDerivative 1 = 0 := by
  simp [roughSaiasOpenFaceDickmanDerivative]

/-- Away from the single corner, the open-face and right-limit
representatives agree pointwise. -/
theorem roughSaiasOpenFaceDickmanDerivative_eq_roughSaias
    {u : ℝ} (hu : u ≠ 1) :
    roughSaiasOpenFaceDickmanDerivative u =
      roughSaiasDickmanDerivative u := by
  rcases lt_or_gt_of_ne hu with hu1 | h1u
  · rw [roughSaiasOpenFaceDickmanDerivative_of_le_one hu1.le,
      roughSaiasDickmanDerivative_of_lt_one hu1]
  · rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt h1u,
      roughSaiasDickmanDerivative_of_one_le h1u.le]

theorem measurable_roughSaiasOpenFaceDickmanDerivative :
    Measurable roughSaiasOpenFaceDickmanDerivative := by
  unfold roughSaiasOpenFaceDickmanDerivative
  apply Measurable.ite measurableSet_Iic measurable_const
  exact (continuous_rho.measurable.comp
    (measurable_id.sub_const 1)).neg.div measurable_id

/-- The open-face representative has the same unit bound as the
right-limit representative on the compact five-face range. -/
theorem roughSaiasOpenFaceDickmanDerivative_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasOpenFaceDickmanDerivative u| ≤ 1 := by
  by_cases hu1 : u ≤ 1
  · simp [roughSaiasOpenFaceDickmanDerivative_of_le_one hu1]
  · have h1u : 1 < u := lt_of_not_ge hu1
    have hb := FriableAsymptotic.rho_delay_integrand_bounds h1u.le hu5
    rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt
        h1u, neg_div, abs_neg, abs_of_nonneg hb.1]
    exact hb.2

/-- In a translated convolution the two derivative representatives differ
at most at `v = u - 1`, so their interval integrals are identical. -/
theorem roughSaiasOpenFace_convolution_eq_rightLimit
    (u a b : ℝ) (w : ℝ → ℝ) :
    (∫ v in a..b,
        roughSaiasOpenFaceDickmanDerivative (u - v) * w v) =
      ∫ v in a..b,
        roughSaiasDickmanDerivative (u - v) * w v := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [((volume : Measure ℝ).ae_ne (u - 1))] with v hv _hvI
  have huv : u - v ≠ 1 := by
    intro h
    apply hv
    linarith
  rw [roughSaiasOpenFaceDickmanDerivative_eq_roughSaias huv]

/-! ## Real logarithmic coordinate and Stieltjes test function -/

/-- Logarithmic Dickman coordinate in the real Stieltjes variable. -/
noncomputable def roughSaiasStieltjesCoordinate
    (x y t : ℝ) : ℝ :=
  (Real.log x - Real.log t) / Real.log y

/-- The Abel test function whose integer values are the atoms
`x*rho(log(x/n)/log y)/n`. -/
noncomputable def roughSaiasStieltjesTest
    (x y t : ℝ) : ℝ :=
  x * rho (roughSaiasStieltjesCoordinate x y t) / t

/-- The honest right derivative of `roughSaiasStieltjesTest` on positive
Stieltjes variables. -/
noncomputable def roughSaiasStieltjesTestRightDerivative
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
        (roughSaiasStieltjesCoordinate x y t) *
      (-1 / (t * Real.log y)) / t -
    x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2

/-- On `1 ≤ t ≤ x`, the Stieltjes coordinate stays between zero and
the endpoint coordinate. -/
theorem roughSaiasStieltjesCoordinate_mem
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x) :
    0 ≤ roughSaiasStieltjesCoordinate x y t ∧
      roughSaiasStieltjesCoordinate x y t ≤
        Real.log x / Real.log y := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogtx : Real.log t ≤ Real.log x :=
    Real.log_le_log htpos htx
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  unfold roughSaiasStieltjesCoordinate
  constructor
  · exact div_nonneg (sub_nonneg.mpr hlogtx) hlogy.le
  · apply (div_le_iff₀ hlogy).2
    have hendpoint :
        Real.log x / Real.log y * Real.log y = Real.log x := by
      field_simp [hlogy.ne']
    rw [hendpoint]
    linarith

/-- Continuity of the Stieltjes test on every positive compact interval. -/
theorem continuousOn_roughSaiasStieltjesTest
    {x y A B : ℝ} (hy : 1 < y) (hA : 0 < A) :
    ContinuousOn (roughSaiasStieltjesTest x y) (Set.Icc A B) := by
  intro t ht
  have htpos : 0 < t := hA.trans_le ht.1
  have ht0 : t ≠ 0 := htpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hcoord : ContinuousAt (roughSaiasStieltjesCoordinate x y) t := by
    unfold roughSaiasStieltjesCoordinate
    exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div_const _
  unfold roughSaiasStieltjesTest
  exact ((continuousAt_const.mul
      (continuous_rho.continuousAt.comp hcoord)).div
        continuousAt_id ht0).continuousWithinAt

/-! ## The corner-safe right derivative -/

/-- The displayed derivative is the genuine right derivative throughout
the compact Stieltjes interval.  At coordinate `1`, increasing `t` moves
onto the constant Dickman face, hence the zero open-face value above. -/
theorem hasDerivWithinAt_roughSaiasStieltjesTest_right
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt (roughSaiasStieltjesTest x y)
      (roughSaiasStieltjesTestRightDerivative x y t)
      (Set.Ioi t) t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have ht0 : t ≠ 0 := htpos.ne'
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoordMem := roughSaiasStieltjesCoordinate_mem hy ht1 htx
  have hcoord5 : roughSaiasStieltjesCoordinate x y t ≤ 5 :=
    hcoordMem.2.trans hu5
  by_cases hface : roughSaiasStieltjesCoordinate x y t ≤ 1
  · have heq :
        roughSaiasStieltjesTest x y =ᶠ[nhdsWithin t (Set.Ioi t)]
          (fun s : ℝ ↦ x / s) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hts : t < s := hs
      have hspos : 0 < s := htpos.trans hts
      have hlogts : Real.log t < Real.log s :=
        Real.strictMonoOn_log htpos hspos hts
      have hcoordLt :
          roughSaiasStieltjesCoordinate x y s <
            roughSaiasStieltjesCoordinate x y t := by
        unfold roughSaiasStieltjesCoordinate
        exact (div_lt_div_iff_of_pos_right hlogy).2 (by linarith)
      rw [roughSaiasStieltjesTest,
        rho_eq_one_of_le_one (hcoordLt.le.trans hface)]
      ring
    have hsimple : HasDerivAt (fun s : ℝ ↦ x / s) (-x / t ^ 2) t := by
      have h := (hasDerivAt_const t x).div (hasDerivAt_id t) ht0
      convert h using 1
      simp only [id_eq, zero_mul, mul_one, zero_sub]
    have hvalue : roughSaiasStieltjesTest x y t = x / t := by
      rw [roughSaiasStieltjesTest, rho_eq_one_of_le_one hface]
      ring
    have hcongr := hsimple.hasDerivWithinAt.congr_of_eventuallyEq
      heq hvalue
    convert hcongr using 1
    unfold roughSaiasStieltjesTestRightDerivative
    simp only [roughSaiasOpenFaceDickmanDerivative_of_le_one hface,
      mul_zero, zero_mul, zero_div, rho_eq_one_of_le_one hface,
      mul_one, zero_sub]
    ring
  · have hface' : 1 < roughSaiasStieltjesCoordinate x y t :=
      lt_of_not_ge hface
    have hcoordDeriv :
        HasDerivAt (roughSaiasStieltjesCoordinate x y)
          (-1 / (t * Real.log y)) t := by
      unfold roughSaiasStieltjesCoordinate
      have h := ((hasDerivAt_const t (Real.log x)).sub
        (Real.hasDerivAt_log ht0)).div_const (Real.log y)
      convert h using 1
      field_simp [ht0, hlogy.ne']
      ring
    have hrho : HasDerivAt
        (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        ((-rho (roughSaiasStieltjesCoordinate x y t - 1) /
            roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y))) t :=
      (hasDerivAt_rho hface' (hcoord5.trans (by norm_num))).comp t hcoordDeriv
    have hquot := ((hasDerivAt_const t x).mul hrho).div
      (hasDerivAt_id t) ht0
    convert hquot.hasDerivWithinAt using 1
    unfold roughSaiasStieltjesTestRightDerivative
    rw [roughSaiasOpenFaceDickmanDerivative_of_one_lt hface']
    simp only [id_eq, Pi.mul_apply, zero_mul, zero_add, mul_one]
    field_simp [ht0]

/-- The right-derivative theorem in the exact open-interval shape expected
by `sum_mul_eq_sub_sub_integral_mul_right`. -/
theorem roughSaiasStieltjesTest_hasRightDerivOn
    {x y R : ℝ} (hy : 1 < y) (_hR : 1 ≤ R) (hRx : R ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    ∀ t ∈ Set.Ioo (1 : ℝ) R,
      HasDerivWithinAt (roughSaiasStieltjesTest x y)
        (roughSaiasStieltjesTestRightDerivative x y t)
        (Set.Ioi t) t := by
  intro t ht
  exact hasDerivWithinAt_roughSaiasStieltjesTest_right hy ht.1.le
    (ht.2.le.trans hRx) hu5

/-! ## Integrability of the right derivative -/

theorem measurable_roughSaiasStieltjesCoordinate (x y : ℝ) :
    Measurable (roughSaiasStieltjesCoordinate x y) := by
  unfold roughSaiasStieltjesCoordinate
  exact (measurable_const.sub Real.measurable_log).div measurable_const

theorem measurable_roughSaiasStieltjesTestRightDerivative
    (x y : ℝ) :
    Measurable (roughSaiasStieltjesTestRightDerivative x y) := by
  have hcoord := measurable_roughSaiasStieltjesCoordinate x y
  unfold roughSaiasStieltjesTestRightDerivative
  exact (((measurable_const.mul
      (measurable_roughSaiasOpenFaceDickmanDerivative.comp hcoord)).mul
        (measurable_const.div
          (measurable_id.mul measurable_const))).div measurable_id).sub
      ((measurable_const.mul (continuous_rho.measurable.comp hcoord)).div
        (measurable_id.pow_const 2))

/-- A crude compact majorant, used only to certify ordinary integrability.
The later sharp estimates retain the signed kernel and do not use this
triangle inequality. -/
theorem roughSaiasStieltjesTestRightDerivative_abs_le
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    |roughSaiasStieltjesTestRightDerivative x y t| ≤
      x * (1 / Real.log y + 1) := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hxpos : 0 < x := htpos.trans_le htx
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hcoord := roughSaiasStieltjesCoordinate_mem hy ht1 htx
  have hcoord5 : roughSaiasStieltjesCoordinate x y t ≤ 5 :=
    hcoord.2.trans hu5
  have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one hcoord5
  have hrho0 : 0 ≤ rho (roughSaiasStieltjesCoordinate x y t) :=
    (rho_pos_on_zero_five hcoord.1 hcoord5).le
  have hrho1 : rho (roughSaiasStieltjesCoordinate x y t) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hcoord5
  have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
  have hinvDenom : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
    apply one_div_le_one_div_of_le hlogy
    nlinarith [mul_le_mul_of_nonneg_right ht1 hlogy.le]
  have hfirstNonneg :
      0 ≤ x *
        |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t)| *
          (1 / (t * Real.log y)) := by positivity
  have hfirst :
      |x * roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)) / t| ≤
        x * (1 / Real.log y) := by
    calc
      _ = (x *
          |roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t)| *
            (1 / (t * Real.log y))) / t := by
          rw [abs_div, abs_mul, abs_mul, neg_div, abs_neg, abs_div,
            abs_one, abs_of_pos hxpos, abs_of_pos hdenom,
            abs_of_pos htpos]
      _ ≤ x *
          |roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t)| *
            (1 / (t * Real.log y)) :=
        div_le_self hfirstNonneg ht1
      _ ≤ x * 1 * (1 / Real.log y) := by
        gcongr
      _ = x * (1 / Real.log y) := by ring
  have hsecond :
      |x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2| ≤ x := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg hxpos.le hrho0)
      (sq_nonneg t))]
    calc
      x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2 ≤
          x * rho (roughSaiasStieltjesCoordinate x y t) :=
        div_le_self (mul_nonneg hxpos.le hrho0) (by nlinarith)
      _ ≤ x * 1 := mul_le_mul_of_nonneg_left hrho1 hxpos.le
      _ = x := mul_one x
  unfold roughSaiasStieltjesTestRightDerivative
  calc
    _ ≤
        |x * roughSaiasOpenFaceDickmanDerivative
              (roughSaiasStieltjesCoordinate x y t) *
            (-1 / (t * Real.log y)) / t| +
          |x * rho (roughSaiasStieltjesCoordinate x y t) / t ^ 2| :=
      abs_sub _ _
    _ ≤ x * (1 / Real.log y) + x := add_le_add hfirst hsecond
    _ = x * (1 / Real.log y + 1) := by ring

/-- The corner-safe derivative is integrable on the entire natural compact
interval needed by the finite signed functional. -/
theorem integrableOn_roughSaiasStieltjesTestRightDerivative
    {X : ℕ} {y : ℝ} (hX1 : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      (Set.Icc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX1
  have hC : 0 ≤ (X : ℝ) * (1 / Real.log y + 1) := by
    have hlogy : 0 < Real.log y := Real.log_pos hy
    positivity
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ (X : ℝ) * (1 / Real.log y + 1))
      volume (1 : ℝ) (X : ℝ) :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable
      (roughSaiasStieltjesTestRightDerivative (X : ℝ) y)
      volume (1 : ℝ) (X : ℝ) := by
    apply hconst.mono_fun'
      (measurable_roughSaiasStieltjesTestRightDerivative
        (X : ℝ) y).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      have htIoc : t ∈ Set.Ioc (1 : ℝ) (X : ℝ) := by
        simpa [Set.uIoc_of_le hXR] using ht
      exact ⟨htIoc.1.le, htIoc.2⟩
    simpa only [Real.norm_eq_abs, abs_of_nonneg hC] using
      (roughSaiasStieltjesTestRightDerivative_abs_le
        hy htI.1 htI.2 hu5)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hint

end

end Erdos390.WholePaper
