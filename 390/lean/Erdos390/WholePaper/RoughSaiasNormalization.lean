import Erdos390.WholePaper.RoughFriableFaceInduction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# The finite de Bruijn--Saias normal form on the five Dickman faces

Section 8.5 of the paper uses the integration-by-parts identity

`Lambda(z,y) = z * G_y(log z / log y) - fract z`,

where

`G_y(u) = rho(u) - integral rho'(u-v) * fract(y^v) * y^(-v) dv`.

This file formalizes the finite normal form, its exact initial face, the
compact bounded-variation datum behind the asserted Lipschitz estimate, and
the exact way in which this normalization enters the already isolated rough
prime-transition ledger.

The cited Hildebrand--Tenenbaum--Saias estimate for `Psi - Lambda` is not
proved in the paper.  Accordingly, no theorem below declares that estimate
as an axiom.  Its precise endpoint-shaped consequence is exposed as a `Prop`
which can be passed to a reduction theorem.  In particular, the endpoint
error remains proportional to `A+B`, not to the short gap `B-A`.
-/

open scoped BigOperators Interval ENNReal

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The finite `G_y` normal form -/

/-- The right-continuous representative of the derivative of the finite
Dickman function, extended by zero on the open initial face.  The value at
`u = 1` is the right limit `-1`; changing one point does not change any
Lebesgue integral below. -/
noncomputable def roughSaiasDickmanDerivative (u : ℝ) : ℝ :=
  if u < 1 then 0 else -rho (u - 1) / u

/-- The fractional weight occurring after integration by parts in the
de Bruijn--Saias normalization. -/
noncomputable def roughSaiasFractionalWeight (y : ℕ) (v : ℝ) : ℝ :=
  Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v)

/-- A fixed-interval version of `G_y`.  For `u <= 5`, the zero extension of
the Dickman derivative makes this equal to the paper's integral over
`[0, (u-1)_+]`; see `roughSaiasG_eq_moving` below. -/
noncomputable def roughSaiasG (y : ℕ) (u : ℝ) : ℝ :=
  rho u - ∫ v in (0 : ℝ)..5,
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFractionalWeight y v

/-- The literal moving-endpoint expression printed in the paper. -/
noncomputable def roughSaiasGMoving (y : ℕ) (u : ℝ) : ℝ :=
  rho u - ∫ v in (0 : ℝ)..max (u - 1) 0,
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFractionalWeight y v

/-- The finite normal form `z * G_y(u) - fract z`.  This definition does not
silently assert equality with the Stieltjes-integral definition of `Lambda`;
that equality is the integration-by-parts step from the cited source. -/
noncomputable def roughSaiasLambdaNormalForm (z : ℝ) (y : ℕ) : ℝ :=
  z * roughSaiasG y (Real.log z / Real.log (y : ℝ)) - Int.fract z

@[simp]
theorem roughSaiasDickmanDerivative_of_lt_one
    {u : ℝ} (hu : u < 1) :
    roughSaiasDickmanDerivative u = 0 := by
  simp [roughSaiasDickmanDerivative, hu]

theorem roughSaiasDickmanDerivative_of_one_le
    {u : ℝ} (hu : 1 ≤ u) :
    roughSaiasDickmanDerivative u = -rho (u - 1) / u := by
  simp [roughSaiasDickmanDerivative, not_lt.mpr hu]

@[simp]
theorem roughSaiasDickmanDerivative_one :
    roughSaiasDickmanDerivative 1 = -1 := by
  simp [roughSaiasDickmanDerivative]

theorem measurable_roughSaiasDickmanDerivative :
    Measurable roughSaiasDickmanDerivative := by
  unfold roughSaiasDickmanDerivative
  apply Measurable.ite measurableSet_Iio measurable_const
  exact (continuous_rho.measurable.comp
    (measurable_id.sub_const 1)).neg.div measurable_id

theorem continuous_roughSaiasBaseRpow {y : ℕ} (hy : 0 < y) :
    Continuous (fun v : ℝ => (y : ℝ) ^ v) := by
  exact Real.continuous_const_rpow (by positivity)

theorem measurable_roughSaiasFractionalWeight {y : ℕ} (hy : 0 < y) :
    Measurable (roughSaiasFractionalWeight y) := by
  have hpow : Continuous (fun v : ℝ => (y : ℝ) ^ v) :=
    continuous_roughSaiasBaseRpow hy
  have hpowNeg : Continuous (fun v : ℝ => (y : ℝ) ^ (-v)) :=
    hpow.comp continuous_neg
  exact hpow.measurable.fract.mul hpowNeg.measurable

/-- The fractional Saias weight is uniformly between zero and one on the
integration interval. -/
theorem roughSaiasFractionalWeight_mem_unitInterval
    {y : ℕ} (hy : 1 ≤ y) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ roughSaiasFractionalWeight y v ∧
      roughSaiasFractionalWeight y v ≤ 1 := by
  have hbase : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hpowNonneg : 0 ≤ (y : ℝ) ^ (-v) :=
    Real.rpow_nonneg (by positivity) _
  have hpowLe : (y : ℝ) ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hfractNonneg : 0 ≤ Int.fract ((y : ℝ) ^ v) :=
    Int.fract_nonneg _
  have hfractLe : Int.fract ((y : ℝ) ^ v) ≤ 1 :=
    (Int.fract_lt_one _).le
  unfold roughSaiasFractionalWeight
  constructor
  · exact mul_nonneg hfractNonneg hpowNonneg
  · calc
      Int.fract ((y : ℝ) ^ v) * (y : ℝ) ^ (-v) ≤
          1 * (y : ℝ) ^ (-v) :=
        mul_le_mul_of_nonneg_right hfractLe hpowNonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
      _ = 1 := mul_one _

/-- The right-limit Dickman derivative has absolute value at most one on
the whole compact interval that can occur in the convolution. -/
theorem roughSaiasDickmanDerivative_abs_le_one
    {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasDickmanDerivative u| ≤ 1 := by
  by_cases hu1 : u < 1
  · simp [roughSaiasDickmanDerivative, hu1]
  · have hu1' : 1 ≤ u := le_of_not_gt hu1
    have hb := FriableAsymptotic.rho_delay_integrand_bounds hu1' hu5
    rw [roughSaiasDickmanDerivative_of_one_le hu1', neg_div, abs_neg,
      abs_of_nonneg hb.1]
    exact hb.2

/-- The unweighted translated derivative is interval-integrable on the
fixed compact interval. -/
theorem roughSaiasDickmanDerivative_translate_intervalIntegrable
    {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v))
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v)) :=
    measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (0 : ℝ) 5 := by
    have hvIoc : v ∈ Ioc (0 : ℝ) 5 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
    exact ⟨hvIoc.1.le, hvIoc.2⟩
  simpa only [Real.norm_eq_abs, norm_one] using
    roughSaiasDickmanDerivative_abs_le_one
      (u := u - v) (by linarith [hv'.1])

/-- The complete integrand in the finite Saias normal form is
interval-integrable. -/
theorem roughSaiasIntegrand_intervalIntegrable
    {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v)
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ => roughSaiasDickmanDerivative (u - v) *
        roughSaiasFractionalWeight y v) :=
    (measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)).mul
        (measurable_roughSaiasFractionalWeight (by omega))
  have hone : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Icc (0 : ℝ) 5 := by
    have hvIoc : v ∈ Ioc (0 : ℝ) 5 := by
      simpa [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
    exact ⟨hvIoc.1.le, hvIoc.2⟩
  have hderiv := roughSaiasDickmanDerivative_abs_le_one
    (u := u - v) (by linarith [hv'.1])
  have hweight := roughSaiasFractionalWeight_mem_unitInterval
    (y := y) (by omega) hv'.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1]
  calc
    |roughSaiasDickmanDerivative (u - v)| *
        roughSaiasFractionalWeight y v ≤
      1 * roughSaiasFractionalWeight y v :=
        mul_le_mul_of_nonneg_right hderiv hweight.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hweight.2 (by norm_num)
    _ = 1 := mul_one _

/-- On `u <= 5`, the fixed interval and the moving endpoint printed in the
paper give the same `G_y`. -/
theorem roughSaiasG_eq_moving
    {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    roughSaiasG y u = roughSaiasGMoving y u := by
  let c : ℝ := max (u - 1) 0
  let f : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFractionalWeight y v
  have hc0 : 0 ≤ c := by simp [c]
  have hc5 : c ≤ 5 := by
    dsimp [c]
    exact max_le (by linarith) (by norm_num)
  have hcMem : c ∈ [[(0 : ℝ), 5]] := by
    simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using
      (show c ∈ Icc (0 : ℝ) 5 from ⟨hc0, hc5⟩)
  have hf : IntervalIntegrable f volume 0 5 := by
    simpa only [f] using roughSaiasIntegrand_intervalIntegrable hy2 hu5
  have hparts :
      IntervalIntegrable f volume 0 c ∧
        IntervalIntegrable f volume c 5 :=
    (IntervalIntegrable.trans_iff hcMem).mp hf
  have htail : (∫ v in c..5, f v) = 0 := by
    have hcongr : (∫ v in c..5, f v) = ∫ _v in c..5, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with v
      intro hv
      have hv' : v ∈ Ioc c 5 := by
        simpa [uIoc_of_le hc5] using hv
      have hvc : c < v := hv'.1
      have hcLower : u - 1 ≤ c := le_max_left _ _
      have huv : u - v < 1 := by linarith
      simp [f, roughSaiasDickmanDerivative_of_lt_one huv]
    simpa using hcongr
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasG roughSaiasGMoving
  change rho u - ∫ v in (0 : ℝ)..5, f v =
    rho u - ∫ v in (0 : ℝ)..c, f v
  rw [← hsplit, htail, add_zero]

/-- The finite normal form is exactly the integer count on the initial
Dickman face.  This includes the corner `u = 1`: the only exceptional
integrand value is at the left endpoint and has zero fractional weight. -/
theorem roughSaiasG_eq_one_of_le_one {y : ℕ} {u : ℝ} (hu : u ≤ 1) :
    roughSaiasG y u = 1 := by
  have hzero :
      (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (u - v) *
          roughSaiasFractionalWeight y v) = 0 := by
    have hcongr :
        (∫ v in (0 : ℝ)..5,
          roughSaiasDickmanDerivative (u - v) *
            roughSaiasFractionalWeight y v) =
          ∫ _v in (0 : ℝ)..5, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Icc (0 : ℝ) 5 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
      by_cases huv : u - v < 1
      · simp [roughSaiasDickmanDerivative_of_lt_one huv]
      · have huEq : u = 1 := by linarith [hv'.1]
        have hvEq : v = 0 := by linarith [hv'.1]
        subst u
        subst v
        simp [roughSaiasFractionalWeight]
    simpa using hcongr
  rw [roughSaiasG, hzero, sub_zero, rho_eq_one_of_le_one hu]

/-- At a natural endpoint the fractional term in the normal form vanishes. -/
theorem roughSaiasLambdaNormalForm_nat
    (X y : ℕ) :
    roughSaiasLambdaNormalForm (X : ℝ) y =
      (X : ℝ) * roughSaiasG y (FriableAsymptotic.dickmanU X y) := by
  simp [roughSaiasLambdaNormalForm, FriableAsymptotic.dickmanU,
    Int.fract_natCast]

/-- The normal form itself is exactly `floor z` below the first transition. -/
theorem roughSaiasLambdaNormalForm_eq_floor
    {z : ℝ} {y : ℕ}
    (hu : Real.log z / Real.log (y : ℝ) ≤ 1) :
    roughSaiasLambdaNormalForm z y = ((⌊z⌋ : ℤ) : ℝ) := by
  rw [roughSaiasLambdaNormalForm, roughSaiasG_eq_one_of_le_one hu, mul_one]
  exact Int.self_sub_fract z

/-- For a positive natural endpoint below `y`, the finite normal form and
the genuine friable count both equal the endpoint exactly. -/
theorem roughSaiasLambdaNormalForm_eq_friableCount_initial
    {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughSaiasLambdaNormalForm (X : ℝ) y =
      (FriableAsymptotic.friableCount X y : ℝ) := by
  rw [roughSaiasLambdaNormalForm_nat,
    roughSaiasG_eq_one_of_le_one
      (FriableAsymptotic.dickmanU_le_one hX hy hXy),
    mul_one, FriableAsymptotic.friableCount_eq_self hXy]

/-! ## The bounded-variation datum and compact Lipschitz reduction -/

/-- The finite Dickman function is antitone on the whole nonnegative compact
range.  The existing library theorem starts at `1`; the initial interval is
filled in here using the exact constant branch. -/
theorem roughRho_antitoneOn_zero_five :
    AntitoneOn rho (Icc (0 : ℝ) 5) := by
  intro a ha b hb hab
  by_cases hb1 : b ≤ 1
  · rw [rho_eq_one_of_le_one hb1,
      rho_eq_one_of_le_one (hab.trans hb1)]
  by_cases ha1 : 1 ≤ a
  · exact antitoneOn_rho_one_five
      ⟨ha1, ha.2⟩ ⟨(le_of_not_ge hb1), hb.2⟩ hab
  · rw [rho_eq_one_of_le_one (le_of_not_ge ha1)]
    exact FriableAsymptotic.rho_le_one_of_le_five hb.2

/-- On the left of its single jump, the right-limit derivative extension is
antitone. -/
theorem roughSaiasDickmanDerivative_antitoneOn_left :
    AntitoneOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases hb1 : b < 1
  · have ha1 : a < 1 := hab.trans_lt hb1
    simp [roughSaiasDickmanDerivative_of_lt_one ha1,
      roughSaiasDickmanDerivative_of_lt_one hb1]
  · have hbEq : b = 1 := le_antisymm hb.2 (le_of_not_gt hb1)
    subst b
    by_cases ha1 : a < 1
    · rw [roughSaiasDickmanDerivative_of_lt_one ha1,
        roughSaiasDickmanDerivative_one]
      norm_num
    · have haEq : a = 1 :=
        le_antisymm hab (le_of_not_gt ha1)
      subst a
      exact le_rfl

/-- To the right of the jump, the Dickman derivative increases from `-1`
towards zero. -/
theorem roughSaiasDickmanDerivative_monotoneOn_right :
    MonotoneOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) := by
  intro a ha b hb hab
  have hrho : rho (b - 1) ≤ rho (a - 1) := by
    apply roughRho_antitoneOn_zero_five
    · constructor <;> linarith [ha.1, ha.2]
    · constructor <;> linarith [hb.1, hb.2]
    · linarith
  have hrhoA : 0 ≤ rho (a - 1) :=
    (rho_pos_on_zero_five (by linarith [ha.1])
      (by linarith [ha.2])).le
  have hfirst : rho (b - 1) / b ≤ rho (a - 1) / b :=
    div_le_div_of_nonneg_right hrho (by linarith [hb.1])
  have hsecond : rho (a - 1) / b ≤ rho (a - 1) / a :=
    div_le_div_of_nonneg_left hrhoA (by linarith [ha.1]) hab
  have hratio : rho (b - 1) / b ≤ rho (a - 1) / a :=
    hfirst.trans hsecond
  rw [roughSaiasDickmanDerivative_of_one_le ha.1,
    roughSaiasDickmanDerivative_of_one_le hb.1]
  calc
    -rho (a - 1) / a = -(rho (a - 1) / a) := by ring
    _ ≤ -(rho (b - 1) / b) := neg_le_neg hratio
    _ = -rho (b - 1) / b := by ring

/-- Negation does not change total variation of a real-valued function. -/
theorem eVariationOn_neg_real (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  simp only [eVariationOn, edist_neg_neg]

/-- The exact compact variation datum used by the proof in the paper.  The
single jump contributes one and the monotone right branch contributes at
most one, so the total variation is at most two. -/
theorem roughSaiasDickmanDerivative_eVariationOn_le_two :
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) ≤
      ENNReal.ofReal 2 := by
  have hleftMono : MonotoneOn
      (fun u : ℝ => -roughSaiasDickmanDerivative u)
      (Icc (-5 : ℝ) 1) := by
    intro a ha b hb hab
    exact neg_le_neg
      (roughSaiasDickmanDerivative_antitoneOn_left ha hb hab)
  have hleftNeg :
      eVariationOn (fun u : ℝ => -roughSaiasDickmanDerivative u)
          (Icc (-5 : ℝ) 1) ≤ ENNReal.ofReal 1 := by
    have hraw := hleftMono.eVariationOn_le
      (a := (-5 : ℝ)) (b := (1 : ℝ))
      (by norm_num) (by norm_num)
    norm_num [roughSaiasDickmanDerivative] at hraw
    simpa only [roughSaiasDickmanDerivative, ENNReal.ofReal_one] using hraw
  have hleft :
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) ≤
        ENNReal.ofReal 1 := by
    rw [← eVariationOn_neg_real roughSaiasDickmanDerivative
      (Icc (-5 : ℝ) 1)]
    exact hleftNeg
  have hrightRaw :=
    roughSaiasDickmanDerivative_monotoneOn_right.eVariationOn_le
      (a := (1 : ℝ)) (b := (5 : ℝ))
      (by norm_num) (by norm_num)
  have hrightRaw' :
      eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) ≤
        ENNReal.ofReal
          (roughSaiasDickmanDerivative 5 -
            roughSaiasDickmanDerivative 1) := by
    simpa using hrightRaw
  have hq5 : roughSaiasDickmanDerivative 5 ≤ 0 := by
    rw [roughSaiasDickmanDerivative_of_one_le (by norm_num)]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr
        (rho_pos_on_zero_five (by norm_num) (by norm_num)).le)
      (by norm_num)
  have hright :
      eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) ≤
        ENNReal.ofReal 1 := by
    apply hrightRaw'.trans
    apply ENNReal.ofReal_le_ofReal
    rw [roughSaiasDickmanDerivative_one]
    linarith
  have hadd :
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) +
        eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) =
      eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) := by
    simpa only [univ_inter] using
      (eVariationOn.Icc_add_Icc
        (f := roughSaiasDickmanDerivative) (s := (Set.univ : Set ℝ))
        (a := (-5 : ℝ)) (b := (1 : ℝ)) (c := (5 : ℝ))
        (by norm_num) (by norm_num) (by simp))
  calc
    eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 5) =
        eVariationOn roughSaiasDickmanDerivative (Icc (-5 : ℝ) 1) +
          eVariationOn roughSaiasDickmanDerivative (Icc (1 : ℝ) 5) :=
      hadd.symm
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal 1 := add_le_add hleft hright
    _ = ENNReal.ofReal 2 := by norm_num

theorem roughSaiasDickmanDerivative_boundedVariationOn :
    BoundedVariationOn roughSaiasDickmanDerivative
      (Icc (-5 : ℝ) 5) := by
  exact (roughSaiasDickmanDerivative_eVariationOn_le_two.trans_lt
    ENNReal.ofReal_lt_top).ne

/-- The pure real-analysis translation principle used in the paper's proof.
It is deliberately independent of `Psi`, primes, residuals, and selectors.
Mathlib currently contains bounded variation but not this standard truncated
`L¹` translation inequality in a directly applicable form. -/
def RoughCompactBVTranslationPrinciple : Prop :=
  ∀ (f : ℝ → ℝ),
    eVariationOn f (Icc (-5 : ℝ) 5) ≤ ENNReal.ofReal 2 →
    ∀ {a b : ℝ}, a ∈ Icc (0 : ℝ) 5 → b ∈ Icc (0 : ℝ) 5 →
      (∫ v in (0 : ℝ)..5, |f (a - v) - f (b - v)|) ≤
        2 * |a - b|

/-- Application of the standard compact BV translation principle to the
actual Dickman derivative, using the proved variation constant `2`. -/
theorem roughSaiasDickmanDerivative_translation_le_two
    (hBV : RoughCompactBVTranslationPrinciple)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    (∫ v in (0 : ℝ)..5,
      |roughSaiasDickmanDerivative (a - v) -
        roughSaiasDickmanDerivative (b - v)|) ≤
      2 * |a - b| := by
  exact hBV roughSaiasDickmanDerivative
    roughSaiasDickmanDerivative_eVariationOn_le_two ha hb

/-- The finite `G_y` normal form is explicitly `3`-Lipschitz on `0 <= u <= 5`
once the standard compact BV translation principle is supplied. -/
theorem roughSaiasG_lipschitz_three
    (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |roughSaiasG y a - roughSaiasG y b| ≤ 3 * |a - b| := by
  let Fa : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (a - v) *
      roughSaiasFractionalWeight y v
  let Fb : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (b - v) *
      roughSaiasFractionalWeight y v
  let qa : ℝ → ℝ := fun v => roughSaiasDickmanDerivative (a - v)
  let qb : ℝ → ℝ := fun v => roughSaiasDickmanDerivative (b - v)
  have hFa : IntervalIntegrable Fa volume 0 5 := by
    simpa only [Fa] using
      roughSaiasIntegrand_intervalIntegrable hy2 ha.2
  have hFb : IntervalIntegrable Fb volume 0 5 := by
    simpa only [Fb] using
      roughSaiasIntegrand_intervalIntegrable hy2 hb.2
  have hqa : IntervalIntegrable qa volume 0 5 := by
    simpa only [qa] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable ha.2
  have hqb : IntervalIntegrable qb volume 0 5 := by
    simpa only [qb] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable hb.2
  have hdiff :
      (∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v =
        ∫ v in (0 : ℝ)..5, Fa v - Fb v := by
    exact (intervalIntegral.integral_sub hFa hFb).symm
  have hintegral :
      |(∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v| ≤
        ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
    rw [hdiff]
    calc
      |(∫ v in (0 : ℝ)..5, Fa v - Fb v)| ≤
          ∫ v in (0 : ℝ)..5, |Fa v - Fb v| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hFa.sub hFb).abs (hqa.sub hqb).abs
        intro v hv
        have hweight := roughSaiasFractionalWeight_mem_unitInterval
          (y := y) (by omega) hv.1
        change
          |qa v * roughSaiasFractionalWeight y v -
              qb v * roughSaiasFractionalWeight y v| ≤
            |qa v - qb v|
        rw [← sub_mul, abs_mul, abs_of_nonneg hweight.1]
        exact mul_le_of_le_one_right (abs_nonneg (qa v - qb v)) hweight.2
  have htranslate :
      (∫ v in (0 : ℝ)..5, |qa v - qb v|) ≤ 2 * |a - b| := by
    simpa only [qa, qb] using
      roughSaiasDickmanDerivative_translation_le_two hBV ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  change
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
      (rho b - ∫ v in (0 : ℝ)..5, Fb v)| ≤ 3 * |a - b|
  calc
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
        (rho b - ∫ v in (0 : ℝ)..5, Fb v)| =
      |(rho a - rho b) -
        ((∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v)| := by
        congr 1
        ring
    _ ≤ |rho a - rho b| +
        |(∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v| := abs_sub _ _
    _ ≤ |a - b| + ∫ v in (0 : ℝ)..5, |qa v - qb v| :=
      add_le_add hrho hintegral
    _ ≤ |a - b| + 2 * |a - b| := add_le_add_right htranslate _
    _ = 3 * |a - b| := by ring

/-- The literal moving-endpoint `G_y` from the paper has the same explicit
Lipschitz constant. -/
theorem roughSaiasGMoving_lipschitz_three
    (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |roughSaiasGMoving y a - roughSaiasGMoving y b| ≤
      3 * |a - b| := by
  rw [← roughSaiasG_eq_moving hy2 ha.2,
    ← roughSaiasG_eq_moving hy2 hb.2]
  exact roughSaiasG_lipschitz_three hBV hy2 ha hb

/-! ## The explicit `1 / log y` normalization correction -/

theorem roughSaiasFractionalWeight_le_rpow_neg
    {y : ℕ} (hy : 0 < y) {v : ℝ} :
    roughSaiasFractionalWeight y v ≤ (y : ℝ) ^ (-v) := by
  have hpow : 0 ≤ (y : ℝ) ^ (-v) :=
    Real.rpow_nonneg (by positivity) _
  have hfractLe : Int.fract ((y : ℝ) ^ v) ≤ 1 :=
    (Int.fract_lt_one _).le
  unfold roughSaiasFractionalWeight
  exact mul_le_of_le_one_left hpow hfractLe

/-- Exact elementary integral of the exponential envelope for the
fractional Saias weight. -/
theorem roughSaias_integral_rpow_neg
    {y : ℕ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) =
      (1 - (y : ℝ) ^ (-(5 : ℝ))) / Real.log (y : ℝ) := by
  have hypos : (0 : ℝ) < (y : ℝ) := by positivity
  have hlogpos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  have hc : -Real.log (y : ℝ) ≠ 0 := by linarith
  have hpointwise : ∀ v : ℝ,
      (y : ℝ) ^ (-v) =
        Real.exp ((-Real.log (y : ℝ)) * v) := by
    intro v
    rw [Real.rpow_def_of_pos hypos]
    congr 1
    ring
  have hexpFive :
      Real.exp ((-Real.log (y : ℝ)) * 5) =
        (y : ℝ) ^ (-(5 : ℝ)) := by
    rw [Real.rpow_def_of_pos hypos]
    congr 1
    ring
  calc
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) =
        ∫ v in (0 : ℝ)..5,
          Real.exp ((-Real.log (y : ℝ)) * v) := by
      apply intervalIntegral.integral_congr
      intro v _hv
      exact hpointwise v
    _ = (-Real.log (y : ℝ))⁻¹ *
        (Real.exp ((-Real.log (y : ℝ)) * 5) - 1) := by
      rw [intervalIntegral.integral_comp_mul_left
        (f := Real.exp) (a := (0 : ℝ)) (b := (5 : ℝ)) hc]
      simp only [integral_exp, smul_eq_mul, mul_zero, Real.exp_zero]
    _ = (1 - (y : ℝ) ^ (-(5 : ℝ))) /
        Real.log (y : ℝ) := by
      rw [hexpFive]
      field_simp [hlogpos.ne']
      ring

theorem roughSaias_integral_rpow_neg_le_inv_log
    {y : ℕ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5, (y : ℝ) ^ (-v)) ≤
      1 / Real.log (y : ℝ) := by
  have hlogpos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  rw [roughSaias_integral_rpow_neg hy]
  apply div_le_div_of_nonneg_right _ hlogpos.le
  have hpow : 0 ≤ (y : ℝ) ^ (-(5 : ℝ)) :=
    Real.rpow_nonneg (by positivity) _
  linarith

/-- On the five-face compact range, the entire difference between `G_y`
and `rho` is at most `1 / log y`. -/
theorem roughSaiasG_sub_rho_abs_le_inv_log
    {y : ℕ} (hy2 : 2 ≤ y) {u : ℝ} (hu5 : u ≤ 5) :
    |roughSaiasG y u - rho u| ≤ 1 / Real.log (y : ℝ) := by
  let f : ℝ → ℝ := fun v =>
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFractionalWeight y v
  let e : ℝ → ℝ := fun v => (y : ℝ) ^ (-v)
  have hf : IntervalIntegrable f volume 0 5 := by
    simpa only [f] using
      roughSaiasIntegrand_intervalIntegrable hy2 hu5
  have he : IntervalIntegrable e volume 0 5 := by
    have hpow : Continuous (fun v : ℝ => (y : ℝ) ^ v) :=
      continuous_roughSaiasBaseRpow (by omega)
    exact (hpow.comp continuous_neg).intervalIntegrable 0 5
  have hmono :
      (∫ v in (0 : ℝ)..5, |f v|) ≤ ∫ v in (0 : ℝ)..5, e v := by
    apply intervalIntegral.integral_mono_on (by norm_num) hf.abs he
    intro v hv
    have hq := roughSaiasDickmanDerivative_abs_le_one
      (u := u - v) (by linarith [hv.1])
    have hw := roughSaiasFractionalWeight_mem_unitInterval
      (y := y) (by omega) hv.1
    change
      |roughSaiasDickmanDerivative (u - v) *
          roughSaiasFractionalWeight y v| ≤ e v
    rw [abs_mul, abs_of_nonneg hw.1]
    calc
      |roughSaiasDickmanDerivative (u - v)| *
          roughSaiasFractionalWeight y v ≤
        1 * roughSaiasFractionalWeight y v :=
          mul_le_mul_of_nonneg_right hq hw.1
      _ = roughSaiasFractionalWeight y v := one_mul _
      _ ≤ e v := roughSaiasFractionalWeight_le_rpow_neg
        (y := y) (by omega)
  have habs : |(∫ v in (0 : ℝ)..5, f v)| ≤
      ∫ v in (0 : ℝ)..5, e v := by
    exact (intervalIntegral.abs_integral_le_integral_abs
      (f := f) (by norm_num)).trans hmono
  have henv := roughSaias_integral_rpow_neg_le_inv_log
    (y := y) (by omega)
  have hrewrite : roughSaiasG y u - rho u =
      -(∫ v in (0 : ℝ)..5, f v) := by
    unfold roughSaiasG
    change
      (rho u - ∫ v in (0 : ℝ)..5, f v) - rho u =
        -(∫ v in (0 : ℝ)..5, f v)
    ring
  rw [hrewrite, abs_neg]
  exact habs.trans henv

/-- Since `G_y` is `3`-Lipschitz and `rho` is `1`-Lipschitz, their
difference is explicitly `4`-Lipschitz. -/
theorem roughSaiasG_sub_rho_lipschitz_four
    (hBV : RoughCompactBVTranslationPrinciple)
    {y : ℕ} (hy2 : 2 ≤ y)
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 5)
    (hb : b ∈ Icc (0 : ℝ) 5) :
    |(roughSaiasG y a - rho a) - (roughSaiasG y b - rho b)| ≤
      4 * |a - b| := by
  have hG := roughSaiasG_lipschitz_three hBV hy2 ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  calc
    |(roughSaiasG y a - rho a) - (roughSaiasG y b - rho b)| =
        |(roughSaiasG y a - roughSaiasG y b) - (rho a - rho b)| := by
      congr 1
      ring
    _ ≤ |roughSaiasG y a - roughSaiasG y b| + |rho a - rho b| :=
      abs_sub _ _
    _ ≤ 3 * |a - b| + |a - b| := add_le_add hG hrho
    _ = 4 * |a - b| := by ring

/-! ## Exact connection to the genuine friable residual -/

/-- The Saias normal-form main term at a natural endpoint. -/
noncomputable def roughSaiasNaturalMain (X y : ℕ) : ℝ :=
  (X : ℝ) * roughSaiasG y (FriableAsymptotic.dickmanU X y)

/-- The actual finite endpoint error `Psi - Lambda_normalForm`.  This is a
definition of a genuine number, not an assumed error function. -/
noncomputable def roughSaiasEndpointError (X y : ℕ) : ℝ :=
  (FriableAsymptotic.friableCount X y : ℝ) -
    roughSaiasNaturalMain X y

/-- The deterministic correction from the Saias normal form back to the
plain Dickman main term. -/
noncomputable def roughSaiasDickmanCorrection (X y : ℕ) : ℝ :=
  (X : ℝ) *
    (roughSaiasG y (FriableAsymptotic.dickmanU X y) -
      rho (FriableAsymptotic.dickmanU X y))

theorem roughSaiasNaturalMain_eq_lambdaNormalForm (X y : ℕ) :
    roughSaiasNaturalMain X y =
      roughSaiasLambdaNormalForm (X : ℝ) y := by
  rw [roughSaiasLambdaNormalForm_nat]
  rfl

@[simp]
theorem roughSaiasEndpointError_initial
    {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughSaiasEndpointError X y = 0 := by
  unfold roughSaiasEndpointError
  rw [roughSaiasNaturalMain_eq_lambdaNormalForm,
    roughSaiasLambdaNormalForm_eq_friableCount_initial hX hy hXy]
  ring

/-- Exact decomposition of the already-defined genuine residual. -/
theorem roughFriableResidual_eq_saiasError_add_correction (X y : ℕ) :
    roughFriableResidual X y =
      roughSaiasEndpointError X y + roughSaiasDickmanCorrection X y := by
  unfold roughFriableResidual roughFriableDickmanMain
    roughSaiasEndpointError roughSaiasNaturalMain
    roughSaiasDickmanCorrection
  ring

/-- The normal-form correction has the desired short-gap scale, with the
explicit constant five.  Thus any remaining loss in the residual increment
comes only from the genuine endpoint errors `Psi - Lambda_normalForm`. -/
theorem roughSaiasDickmanCorrection_difference_abs_le
    (hBV : RoughCompactBVTranslationPrinciple)
    {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hy2 : 2 ≤ y)
    (hB5 : FriableAsymptotic.dickmanU B y ≤ 5) :
    |roughSaiasDickmanCorrection B y -
        roughSaiasDickmanCorrection A y| ≤
      5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
  let a : ℝ := FriableAsymptotic.dickmanU A y
  let b : ℝ := FriableAsymptotic.dickmanU B y
  let H : ℝ → ℝ := fun u => roughSaiasG y u - rho u
  have hB : 0 < B := hA.trans_le hAB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogAB : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
    Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hAB)
  have hab : a ≤ b := by
    dsimp [a, b, FriableAsymptotic.dickmanU]
    exact div_le_div_of_nonneg_right hlogAB hlogy.le
  have ha0 : 0 ≤ a := by
    dsimp [a, FriableAsymptotic.dickmanU]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ A by omega))) hlogy.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5 : b ≤ 5 := by simpa only [b] using hB5
  have ha5 : a ≤ 5 := hab.trans hb5
  have hHbound : |H b| ≤ 1 / Real.log (y : ℝ) := by
    simpa only [H] using
      roughSaiasG_sub_rho_abs_le_inv_log hy2 hb5
  have hHlip : |H b - H a| ≤ 4 * (b - a) := by
    have h := roughSaiasG_sub_rho_lipschitz_four hBV hy2
      (show b ∈ Icc (0 : ℝ) 5 from ⟨hb0, hb5⟩)
      (show a ∈ Icc (0 : ℝ) 5 from ⟨ha0, ha5⟩)
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
    simpa only [H] using h
  have hlogQuotient :
      Real.log (B : ℝ) - Real.log (A : ℝ) ≤
        (B : ℝ) / (A : ℝ) - 1 := by
    have hBcast : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
    have hAcast : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have h := Real.log_le_sub_one_of_pos
      (div_pos hBcast hAcast)
    rw [Real.log_div hBcast.ne' hAcast.ne'] at h
    exact h
  have hscaled :
      (A : ℝ) * (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
        (B : ℝ) - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogQuotient
      (by positivity : (0 : ℝ) ≤ (A : ℝ))
    calc
      (A : ℝ) * (Real.log (B : ℝ) - Real.log (A : ℝ)) ≤
          (A : ℝ) * ((B : ℝ) / (A : ℝ) - 1) := h
      _ = (B : ℝ) - (A : ℝ) := by field_simp
  have hcoordinate :
      (A : ℝ) * (b - a) ≤
        ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogy.le
    rw [Nat.cast_sub hAB]
    dsimp [a, b, FriableAsymptotic.dickmanU]
    convert hdiv using 1
    ring
  have hsecond :
      (A : ℝ) * (4 * (b - a)) ≤
        4 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
    calc
      (A : ℝ) * (4 * (b - a)) = 4 * ((A : ℝ) * (b - a)) := by
        ring
      _ ≤ 4 * (((B - A : ℕ) : ℝ) / Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoordinate (by norm_num)
      _ = 4 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
        ring
  have hgapNonneg : 0 ≤ ((B - A : ℕ) : ℝ) := by positivity
  have hAcastNonneg : 0 ≤ (A : ℝ) := by positivity
  unfold roughSaiasDickmanCorrection
  change |(B : ℝ) * H b - (A : ℝ) * H a| ≤
    5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ)
  have hexpand :
      (B : ℝ) * H b - (A : ℝ) * H a =
        ((B - A : ℕ) : ℝ) * H b + (A : ℝ) * (H b - H a) := by
    rw [Nat.cast_sub hAB]
    ring
  rw [hexpand]
  calc
    |((B - A : ℕ) : ℝ) * H b + (A : ℝ) * (H b - H a)| ≤
        |((B - A : ℕ) : ℝ) * H b| +
          |(A : ℝ) * (H b - H a)| := abs_add_le _ _
    _ = ((B - A : ℕ) : ℝ) * |H b| +
        (A : ℝ) * |H b - H a| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hgapNonneg,
        abs_of_nonneg hAcastNonneg]
    _ ≤ ((B - A : ℕ) : ℝ) *
          (1 / Real.log (y : ℝ)) +
        (A : ℝ) * (4 * (b - a)) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hHbound hgapNonneg)
        (mul_le_mul_of_nonneg_left hHlip hAcastNonneg)
    _ ≤ ((B - A : ℕ) : ℝ) *
          (1 / Real.log (y : ℝ)) +
        4 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
      add_le_add_right hsecond _
    _ = 5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
      ring

/-- Exact finite-difference decomposition of the genuine friable residual. -/
theorem roughFriableResidual_difference_eq_saias
    (A B y : ℕ) :
    roughFriableResidual B y - roughFriableResidual A y =
      (roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y) := by
  rw [roughFriableResidual_eq_saiasError_add_correction,
    roughFriableResidual_eq_saiasError_add_correction]
  ring

/-- Therefore the common-prime transition ledger is exactly the sum of a
`Psi - Lambda_normalForm` error increment and the explicit deterministic
normalization correction. -/
theorem roughFriablePrimeTransitionLedger_eq_saias
    {A B y : ℕ} (hyB : y ≤ B) (hAB : A ≤ B) :
    roughFriablePrimeTransitionLedger A B y =
      |(roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y)| := by
  rw [roughFriablePrimeTransitionLedger_eq_residualDifference hyB hAB,
    roughFriableResidual_difference_eq_saias]

/-- Finite endpoint-error envelope having exactly the shape obtained from
the published Hildebrand--Tenenbaum--Saias theorem on `u <= 5`.  This is a
named proposition, not a new axiom; the cited theorem must ultimately be
proved before this proposition can be instantiated in a closed proof. -/
def RoughSaiasEndpointApproximationUpToFive
    (eta : ℕ → ℝ) (Y₀ : ℕ) : Prop :=
  ∀ {X y : ℕ}, Y₀ ≤ y → 2 ≤ y → 0 < X →
    Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
    |roughSaiasEndpointError X y| ≤ eta y * (X : ℝ)

/-- What an endpoint-shaped HT--Saias approximation actually yields for the
prime-transition ledger.  The deterministic normalization has the desired
gap scale, but the two endpoint errors contribute `eta(y) * (A+B)`.

This theorem is the formal connection to
`RoughFriablePrimeTransitionEstimateUpToFive`: it also records why the cited
endpoint theorem alone does not instantiate that local transition estimate
for arbitrary near-diagonal natural endpoints. -/
theorem roughFriablePrimeTransitionLedger_le_of_saiasEndpointApproximation
    (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y) (hyB : y ≤ B)
    (hA : 0 < A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    roughFriablePrimeTransitionLedger A B y ≤
      eta y * ((A : ℝ) + (B : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
  have hB : 0 < B := hA.trans_le hAB
  have hlogA : Real.log (A : ℝ) ≤
      5 * Real.log (y : ℝ) := by
    have hABlog : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log (by exact_mod_cast hA) (by exact_mod_cast hAB)
    exact hABlog.trans hlogB
  have herrorA : |roughSaiasEndpointError A y| ≤ eta y * (A : ℝ) :=
    happrox hY hy2 hA hlogA
  have herrorB : |roughSaiasEndpointError B y| ≤ eta y * (B : ℝ) :=
    happrox hY hy2 hB hlogB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hB5 : FriableAsymptotic.dickmanU B y ≤ 5 := by
    dsimp [FriableAsymptotic.dickmanU]
    apply (div_le_iff₀ hlogy).2
    simpa [mul_comm] using hlogB
  have hcorrection := roughSaiasDickmanCorrection_difference_abs_le
    hBV hA hAB hy2 hB5
  rw [roughFriablePrimeTransitionLedger_eq_saias hyB hAB]
  calc
    |(roughSaiasEndpointError B y - roughSaiasEndpointError A y) +
        (roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y)| ≤
      |roughSaiasEndpointError B y - roughSaiasEndpointError A y| +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := abs_add_le _ _
    _ ≤ (|roughSaiasEndpointError B y| +
          |roughSaiasEndpointError A y|) +
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y| := by
      exact add_le_add_left
        (abs_sub (roughSaiasEndpointError B y)
          (roughSaiasEndpointError A y))
        |roughSaiasDickmanCorrection B y -
          roughSaiasDickmanCorrection A y|
    _ ≤ (eta y * (B : ℝ) + eta y * (A : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
      add_le_add (add_le_add herrorB herrorA) hcorrection
    _ = eta y * ((A : ℝ) + (B : ℝ)) +
        5 * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
      ring

end

end Erdos390.WholePaper
