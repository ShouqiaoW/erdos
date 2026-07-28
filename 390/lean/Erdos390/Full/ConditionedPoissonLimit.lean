import Erdos390.Full.DickmanBasic
import Erdos390.Full.ConditionedPoisson

/-!
# Exact analytic identities for the Poisson--Dickman bridge

This file continues the explicit finite-cutoff construction in
`ConditionedPoisson`.  The first layer below isolates the identities which
are needed by the covariance operator and proves them directly from the
method-of-steps Dickman equation.  In particular, the fact that the scale
function `t` is a null direction is not postulated.

The probability-theoretic exact-total projective limit is kept separate from
these analytic identities: this prevents a choice of a regular conditional
law on a null fibre from silently entering the operator calculation.
-/

open Filter Set
open scoped Interval BigOperators ENNReal NNReal

noncomputable section

namespace Erdos390.Full.ConditionedPoissonLimit

open MeasureTheory ProbabilityTheory Real
open DickmanBasic

/-! ## A global method-of-steps Dickman function -/

/-- Later stages of the method of steps agree with every earlier stage on
the interval already constructed. -/
lemma rhoApprox_eq_of_le {m n : ℕ} (hmn : m ≤ n) {x : ℝ}
    (hx : x ≤ (m : ℝ) + 1) : rhoApprox n x = rhoApprox m x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  induction k with
  | zero => simp
  | succ k ih =>
      rw [show m + (k + 1) = (m + k) + 1 by omega,
        rhoApprox_succ_eq_prev]
      · exact ih (Nat.le_add_right m k)
      · have hmk : (m : ℝ) ≤ (m + k : ℕ) := by
          exact_mod_cast Nat.le_add_right m k
        linarith

/-- The genuine global method-of-steps solution: at `x` use the first stage
whose constructed interval has reached `x`. -/
def rhoGlobal (x : ℝ) : ℝ := rhoApprox ⌈x⌉₊ x

lemma rhoGlobal_eq_rhoApprox_of_le_nat (n : ℕ) {x : ℝ} (hx : x ≤ n) :
    rhoGlobal x = rhoApprox n x := by
  have hceil : ⌈x⌉₊ ≤ n := Nat.ceil_le.mpr hx
  unfold rhoGlobal
  symm
  apply rhoApprox_eq_of_le hceil
  have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  linarith

lemma rhoGlobal_eq_one_of_le_one {x : ℝ} (hx : x ≤ 1) : rhoGlobal x = 1 := by
  rw [rhoGlobal_eq_rhoApprox_of_le_nat 1 (by norm_num at hx ⊢; exact hx)]
  simp [rhoApprox, hx]

@[simp] lemma rhoGlobal_zero : rhoGlobal 0 = 1 :=
  rhoGlobal_eq_one_of_le_one (by norm_num)

/-- On every bounded interval `rhoGlobal` is literally one fixed finite
approximant.  This proves global continuity without gluing by fiat. -/
lemma continuous_rhoGlobal : Continuous rhoGlobal := by
  rw [continuous_iff_continuousAt]
  intro x
  let n : ℕ := ⌈x⌉₊ + 1
  have hxn : x < (n : ℝ) := by
    have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    dsimp [n]
    push_cast
    linarith
  have heq : rhoGlobal =ᶠ[nhds x] rhoApprox n := by
    filter_upwards [Iio_mem_nhds hxn] with z hz
    apply rhoGlobal_eq_rhoApprox_of_le_nat n
    exact hz.le
  exact (continuous_rhoApprox n).continuousAt.congr_of_eventuallyEq heq

/-- The global object agrees with the already audited finite object throughout
the range used by the covariance kernel. -/
lemma rhoGlobal_eq_rho {x : ℝ} (hx : x ≤ 5) : rhoGlobal x = rho x := by
  exact rhoGlobal_eq_rhoApprox_of_le_nat 5 hx

/-- Global delay differential equation. -/
lemma hasDerivAt_rhoGlobal {x : ℝ} (hx : 1 < x) :
    HasDerivAt rhoGlobal (-rhoGlobal (x - 1) / x) x := by
  let n : ℕ := ⌈x⌉₊
  have hxn : x ≤ (n : ℝ) := by exact Nat.le_ceil x
  have heq : rhoGlobal =ᶠ[nhds x] rhoApprox (n + 1) := by
    have hxlt : x < ((n + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    filter_upwards [Iio_mem_nhds hxlt] with z hz
    apply rhoGlobal_eq_rhoApprox_of_le_nat (n + 1)
    exact hz.le
  have hprev : rhoGlobal (x - 1) = rhoApprox n (x - 1) := by
    apply rhoGlobal_eq_rhoApprox_of_le_nat n
    linarith
  have hfinite := hasDerivAt_rhoApprox_succ n hx
  rw [hprev]
  exact hfinite.congr_of_eventuallyEq heq

lemma deriv_rhoGlobal {x : ℝ} (hx : 1 < x) :
    deriv rhoGlobal x = -rhoGlobal (x - 1) / x :=
  (hasDerivAt_rhoGlobal hx).deriv

lemma delay_equation_rhoGlobal {x : ℝ} (hx : 1 < x) :
    x * deriv rhoGlobal x + rhoGlobal (x - 1) = 0 := by
  rw [deriv_rhoGlobal hx]
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  field_simp
  ring

/-- Global integral form of the delay equation. -/
lemma rhoGlobal_integral_eq {x : ℝ} (hx : 1 ≤ x) :
    rhoGlobal x = 1 - ∫ t in (1 : ℝ)..x, rhoGlobal (t - 1) / t := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [rhoGlobal_eq_one_of_le_one]
  · let n : ℕ := ⌈x⌉₊
    have hnpos : 0 < n := Nat.ceil_pos.mpr (zero_lt_one.trans hx)
    let m : ℕ := n - 1
    have hnm : n = m + 1 := by
      dsimp [m]
      omega
    have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
    rw [rhoGlobal_eq_rhoApprox_of_le_nat n hxn, hnm,
      rhoApprox_succ_of_one_lt m hx]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    have htmem : t ∈ Icc (1 : ℝ) x := by
      simpa [uIcc_of_le hx.le] using ht
    have htm : t - 1 ≤ (m : ℝ) := by
      have hncast : (n : ℝ) = (m : ℝ) + 1 := by
        exact_mod_cast hnm
      linarith [htmem.2, hxn]
    have hfull := rhoGlobal_eq_rhoApprox_of_le_nat m htm
    change rhoApprox m (t - 1) / safeDenom t = rhoGlobal (t - 1) / t
    rw [safeDenom_eq_self htmem.1]
    exact congrArg (fun z : ℝ => z / t) hfull.symm

lemma integral_rhoGlobal_zero_one :
    (∫ t in (0 : ℝ)..1, rhoGlobal t) = 1 := by
  calc
    (∫ t in (0 : ℝ)..1, rhoGlobal t) =
        ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          apply rhoGlobal_eq_one_of_le_one
          have ht' : t ∈ Icc (0 : ℝ) 1 := by
            simpa [uIcc_of_le zero_le_one] using ht
          exact ht'.2
    _ = 1 := by simp

/-- Global positive averaging identity. -/
lemma rhoGlobal_average_eq {x : ℝ} (hx : 1 ≤ x) :
    x * rhoGlobal x = ∫ t in (x - 1)..x, rhoGlobal t := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [rhoGlobal_eq_one_of_le_one, integral_rhoGlobal_zero_one]
  · have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
        HasDerivWithinAt (fun u : ℝ => u * rhoGlobal u)
          (rhoGlobal t - rhoGlobal (t - 1)) (Ioi t) t := by
      intro t ht
      have h := (hasDerivAt_id t).mul (hasDerivAt_rhoGlobal ht.1)
      have ht0 : t ≠ 0 := ne_of_gt (zero_lt_one.trans ht.1)
      have heq : 1 * rhoGlobal t + t * (-rhoGlobal (t - 1) / t) =
          rhoGlobal t - rhoGlobal (t - 1) := by
        field_simp
        ring
      exact (h.congr_deriv heq).hasDerivWithinAt
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
      hx.le
      ((continuous_id.mul continuous_rhoGlobal).continuousOn)
      hderiv
      ((continuous_rhoGlobal.sub
        (continuous_rhoGlobal.comp
          (continuous_id.sub continuous_const))).intervalIntegrable 1 x)
    have hshift : (∫ t in (1 : ℝ)..x, rhoGlobal (t - 1)) =
        ∫ t in (0 : ℝ)..(x - 1), rhoGlobal t := by
      convert intervalIntegral.integral_comp_sub_right
        (a := (1 : ℝ)) (b := x) rhoGlobal 1 using 1
      norm_num
    have hsub : (∫ t in (1 : ℝ)..x, rhoGlobal t - rhoGlobal (t - 1)) =
        (∫ t in (1 : ℝ)..x, rhoGlobal t) -
          ∫ t in (1 : ℝ)..x, rhoGlobal (t - 1) := by
      apply intervalIntegral.integral_sub
      · exact continuous_rhoGlobal.intervalIntegrable 1 x
      · exact (continuous_rhoGlobal.comp
          (continuous_id.sub continuous_const)).intervalIntegrable 1 x
    have hadd₁ := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      (continuous_rhoGlobal.intervalIntegrable (0 : ℝ) 1)
      (continuous_rhoGlobal.intervalIntegrable (1 : ℝ) x)
    have hadd₂ := intervalIntegral.integral_add_adjacent_intervals
      (μ := volume)
      (continuous_rhoGlobal.intervalIntegrable (0 : ℝ) (x - 1))
      (continuous_rhoGlobal.intervalIntegrable (x - 1) x)
    rw [hsub, hshift] at hFTC
    rw [integral_rhoGlobal_zero_one] at hadd₁
    have hrho1 : rhoGlobal (1 : ℝ) = 1 :=
      rhoGlobal_eq_one_of_le_one le_rfl
    rw [hrho1] at hFTC
    norm_num at hFTC
    linarith

private lemma rhoGlobal_pos_step {a : ℝ} (ha1 : 1 ≤ a)
    (hprev : ∀ x ∈ Icc (a - 1) a, 0 < rhoGlobal x) :
    ∀ x ∈ Icc a (a + 1), 0 < rhoGlobal x := by
  have hanti : AntitoneOn rhoGlobal (Icc a (a + 1)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a (a + 1))
      continuous_rhoGlobal.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      exact (hasDerivAt_rhoGlobal (by linarith [hx.1, ha1])).differentiableAt
        |>.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hshift : x - 1 ∈ Icc (a - 1) a := by
        constructor <;> linarith [hx.1, hx.2]
      have hpos := hprev (x - 1) hshift
      rw [deriv_rhoGlobal (by linarith [hx.1, ha1])]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpos.le)
        (by linarith [hx.1, ha1])
  have hend_le (x : ℝ) (hx : x ∈ Icc a (a + 1)) :
      rhoGlobal (a + 1) ≤ rhoGlobal x :=
    hanti hx (right_mem_Icc.mpr (by linarith)) hx.2
  have hIntegralLower :
      rhoGlobal (a + 1) ≤ ∫ t in a..(a + 1), rhoGlobal t := by
    have hmono := intervalIntegral.integral_mono_on (μ := volume)
      (show a ≤ a + 1 by linarith)
      (continuous_const.intervalIntegrable a (a + 1))
      (continuous_rhoGlobal.intervalIntegrable a (a + 1))
      (fun x hx => hend_le x hx)
    simpa using hmono
  have hAverage :
      (a + 1) * rhoGlobal (a + 1) = ∫ t in a..(a + 1), rhoGlobal t := by
    have h := rhoGlobal_average_eq (x := a + 1) (by linarith)
    rw [show a + 1 - 1 = a by ring] at h
    exact h
  have hend_nonneg : 0 ≤ rhoGlobal (a + 1) := by nlinarith
  have hnonneg (x : ℝ) (hx : x ∈ Icc a (a + 1)) : 0 ≤ rhoGlobal x :=
    hend_nonneg.trans (hend_le x hx)
  have hIntegralPos : 0 < ∫ t in a..(a + 1), rhoGlobal t := by
    apply intervalIntegral.integral_pos (by linarith)
      continuous_rhoGlobal.continuousOn
    · intro x hx
      exact hnonneg x ⟨hx.1.le, hx.2⟩
    · refine ⟨a, left_mem_Icc.mpr (by linarith), ?_⟩
      exact hprev a ⟨by linarith, le_rfl⟩
  have hend_pos : 0 < rhoGlobal (a + 1) := by nlinarith
  intro x hx
  exact hend_pos.trans_le (hend_le x hx)

/-- Global strict positivity, established one unit interval at a time. -/
lemma rhoGlobal_pos {x : ℝ} (hx : 0 ≤ x) : 0 < rhoGlobal x := by
  have hnat : ∀ n : ℕ, ∀ z ∈ Icc (0 : ℝ) n, 0 < rhoGlobal z := by
    intro n
    induction n with
    | zero =>
        intro z hz
        have hzle : z ≤ 0 := by simpa using hz.2
        have hz0 : z = 0 := le_antisymm hzle hz.1
        simp [hz0]
    | succ n ih =>
        intro z hz
        by_cases hn0 : n = 0
        · subst n
          rw [rhoGlobal_eq_one_of_le_one]
          · norm_num
          · norm_num at hz ⊢
            exact hz.2
        · by_cases hzn : z ≤ (n : ℝ)
          · exact ih z ⟨hz.1, hzn⟩
          · have hn1 : (1 : ℝ) ≤ n := by
              exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn0)
            have hprev : ∀ w ∈ Icc ((n : ℝ) - 1) n,
                0 < rhoGlobal w := by
              intro w hw
              exact ih w ⟨by linarith [hw.1, hn1], hw.2⟩
            have hstep := rhoGlobal_pos_step hn1 hprev
            apply hstep z
            constructor
            · exact le_of_not_ge hzn
            · norm_num [Nat.cast_add, Nat.cast_one] at hz ⊢
              exact hz.2
  let n : ℕ := ⌈x⌉₊
  apply hnat n x
  exact ⟨hx, Nat.le_ceil x⟩

/-- Beyond the constant initial interval, the global Dickman function is
strictly decreasing. -/
lemma strictAntiOn_rhoGlobal_Ici_one :
    StrictAntiOn rhoGlobal (Ici (1 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (1 : ℝ))
    continuous_rhoGlobal.continuousOn
  intro x hx
  have hx' : 1 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
  rw [deriv_rhoGlobal hx']
  have hnum : 0 < rhoGlobal (x - 1) := rhoGlobal_pos (sub_nonneg.mpr hx'.le)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) (zero_lt_one.trans hx')

lemma rhoGlobal_le_one (x : ℝ) : rhoGlobal x ≤ 1 := by
  by_cases hx1 : x ≤ 1
  · rw [rhoGlobal_eq_one_of_le_one hx1]
  · have h1mem : (1 : ℝ) ∈ Ici (1 : ℝ) := by simp
    have hxmem : x ∈ Ici (1 : ℝ) := by simpa using (le_of_lt (lt_of_not_ge hx1))
    have hlt := strictAntiOn_rhoGlobal_Ici_one h1mem hxmem (lt_of_not_ge hx1)
    rw [rhoGlobal_eq_one_of_le_one le_rfl] at hlt
    exact hlt.le

/-- The classical Dickman density, with its support convention made
explicit. -/
def dickmanDensity (x : ℝ) : ℝ :=
  if 0 ≤ x then exp (-Real.eulerMascheroniConstant) * rhoGlobal x else 0

lemma measurable_dickmanDensity : Measurable dickmanDensity := by
  unfold dickmanDensity
  apply Measurable.ite measurableSet_Ici
  · exact measurable_const.mul continuous_rhoGlobal.measurable
  · exact measurable_const

lemma dickmanDensity_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    dickmanDensity x = exp (-Real.eulerMascheroniConstant) * rhoGlobal x := by
  simp [dickmanDensity, hx]

lemma dickmanDensity_of_neg {x : ℝ} (hx : x < 0) : dickmanDensity x = 0 := by
  simp [dickmanDensity, not_le.mpr hx]

lemma dickmanDensity_pos {x : ℝ} (hx : 0 ≤ x) : 0 < dickmanDensity x := by
  rw [dickmanDensity_of_nonneg hx]
  exact mul_pos (exp_pos _) (rhoGlobal_pos hx)

lemma dickmanDensity_U_pos : 0 < dickmanDensity U := by
  apply dickmanDensity_pos
  norm_num [U]

lemma dickmanDensity_U_ne_zero : dickmanDensity U ≠ 0 :=
  ne_of_gt dickmanDensity_U_pos

/-- Scaling law for the total of the atoms below a cutoff `eps`. -/
def scaledDickmanDensity (eps v : ℝ) : ℝ :=
  dickmanDensity (v / eps) / eps

lemma scaledDickmanDensity_pos {eps v : ℝ} (heps : 0 < eps) (hv : 0 ≤ v) :
    0 < scaledDickmanDensity eps v := by
  unfold scaledDickmanDensity
  exact div_pos (dickmanDensity_pos (div_nonneg hv heps.le)) heps

/-- Infinitesimal cutoff consistency.  Moving the cutoff exposes one boundary
atom; this is the generator whose exponential is the finite-cutoff Janossy
convolution. -/
lemma hasDerivAt_rhoGlobal_div_cutoff {r eps : ℝ} (heps : 0 < eps)
    (hre : eps < r) :
    HasDerivAt (fun e : ℝ => rhoGlobal (r / e))
      (rhoGlobal (r / eps - 1) / eps) eps := by
  have heps0 : eps ≠ 0 := ne_of_gt heps
  have hr0 : r ≠ 0 := ne_of_gt (heps.trans hre)
  have hu : 1 < r / eps := (lt_div_iff₀ heps).mpr (by simpa using hre)
  have hinner : HasDerivAt (fun e : ℝ => r / e) (-r / eps ^ 2) eps := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_const eps r).mul (hasDerivAt_inv heps0)
  have hcomp := (hasDerivAt_rhoGlobal hu).comp eps hinner
  convert hcomp using 1
  field_simp [heps0, hr0]

/-- Integrated form of the cutoff generator on a compact positive cutoff
interval. -/
lemma rhoGlobal_cutoff_increment {r a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbr : b ≤ r) :
    rhoGlobal (r / b) - rhoGlobal (r / a) =
      ∫ e in a..b, rhoGlobal (r / e - 1) / e := by
  have hderiv : ∀ e ∈ Ioo a b,
      HasDerivAt (fun z : ℝ => rhoGlobal (r / z))
        (rhoGlobal (r / e - 1) / e) e := by
    intro e he
    apply hasDerivAt_rhoGlobal_div_cutoff
    · linarith [he.1, ha]
    · linarith [he.2, hbr]
  have hint : IntervalIntegrable (fun e : ℝ => rhoGlobal (r / e - 1) / e)
      volume a b := by
    have hcont : ContinuousOn (fun e : ℝ => rhoGlobal (r / e - 1) / e)
        (Icc a b) := by
      have hdiv : ContinuousOn (fun e : ℝ => r / e) (Icc a b) :=
        continuous_const.continuousOn.div continuous_id.continuousOn
          (fun e he => ne_of_gt (ha.trans_le he.1))
      have hnum : ContinuousOn (fun e : ℝ => rhoGlobal (r / e - 1))
          (Icc a b) :=
        continuous_rhoGlobal.comp_continuousOn (hdiv.sub continuous_const.continuousOn)
      exact hnum.div continuous_id.continuousOn
        (fun e he => ne_of_gt (ha.trans_le he.1))
    exact hcont.intervalIntegrable_of_Icc hab
  symm
  have hprimitive : ContinuousOn (fun e : ℝ => rhoGlobal (r / e)) (Icc a b) := by
    have hdiv : ContinuousOn (fun e : ℝ => r / e) (Icc a b) :=
      continuous_const.continuousOn.div continuous_id.continuousOn
        (fun e he => ne_of_gt (ha.trans_le he.1))
    exact continuous_rhoGlobal.comp_continuousOn hdiv
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hprimitive hderiv hint

/-- Density shape supported on nonnegative residual masses.  We retain the
right-continuous value at zero; changing that single value would not affect
the Janossy integrals, but this convention makes the renewal identity exact
at the moving boundary. -/
def positiveDickmanShape (x : ℝ) : ℝ :=
  if 0 ≤ x then rhoGlobal x else 0

lemma positiveDickmanShape_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    positiveDickmanShape x = rhoGlobal x := by
  simp [positiveDickmanShape, hx]

lemma positiveDickmanShape_of_neg {x : ℝ} (hx : x < 0) :
    positiveDickmanShape x = 0 := by
  simp [positiveDickmanShape, not_le.mpr hx]

lemma dickmanDensity_eq_exp_mul_positiveDickmanShape (x : ℝ) :
    dickmanDensity x =
      exp (-Real.eulerMascheroniConstant) * positiveDickmanShape x := by
  by_cases hx : 0 ≤ x
  · rw [dickmanDensity_of_nonneg hx, positiveDickmanShape_of_nonneg hx]
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [dickmanDensity_of_neg hxneg, positiveDickmanShape_of_neg hxneg, mul_zero]

/-- Full one-boundary-atom cutoff identity, including the case where the
moving cutoff passes the available residual mass. -/
lemma rhoGlobal_cutoff_increment_full {r a b : ℝ} (hr : 0 < r)
    (ha : 0 < a) (hab : a ≤ b) :
    rhoGlobal (r / b) - rhoGlobal (r / a) =
      ∫ e in a..b, positiveDickmanShape ((r - e) / e) / e := by
  have hb : 0 < b := ha.trans_le hab
  by_cases hbr : b ≤ r
  · have hbase := rhoGlobal_cutoff_increment ha hab hbr
    rw [hbase]
    apply intervalIntegral.integral_congr
    intro e he
    have hmem : e ∈ Icc a b := by simpa [uIcc_of_le hab] using he
    have hea : a ≤ e := hmem.1
    have heb : e ≤ b := hmem.2
    have he0 : 0 < e := ha.trans_le hea
    have herle : e ≤ r := heb.trans hbr
    have harg : r / e - 1 = (r - e) / e := by
      field_simp [ne_of_gt he0]
    have hshape := positiveDickmanShape_of_nonneg
      (div_nonneg (sub_nonneg.mpr herle) he0.le)
    change rhoGlobal (r / e - 1) / e = positiveDickmanShape ((r - e) / e) / e
    rw [hshape, ← harg]
  · have hrb : r < b := lt_of_not_ge hbr
    by_cases hra : r ≤ a
    · have hraDiv : r / a ≤ 1 := (div_le_one ha).mpr hra
      have hrbDiv : r / b ≤ 1 := (div_le_one hb).mpr hrb.le
      rw [rhoGlobal_eq_one_of_le_one hraDiv, rhoGlobal_eq_one_of_le_one hrbDiv]
      simp only [sub_self]
      symm
      calc
        (∫ e in a..b, positiveDickmanShape ((r - e) / e) / e) =
            ∫ _e in a..b, (0 : ℝ) := by
              apply intervalIntegral.integral_congr_ae
              filter_upwards with e he
              have hmem : e ∈ Ioc a b := by
                simpa [uIoc_of_le hab] using he
              have he0 : 0 < e := ha.trans hmem.1
              have hre : r < e := hra.trans_lt hmem.1
              rw [positiveDickmanShape_of_neg]
              · simp
              · exact div_neg_of_neg_of_pos (sub_neg.mpr hre) he0
        _ = 0 := by simp
    · have har : a < r := lt_of_not_ge hra
      have hleft := rhoGlobal_cutoff_increment ha har.le le_rfl
      have hrightZero :
          (∫ e in r..b, positiveDickmanShape ((r - e) / e) / e) = 0 := by
        calc
          (∫ e in r..b, positiveDickmanShape ((r - e) / e) / e) =
              ∫ _e in r..b, (0 : ℝ) := by
                apply intervalIntegral.integral_congr_ae
                filter_upwards with e he
                have hmem : e ∈ Ioc r b := by
                  simpa [uIoc_of_le hrb.le] using he
                have he0 : 0 < e := hr.trans hmem.1
                rw [positiveDickmanShape_of_neg]
                · simp
                · exact div_neg_of_neg_of_pos (sub_neg.mpr hmem.1) he0
          _ = 0 := by simp
      have hleftShape :
          (∫ e in a..r, positiveDickmanShape ((r - e) / e) / e) =
            ∫ e in a..r, rhoGlobal (r / e - 1) / e := by
        apply intervalIntegral.integral_congr
        intro e he
        have hmem : e ∈ Icc a r := by simpa [uIcc_of_le har.le] using he
        have he0 : 0 < e := ha.trans_le hmem.1
        have harg : r / e - 1 = (r - e) / e := by
          field_simp [ne_of_gt he0]
        have hshape := positiveDickmanShape_of_nonneg
          (div_nonneg (sub_nonneg.mpr hmem.2) he0.le)
        change positiveDickmanShape ((r - e) / e) / e = rhoGlobal (r / e - 1) / e
        rw [hshape, ← harg]
      have hleftInt : IntervalIntegrable
          (fun e : ℝ => positiveDickmanShape ((r - e) / e) / e) volume a r := by
        have hcont : ContinuousOn (fun e : ℝ => rhoGlobal (r / e - 1) / e)
            (Icc a r) := by
          have hdiv : ContinuousOn (fun e : ℝ => r / e) (Icc a r) :=
            continuous_const.continuousOn.div continuous_id.continuousOn
              (fun e he => ne_of_gt (ha.trans_le he.1))
          have hnum : ContinuousOn (fun e : ℝ => rhoGlobal (r / e - 1))
              (Icc a r) :=
            continuous_rhoGlobal.comp_continuousOn
              (hdiv.sub continuous_const.continuousOn)
          exact hnum.div continuous_id.continuousOn
            (fun e he => ne_of_gt (ha.trans_le he.1))
        have hbaseInt : IntervalIntegrable
            (fun e : ℝ => rhoGlobal (r / e - 1) / e) volume a r :=
          hcont.intervalIntegrable_of_Icc har.le
        apply hbaseInt.congr
        intro e he
        have hmem : e ∈ Icc a r := by
          simpa [uIcc_of_le har.le] using (uIoc_subset_uIcc he)
        have he0 : 0 < e := ha.trans_le hmem.1
        have harg : r / e - 1 = (r - e) / e := by
          field_simp [ne_of_gt he0]
        have hshape := positiveDickmanShape_of_nonneg
          (div_nonneg (sub_nonneg.mpr hmem.2) he0.le)
        change rhoGlobal (r / e - 1) / e = positiveDickmanShape ((r - e) / e) / e
        rw [hshape, ← harg]
      have hrightInt : IntervalIntegrable
          (fun e : ℝ => positiveDickmanShape ((r - e) / e) / e) volume r b := by
        have hzeroInt : IntervalIntegrable (fun _e : ℝ => (0 : ℝ)) volume r b :=
          continuous_zero.intervalIntegrable r b
        apply hzeroInt.congr
        intro e he
        have hmem : e ∈ Ioc r b := by simpa [uIoc_of_le hrb.le] using he
        have he0 : 0 < e := hr.trans hmem.1
        change (0 : ℝ) = positiveDickmanShape ((r - e) / e) / e
        rw [positiveDickmanShape_of_neg]
        · simp
        · exact div_neg_of_neg_of_pos (sub_neg.mpr hmem.1) he0
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (μ := volume)
        hleftInt hrightInt
      have hrbOne : rhoGlobal (r / b) = 1 :=
        rhoGlobal_eq_one_of_le_one ((div_le_one hb).mpr hrb.le)
      have hrrOne : rhoGlobal (r / r) = 1 := by
        rw [div_self (ne_of_gt hr)]
        exact rhoGlobal_eq_one_of_le_one le_rfl
      rw [hrbOne]
      calc
        1 - rhoGlobal (r / a) =
            (∫ e in a..r, positiveDickmanShape ((r - e) / e) / e) +
              ∫ e in r..b, positiveDickmanShape ((r - e) / e) / e := by
                rw [hleftShape, hrightZero, add_zero, ← hleft, hrrOne]
        _ = ∫ e in a..b, positiveDickmanShape ((r - e) / e) / e := hadd

/-- Largest-atom renewal equation for the scaled Dickman densities.  The
first two terms correspond to the empty boundary layer; the integral marks
the largest atom exposed while the cutoff moves from `a` to `b`.  This is an
exact analytic identity, with no limiting or almost-everywhere convention. -/
lemma scaledDickmanDensity_cutoff_renewal {r a b : ℝ} (hr : 0 < r)
    (ha : 0 < a) (hab : a ≤ b) :
    b * scaledDickmanDensity b r - a * scaledDickmanDensity a r =
      ∫ e in a..b, scaledDickmanDensity e (r - e) := by
  have hb : 0 < b := ha.trans_le hab
  have hra : 0 ≤ r / a := div_nonneg hr.le ha.le
  have hrb : 0 ≤ r / b := div_nonneg hr.le hb.le
  calc
    b * scaledDickmanDensity b r - a * scaledDickmanDensity a r =
        exp (-Real.eulerMascheroniConstant) *
          (rhoGlobal (r / b) - rhoGlobal (r / a)) := by
      rw [scaledDickmanDensity, scaledDickmanDensity,
        dickmanDensity_of_nonneg hrb, dickmanDensity_of_nonneg hra]
      field_simp [ne_of_gt ha, ne_of_gt hb]
    _ = exp (-Real.eulerMascheroniConstant) *
        ∫ e in a..b, positiveDickmanShape ((r - e) / e) / e := by
      rw [rhoGlobal_cutoff_increment_full hr ha hab]
    _ = ∫ e in a..b,
        exp (-Real.eulerMascheroniConstant) *
          (positiveDickmanShape ((r - e) / e) / e) := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ e in a..b, scaledDickmanDensity e (r - e) := by
      apply intervalIntegral.integral_congr
      intro e _he
      change exp (-Real.eulerMascheroniConstant) *
          (positiveDickmanShape ((r - e) / e) / e) =
        dickmanDensity ((r - e) / e) / e
      rw [dickmanDensity_eq_exp_mul_positiveDickmanShape]
      ring

/-- On the range used by one- and two-point Palm disintegration, the density
ratio is exactly the audited finite Dickman translate `F`. -/
lemma dickmanDensity_ratio_eq_F {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    dickmanDensity (U - x) / dickmanDensity U = F x := by
  have hUx0 : 0 ≤ U - x := by
    norm_num [U] at hx ⊢
    linarith [hx.2]
  have hU0 : 0 ≤ U := by norm_num [U]
  rw [dickmanDensity_of_nonneg hUx0, dickmanDensity_of_nonneg hU0]
  have hglobalx : rhoGlobal (U - x) = rho (U - x) := by
    apply rhoGlobal_eq_rho
    norm_num [U] at hx ⊢
    linarith [hx.1]
  have hglobalU : rhoGlobal U = rho U := by
    apply rhoGlobal_eq_rho
    norm_num [U]
  rw [hglobalx, hglobalU]
  unfold F
  have hexp : exp (-Real.eulerMascheroniConstant) ≠ 0 := ne_of_gt (exp_pos _)
  field_simp [hexp, rho_U_ne_zero]

lemma one_point_density_ratio {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    dickmanDensity (U - s) / dickmanDensity U = F s :=
  dickmanDensity_ratio_eq_F ⟨hs.1, hs.2.trans (by norm_num)⟩

lemma two_point_density_ratio {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    dickmanDensity (U - s - t) / dickmanDensity U = F (s + t) := by
  have hst : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have harg : U - s - t = U - (s + t) := by ring
  rw [harg]
  exact dickmanDensity_ratio_eq_F hst

/-- The two-point defect appearing in the conditioned covariance kernel. -/
def covarianceKernel (s t : ℝ) : ℝ := F (s + t) - F s * F t

lemma covarianceKernel_comm (s t : ℝ) :
    covarianceKernel s t = covarianceKernel t s := by
  unfold covarianceKernel
  rw [add_comm]
  ring

/-- The Dickman averaging identity after translating the unit interval.
This is the analytic content of the total-mass constraint. -/
lemma integral_rho_U_sub_shift (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, rho (U - s - t)) = (U - s) * rho (U - s) := by
  have hx1 : 1 ≤ U - s := by
    norm_num [U] at hs ⊢
    linarith [hs.2]
  have hx5 : U - s ≤ 5 := by
    norm_num [U] at hs ⊢
    linarith [hs.1]
  have havg := rho_average_eq (x := U - s) hx1 hx5
  have hcomp := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 1) rho (U - s)
  rw [show U - s - 1 = (U - s) - 1 by ring] at havg
  rw [hcomp]
  simpa [sub_eq_add_neg, add_assoc] using havg.symm

/-- At zero shift the preceding formula gives the first Palm mass identity. -/
lemma integral_rho_U_sub :
    (∫ t in (0 : ℝ)..1, rho (U - t)) = U * rho U := by
  simpa using integral_rho_U_sub_shift 0 (by norm_num)

/-- The normalized one-point Dickman weight integrates to the conditioned
total `U`. -/
lemma integral_F : (∫ t in (0 : ℝ)..1, F t) = U := by
  unfold F
  have hconst :
      (∫ t in (0 : ℝ)..1, rho (U - t) / rho U) =
        (∫ t in (0 : ℝ)..1, rho (U - t)) / rho U := by
    exact intervalIntegral.integral_div (f := fun t : ℝ => rho (U - t))
      (a := (0 : ℝ)) (b := 1) (rho U)
  rw [hconst, integral_rho_U_sub]
  field_simp [rho_U_ne_zero]

/-- The shifted one-point Palm weight has the exact residual-mass moment. -/
lemma integral_F_shift (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, F (s + t)) = (U - s) * F s := by
  unfold F
  simp_rw [show ∀ t : ℝ, U - (s + t) = U - s - t by intro t; ring]
  have hconst :
      (∫ t in (0 : ℝ)..1, rho (U - s - t) / rho U) =
        (∫ t in (0 : ℝ)..1, rho (U - s - t)) / rho U := by
    exact intervalIntegral.integral_div
      (f := fun t : ℝ => rho (U - s - t))
      (a := (0 : ℝ)) (b := 1) (rho U)
  rw [hconst, integral_rho_U_sub_shift s hs]
  ring

/-- Integrating one variable of the covariance kernel yields exactly the
negative diagonal term required by the deterministic total constraint. -/
lemma integral_covarianceKernel (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, covarianceKernel s t) = -s * F s := by
  have hFint : IntervalIntegrable F volume 0 1 := by
    have hcont : Continuous F := by
      unfold F
      exact (continuous_rho.comp
        (continuous_const.sub continuous_id)).div_const (rho U)
    exact hcont.intervalIntegrable 0 1
  have hshift : IntervalIntegrable (fun t : ℝ => F (s + t)) volume 0 1 := by
    have hcont : Continuous (fun t : ℝ => F (s + t)) := by
      have hF : Continuous F := by
        unfold F
        exact (continuous_rho.comp
          (continuous_const.sub continuous_id)).div_const (rho U)
      exact hF.comp (continuous_const.add continuous_id)
    exact hcont.intervalIntegrable 0 1
  change (∫ t in (0 : ℝ)..1, F (s + t) - F s * F t) = -s * F s
  rw [intervalIntegral.integral_sub hshift (hFint.const_mul (F s))]
  rw [integral_F_shift s hs, intervalIntegral.integral_const_mul, integral_F]
  ring

/-- The covariance operator on a pointwise test function.  For the null
direction `f(t)=t`, the apparent logarithmic singularity cancels exactly. -/
def covarianceOperator (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  F s * f s + ∫ t in (0 : ℝ)..1, covarianceKernel s t * f t / t

/-- The scale function belongs to the kernel, proved from the Dickman
averaging equation rather than from an assumed conditioned process. -/
lemma covarianceOperator_id (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    covarianceOperator id s = 0 := by
  have hzero :
      (∫ t in (0 : ℝ)..1, covarianceKernel s t * id t / t) =
        ∫ t in (0 : ℝ)..1, covarianceKernel s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [covarianceKernel]
    · simp [id, ht0]
  rw [covarianceOperator, hzero, integral_covarianceKernel s hs]
  simp [id]
  ring

/-- The same calculation for every scalar multiple of the scale function. -/
lemma covarianceOperator_smul_id (lambda : ℝ) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    covarianceOperator (fun t => lambda * t) s = 0 := by
  have hzero :
      (∫ t in (0 : ℝ)..1,
          covarianceKernel s t * (lambda * t) / t) =
        lambda * ∫ t in (0 : ℝ)..1, covarianceKernel s t := by
    calc
      (∫ t in (0 : ℝ)..1,
          covarianceKernel s t * (lambda * t) / t) =
          ∫ t in (0 : ℝ)..1, lambda * covarianceKernel s t := by
            apply intervalIntegral.integral_congr
            intro t ht
            by_cases ht0 : t = 0
            · subst t
              simp [covarianceKernel]
            · field_simp
      _ = lambda * ∫ t in (0 : ℝ)..1, covarianceKernel s t := by
        rw [intervalIntegral.integral_const_mul]
  rw [covarianceOperator, hzero, integral_covarianceKernel s hs]
  ring

/-! ## Density-weighted Palm moments and covariance -/

lemma continuous_F : Continuous F := by
  unfold F
  exact (continuous_rho.comp
    (continuous_const.sub continuous_id)).div_const (rho U)

lemma continuous_covarianceKernel :
    Continuous (Function.uncurry covarianceKernel) := by
  unfold covarianceKernel Function.uncurry
  exact (continuous_F.comp (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul (continuous_F.comp continuous_snd))

/-! ## The removable axis singularity and a continuous kernel representative -/

/-- A globally continuous extension of `F'` obtained by projecting to the
compact interval on which the covariance kernel is evaluated. -/
def derivFExtension (x : ℝ) : ℝ :=
  deriv F (projIcc (0 : ℝ) 2 (by norm_num) x)

lemma continuous_derivFExtension : Continuous derivFExtension := by
  have hrestrict : Continuous
      (fun x : Icc (0 : ℝ) 2 => deriv F x) := (continuousOn_deriv_F).restrict
  exact hrestrict.comp continuous_projIcc

/-- Jointly continuous divided-difference extension, defined by the
fundamental-theorem-of-calculus average of the extended derivative. -/
def FdifferenceQuotient (a t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, derivFExtension (a + u * t)

lemma continuous_uncurry_FdifferenceQuotient :
    Continuous (Function.uncurry FdifferenceQuotient) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := (0 : ℝ)) (b₀ := 1)
  exact continuous_derivFExtension.comp
    ((continuous_fst.comp continuous_fst).add
      (continuous_snd.mul (continuous_snd.comp continuous_fst)))

lemma derivFExtension_eq_deriv_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 2) :
    derivFExtension x = deriv F x := by
  simp [derivFExtension,
    projIcc_of_mem (show (0 : ℝ) ≤ 2 by norm_num) hx]

lemma mul_FdifferenceQuotient_eq_sub {a t : ℝ}
    (ha : a ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * FdifferenceQuotient a t = F (a + t) - F a := by
  have hat : a ≤ a + t := le_add_of_nonneg_right ht.1
  have hpath (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      a + u * t ∈ Icc (0 : ℝ) 2 := by
    constructor
    · exact add_nonneg ha.1 (mul_nonneg hu.1 ht.1)
    · nlinarith [ha.2, ht.2, hu.2, mul_nonneg hu.1 ht.1]
  have hreplace :
      (∫ u in (0 : ℝ)..1, derivFExtension (a + u * t)) =
        ∫ u in (0 : ℝ)..1, deriv F (a + t * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have humem : u ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
    change derivFExtension (a + u * t) = deriv F (a + t * u)
    rw [derivFExtension_eq_deriv_of_mem (hpath u humem)]
    congr 2
    ring
  have hsubset : Icc a (a + t) ⊆ Icc (0 : ℝ) 2 := by
    intro x hx
    constructor
    · exact ha.1.trans hx.1
    · nlinarith [hx.2, ha.2, ht.2]
  have hint : IntervalIntegrable (deriv F) volume a (a + t) :=
    (continuousOn_deriv_F.mono hsubset).intervalIntegrable_of_Icc hat
  have hdiff : ∀ x ∈ [[a, a + t]], DifferentiableAt ℝ F x := by
    intro x hx
    apply differentiableAt_F
    apply hsubset
    simpa [uIcc_of_le hat] using hx
  rw [FdifferenceQuotient, hreplace]
  change t • (∫ u in (0 : ℝ)..1, deriv F (a + t * u)) = _
  rw [intervalIntegral.smul_integral_comp_add_mul]
  simp only [mul_zero, add_zero, mul_one]
  exact intervalIntegral.integral_deriv_eq_sub hdiff hint

/-- Continuous extension of `covarianceKernel s t / t` across `t = 0`. -/
def covarianceKernelQuotient (s t : ℝ) : ℝ :=
  FdifferenceQuotient s t - F s * FdifferenceQuotient 0 t

lemma continuous_uncurry_covarianceKernelQuotient :
    Continuous (Function.uncurry covarianceKernelQuotient) := by
  exact continuous_uncurry_FdifferenceQuotient.sub
    ((continuous_F.comp continuous_fst).mul
      (continuous_uncurry_FdifferenceQuotient.comp
        (continuous_const.prodMk continuous_snd)))

lemma mul_covarianceKernelQuotient_eq_kernel {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    t * covarianceKernelQuotient s t = covarianceKernel s t := by
  have hqst := mul_FdifferenceQuotient_eq_sub hs ht
  have hq0t := mul_FdifferenceQuotient_eq_sub
    (a := (0 : ℝ)) (by norm_num) ht
  unfold covarianceKernelQuotient covarianceKernel
  calc
    t * (FdifferenceQuotient s t - F s * FdifferenceQuotient 0 t) =
        t * FdifferenceQuotient s t -
          F s * (t * FdifferenceQuotient 0 t) := by ring
    _ = (F (s + t) - F s) - F s * (F (0 + t) - F 0) := by
      rw [hqst, hq0t]
    _ = F (s + t) - F s * F t := by simp [F_zero]; ring

lemma covarianceKernelQuotient_eq_div {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (ht0 : t ≠ 0) :
    covarianceKernelQuotient s t = covarianceKernel s t / t := by
  apply (eq_div_iff ht0).2
  rw [mul_comm]
  exact mul_covarianceKernelQuotient_eq_kernel hs ht

/-- An `L¹(dt)` input produces a continuous parameter integral after the
removable quotient is filled in. -/
lemma continuousOn_covarianceKernelIntegral (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (0 : ℝ) 1) :
    ContinuousOn (fun s : ℝ =>
      ∫ t in (0 : ℝ)..1, covarianceKernelQuotient s t * f t)
      (Icc (0 : ℝ) 1) := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hScompact.exists_bound_of_continuousOn
    continuous_uncurry_covarianceKernelQuotient.continuousOn
  have hcontinuous : Continuous (fun s : Icc (0 : ℝ) 1 =>
      ∫ t in (0 : ℝ)..1, covarianceKernelQuotient s t * f t) := by
    apply intervalIntegral.continuous_of_dominated_interval
      (bound := fun t => C * ‖f t‖)
    · intro s
      have hcoef : Continuous
          (fun t : ℝ => covarianceKernelQuotient s t) :=
        continuous_uncurry_covarianceKernelQuotient.comp
          (continuous_const.prodMk continuous_id)
      have hfmeas : AEStronglyMeasurable f
          (volume.restrict (Ι (0 : ℝ) 1)) := by
        simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
          hf.1.aestronglyMeasurable
      exact hcoef.aestronglyMeasurable.mul hfmeas
    · intro s
      filter_upwards with t ht
      have htIcc : t ∈ Icc (0 : ℝ) 1 := by
        have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
          simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
        exact ⟨htIoc.1.le, htIoc.2⟩
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (hC (s, t) (by exact ⟨s.property, htIcc⟩)) (norm_nonneg _)
    · exact hf.norm.const_mul C
    · filter_upwards with t ht
      exact (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_subtype_val.prodMk continuous_const)).mul continuous_const
  rw [continuousOn_iff_continuous_restrict]
  exact hcontinuous

lemma singularKernelIntegral_eq_extended (f : ℝ → ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, covarianceKernel s t * f t / t) =
      ∫ t in (0 : ℝ)..1, covarianceKernelQuotient s t * f t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
    simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
  have htIcc : t ∈ Icc (0 : ℝ) 1 := ⟨htIoc.1.le, htIoc.2⟩
  have ht0 : t ≠ 0 := ne_of_gt htIoc.1
  rw [covarianceKernelQuotient_eq_div hs htIcc ht0]
  ring

/-- The continuous representative forced by the equation `Af = 0`. -/
def covarianceKernelRepresentative (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  -(∫ t in (0 : ℝ)..1, covarianceKernelQuotient s t * f t) / F s

lemma continuousOn_covarianceKernelRepresentative (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (0 : ℝ) 1) :
    ContinuousOn (covarianceKernelRepresentative f) (Icc (0 : ℝ) 1) := by
  have hnum := (continuousOn_covarianceKernelIntegral f hf).neg
  apply hnum.div continuous_F.continuousOn
  intro s hs
  exact ne_of_gt (F_pos ⟨hs.1, hs.2.trans (by norm_num)⟩)

lemma ae_eq_covarianceKernelRepresentative_of_operator_zero (f : ℝ → ℝ)
    (hzero : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      covarianceOperator f s = 0) :
    f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      covarianceKernelRepresentative f := by
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioc] with s hs0 hs
  have hsIcc : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
  have hF0 : F s ≠ 0 :=
    ne_of_gt (F_pos ⟨hsIcc.1, hsIcc.2.trans (by norm_num)⟩)
  rw [covarianceOperator, singularKernelIntegral_eq_extended f hsIcc] at hs0
  unfold covarianceKernelRepresentative
  apply (eq_div_iff hF0).2
  nlinarith

/-- Every integrable null vector of the covariance operator has an explicit
continuous representative on the closed unit interval. -/
theorem exists_continuousRepresentative_of_covarianceOperator_ae_zero
    (f : ℝ → ℝ) (hf : IntervalIntegrable f volume (0 : ℝ) 1)
    (hzero : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      covarianceOperator f s = 0) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc (0 : ℝ) 1) ∧
      f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
  exact ⟨covarianceKernelRepresentative f,
    continuousOn_covarianceKernelRepresentative f hf,
    ae_eq_covarianceKernelRepresentative_of_operator_zero f hzero⟩

/-- Finite weighted energy in `L²(dt/t)` implies the ordinary `L¹(dt)`
integrability needed by the removable-kernel argument.  The estimate is the
pointwise inequality
`|f(t)| ≤ (f(t)^2 / t + t) / 2` for `0 < t ≤ 1`. -/
lemma intervalIntegrable_of_weightedSquare
    (f : ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hsq : IntervalIntegrable (fun t : ℝ => f t ^ 2 / t)
      volume (0 : ℝ) 1) :
    IntervalIntegrable f volume (0 : ℝ) 1 := by
  have ht : IntervalIntegrable (fun t : ℝ => t) volume (0 : ℝ) 1 :=
    continuous_id.intervalIntegrable 0 1
  have hmajorant : IntervalIntegrable
      (fun t : ℝ => (2 : ℝ)⁻¹ * (f t ^ 2 / t + t))
      volume (0 : ℝ) 1 :=
    (hsq.add ht).const_mul (2 : ℝ)⁻¹
  apply hmajorant.mono_fun'
  · simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfmeas
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht01
    have htIoc : t ∈ Ioc (0 : ℝ) 1 := by
      simpa [uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht01
    have htpos : 0 < t := htIoc.1
    have hsqBound : 2 * |f t| * t ≤ f t ^ 2 + t ^ 2 := by
      simpa [sq_abs] using two_mul_le_add_sq |f t| t
    have hdiv : 2 * |f t| ≤ f t ^ 2 / t + t := by
      calc
        2 * |f t| ≤ (f t ^ 2 + t ^ 2) / t :=
          (le_div_iff₀ htpos).2 (by simpa [mul_assoc] using hsqBound)
        _ = f t ^ 2 / t + t := by field_simp
    rw [Real.norm_eq_abs]
    have htwo : (0 : ℝ) < 2 := by norm_num
    calc
      |f t| ≤ (f t ^ 2 / t + t) / 2 :=
        (le_div_iff₀ htwo).2 (by simpa [mul_comm] using hdiv)
      _ = (2 : ℝ)⁻¹ * (f t ^ 2 / t + t) := by ring

/-- The continuous-representative conclusion under the natural weighted
`L²(dt/t)` hypothesis of the Poisson--Dickman covariance space. -/
theorem exists_continuousRepresentative_of_weightedSquare_operator_ae_zero
    (f : ℝ → ℝ)
    (hfmeas : AEStronglyMeasurable f
      (volume.restrict (Ioc (0 : ℝ) 1)))
    (hsq : IntervalIntegrable (fun t : ℝ => f t ^ 2 / t)
      volume (0 : ℝ) 1)
    (hzero : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      covarianceOperator f s = 0) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Icc (0 : ℝ) 1) ∧
      f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] g := by
  exact exists_continuousRepresentative_of_covarianceOperator_ae_zero f
    (intervalIntegrable_of_weightedSquare f hfmeas hsq) hzero

/-- One-point density-weighted Palm moment for a statistic `t * Q(t)`.
The logarithmic intensity `dt/t` cancels the displayed factor `t`. -/
def palmMean (Q : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, F t * Q t

/-- Ordered two-point factorial Palm moment for statistics `s*Q(s)` and
`t*R(t)`. -/
def palmPair (Q R : ℝ → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, F (s + t) * Q s * R t

/-- The second moment includes the diagonal one-point contribution. -/
def palmSecondMoment (Q R : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, F t * t * Q t * R t) + palmPair Q R

/-- Covariance determined by the density-weighted one- and two-point Palm
moments. -/
def palmCovariance (Q R : ℝ → ℝ) : ℝ :=
  palmSecondMoment Q R - palmMean Q * palmMean R

/-- Quadratic-kernel form of the same covariance. -/
def kernelCovarianceForm (Q R : ℝ → ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, F t * t * Q t * R t) +
    ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1,
      covarianceKernel s t * Q s * R t

/-- The exact covariance representation obtained by subtracting the product
of the one-point Palm moments from the one-plus-two-point second moment.
Continuity is more than enough for every integral below and avoids hiding
Fubini or integrability side conditions. -/
lemma palmCovariance_eq_kernelCovarianceForm (Q R : ℝ → ℝ)
    (hQ : Continuous Q) (hR : Continuous R) :
    palmCovariance Q R = kernelCovarianceForm Q R := by
  have hFQ : Continuous (fun t : ℝ => F t * Q t) := continuous_F.mul hQ
  have hFR : Continuous (fun t : ℝ => F t * R t) := continuous_F.mul hR
  have hsep (s : ℝ) :
      (∫ t in (0 : ℝ)..1, F s * F t * Q s * R t) =
        (F s * Q s) * palmMean R := by
    unfold palmMean
    calc
      (∫ t in (0 : ℝ)..1, F s * F t * Q s * R t) =
          ∫ t in (0 : ℝ)..1, (F s * Q s) * (F t * R t) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
      _ = (F s * Q s) * ∫ t in (0 : ℝ)..1, F t * R t := by
        rw [intervalIntegral.integral_const_mul]
  have hproduct :
      (∫ s in (0 : ℝ)..1,
          ∫ t in (0 : ℝ)..1, F s * F t * Q s * R t) =
        palmMean Q * palmMean R := by
    simp_rw [hsep]
    unfold palmMean
    rw [intervalIntegral.integral_mul_const]
  have hinner (s : ℝ) :
      (∫ t in (0 : ℝ)..1, covarianceKernel s t * Q s * R t) =
        (∫ t in (0 : ℝ)..1, F (s + t) * Q s * R t) -
          ∫ t in (0 : ℝ)..1, F s * F t * Q s * R t := by
    have hleft : IntervalIntegrable
        (fun t : ℝ => F (s + t) * Q s * R t) volume 0 1 := by
      exact ((continuous_F.comp (continuous_const.add continuous_id)).mul
        continuous_const |>.mul hR).intervalIntegrable 0 1
    have hright : IntervalIntegrable
        (fun t : ℝ => F s * F t * Q s * R t) volume 0 1 := by
      exact (((continuous_const.mul continuous_F).mul continuous_const).mul hR)
        |>.intervalIntegrable 0 1
    change (∫ t in (0 : ℝ)..1,
      (F (s + t) - F s * F t) * Q s * R t) = _
    rw [← intervalIntegral.integral_sub hleft hright]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have houterLeft : IntervalIntegrable
      (fun s : ℝ => ∫ t in (0 : ℝ)..1, F (s + t) * Q s * R t)
      volume 0 1 := by
    have hcont : Continuous (fun s : ℝ =>
        ∫ t in (0 : ℝ)..1, F (s + t) * Q s * R t) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      exact ((continuous_F.comp (continuous_fst.add continuous_snd)).mul
        (hQ.comp continuous_fst)).mul (hR.comp continuous_snd)
    exact hcont.intervalIntegrable 0 1
  have houterRight : IntervalIntegrable
      (fun s : ℝ => ∫ t in (0 : ℝ)..1, F s * F t * Q s * R t)
      volume 0 1 := by
    simp_rw [hsep]
    exact (hFQ.mul continuous_const).intervalIntegrable 0 1
  unfold palmCovariance palmSecondMoment kernelCovarianceForm palmPair
  simp_rw [hinner]
  rw [intervalIntegral.integral_sub houterLeft houterRight, hproduct]
  ring

/-! ## The measurable Cauchy endpoint of the kernel argument -/

/-- A globally additive measurable real function is linear.  This packages
the last, purely functional-analytic, step used after the local Palm argument
has produced an additive representative. -/
lemma measurable_additive_eq_smul (f : ℝ → ℝ) (hf : Measurable f)
    (hadd : ∀ x y : ℝ, f (x + y) = f x + f y) :
    ∀ x : ℝ, f x = x * f 1 := by
  have hzero : f 0 = 0 := by
    have h := hadd 0 0
    simp only [zero_add] at h
    linarith
  let phi : ℝ →+ ℝ :=
    { toFun := f
      map_zero' := hzero
      map_add' := fun x y => hadd x y }
  have hphiMeas : Measurable phi := by
    simpa [phi] using hf
  have hphiCont : Continuous phi :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable phi hphiMeas
  intro x
  have hscale := map_real_smul phi hphiCont x (1 : ℝ)
  simpa [phi] using hscale

/-- Equivalent slope formulation. -/
lemma measurable_additive_linear (f : ℝ → ℝ) (hf : Measurable f)
    (hadd : ∀ x y : ℝ, f (x + y) = f x + f y) :
    ∃ lambda : ℝ, ∀ x : ℝ, f x = lambda * x := by
  refine ⟨f 1, ?_⟩
  intro x
  rw [measurable_additive_eq_smul f hf hadd x]
  ring

/-! The Palm argument produces additivity first on the positive triangle.
The following deterministic lemma records that no global Cauchy equation is
needed: continuity on the closed unit interval and local additivity already
force one common slope. -/

private lemma continuous_local_additive_nat (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hadd : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x + y ≤ 1 → f (x + y) = f x + f y)
    {x : ℝ} (hx0 : 0 ≤ x) (n : ℕ) (hn : (n : ℝ) * x ≤ 1) :
    f ((n : ℝ) * x) = (n : ℝ) * f x := by
  induction n with
  | zero => simpa using hf0
  | succ n ih =>
      have hnx0 : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx0
      have hnx : (n : ℝ) * x ≤ 1 := by
        have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by norm_num
        exact (mul_le_mul_of_nonneg_right hcast hx0).trans (by simpa using hn)
      have hx1 : x ≤ 1 := by
        have hle : x ≤ (n + 1 : ℕ) * x := by
          have hone : (1 : ℝ) ≤ (n + 1 : ℕ) := by norm_num
          simpa using mul_le_mul_of_nonneg_right hone hx0
        exact hle.trans (by simpa using hn)
      have hsum : (n : ℝ) * x + x ≤ 1 := by
        simpa [Nat.cast_add, Nat.cast_one, add_mul] using hn
      have hstep := hadd ((n : ℝ) * x) ⟨hnx0, hnx⟩ x ⟨hx0, hx1⟩ hsum
      rw [show ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x by push_cast; ring,
        hstep, ih hnx]
      push_cast
      ring

private lemma continuous_local_additive_fraction (f : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hadd : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x + y ≤ 1 → f (x + y) = f x + f y)
    (N k : ℕ) (hN : 0 < N) (hk : k ≤ N) :
    f ((k : ℝ) / N) = f 1 * ((k : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNR
  let z : ℝ := 1 / (N : ℝ)
  have hz0 : 0 ≤ z := by positivity
  have hNz : (N : ℝ) * z = 1 := by
    dsimp [z]
    field_simp
  have hkR : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hkz : (k : ℝ) * z ≤ 1 := by
    rw [← hNz]
    exact mul_le_mul_of_nonneg_right hkR hz0
  have hden := continuous_local_additive_nat f hf0 hadd hz0 N (by rw [hNz])
  have hnum := continuous_local_additive_nat f hf0 hadd hz0 k hkz
  have hzval : f z = f 1 / (N : ℝ) := by
    apply (eq_div_iff hNne).2
    rw [mul_comm]
    simpa [hNz] using hden.symm
  calc
    f ((k : ℝ) / N) = f ((k : ℝ) * z) := by simp [z, div_eq_mul_inv]
    _ = (k : ℝ) * f z := hnum
    _ = f 1 * ((k : ℝ) / N) := by
      rw [hzval]
      field_simp

/-- A continuous locally additive function on `[0,1]` is a scalar multiple
of the coordinate.  Natural-floor rational approximants are used explicitly,
so no density argument is hidden. -/
lemma continuousOn_local_additive_linear (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hadd : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      x + y ≤ 1 → f (x + y) = f x + f y) :
    ∃ lambda : ℝ, ∀ x ∈ Icc (0 : ℝ) 1, f x = lambda * x := by
  have hf0 : f 0 = 0 := by
    have h := hadd 0 (by norm_num) 0 (by norm_num) (by norm_num)
    norm_num at h
    linarith
  refine ⟨f 1, ?_⟩
  intro x hx
  let N : ℕ → ℕ := fun n => n + 1
  let k : ℕ → ℕ := fun n => ⌊((N n : ℕ) : ℝ) * x⌋₊
  let a : ℕ → ℝ := fun n => (k n : ℝ) / (N n : ℕ)
  have hNpos (n : ℕ) : 0 < N n := by simp [N]
  have harg0 (n : ℕ) : 0 ≤ ((N n : ℕ) : ℝ) * x :=
    mul_nonneg (Nat.cast_nonneg _) hx.1
  have hkN (n : ℕ) : k n ≤ N n := by
    have hkNR : (k n : ℝ) ≤ (N n : ℕ) := by
      calc
        (k n : ℝ) ≤ (N n : ℕ) * x := Nat.floor_le (harg0 n)
        _ ≤ (N n : ℕ) := by
          have hNR : (0 : ℝ) ≤ (N n : ℕ) := Nat.cast_nonneg _
          simpa using mul_le_mul_of_nonneg_left hx.2 hNR
    exact_mod_cast hkNR
  have ha0 (n : ℕ) : 0 ≤ a n := by
    dsimp [a]
    positivity
  have hale (n : ℕ) : a n ≤ x := by
    have hNR : (0 : ℝ) < (N n : ℕ) := by exact_mod_cast hNpos n
    apply (div_le_iff₀ hNR).2
    simpa [k, mul_comm] using Nat.floor_le (harg0 n)
  have haMem (n : ℕ) : a n ∈ Icc (0 : ℝ) 1 :=
    ⟨ha0 n, (hale n).trans hx.2⟩
  have hgap (n : ℕ) : x - a n < 1 / ((N n : ℕ) : ℝ) := by
    have hNR : (0 : ℝ) < (N n : ℕ) := by exact_mod_cast hNpos n
    have hfloor := Nat.lt_floor_add_one (((N n : ℕ) : ℝ) * x)
    apply (lt_div_iff₀ hNR).2
    dsimp [a, k]
    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hNR)]
    linarith
  have hgap_nonneg (n : ℕ) : 0 ≤ x - a n := sub_nonneg.mpr (hale n)
  have hgap_tendsto : Tendsto (fun n => x - a n) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall hgap_nonneg)
      (Eventually.of_forall fun n => (hgap n).le)
    simpa [N] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0))
  have ha_tendsto : Tendsto a atTop (nhds x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have heq : (fun n => ‖a n - x‖) = fun n => x - a n := by
      funext n
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hale n))]
      ring
    rw [heq]
    exact hgap_tendsto
  have ha_within : Tendsto a atTop (nhdsWithin x (Icc (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha_tendsto, Eventually.of_forall haMem⟩
  have hf_tendsto : Tendsto (fun n => f (a n)) atTop (nhds (f x)) :=
    (hf x hx).tendsto.comp ha_within
  have hformula (n : ℕ) : f (a n) = f 1 * a n := by
    exact continuous_local_additive_fraction f hf0 hadd (N n) (k n)
      (hNpos n) (hkN n)
  have hlinear_tendsto : Tendsto (fun n => f 1 * a n) atTop (nhds (f 1 * x)) :=
    tendsto_const_nhds.mul ha_tendsto
  have hf_tendsto' : Tendsto (fun n => f (a n)) atTop (nhds (f 1 * x)) :=
    hlinear_tendsto.congr' (Eventually.of_forall fun n => (hformula n).symm)
  exact tendsto_nhds_unique hf_tendsto hf_tendsto'

end Erdos390.Full.ConditionedPoissonLimit
