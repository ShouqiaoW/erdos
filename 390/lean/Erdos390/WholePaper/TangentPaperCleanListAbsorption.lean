import Erdos390.WholePaper.TangentCanonicalCleanListLower
import Erdos390.WholePaper.UpperScale

/-!
# Closing the paper-scale tangent clean-list inequality

This file fixes the moving parameters used in Section 9 of the paper:

* `h = upperTailLength c n = ceil(c n / log n)`;
* `Phead = roughHeadModulus W`;
* `X0 = ceil(n ^ deltaStar)`;
* `y = yNat n = floor(n ^ (2/9))`;
* `W < v <= u <= y` and `u / v <= r0 < 3/2`.

For fixed `W`, `K`, `c`, `r0`, and `deltaStar`, the head-density gap is

`roughHeadDensity W * (2 - r0)`.

We reserve one sixteenth of that gap as the effective list density.  A
slightly conservative explicit version of the paper's one-time cutoff makes
the canonical Selberg main term at most one quarter of the gap.  The
Lambda-squared endpoint remainder and the sharp bank deletion census are
then `o(n/u)`, uniformly for `u <= yNat n`.  The fixed-modulus endpoint loss,
the natural floors and ceilings, and `K*h` are absorbed at the same scale.

Consequently the final candidate-floor-versus-loss inequality is proved
eventually; it is not retained as a premise of the paper-facing wrapper.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Literal Section 9 parameters -/

/-- The least natural exceptional-row cutoff which is at least the paper's
real threshold `X0=n^deltaStar`.  Using the ceiling makes the integral clean
condition a strengthening of the literal real condition, rather than losing
the unit-width boundary band. -/
def tangentPaperExceptionalCutoff (deltaStar : ℝ) (n : ℕ) : ℕ :=
  ⌈(n : ℝ) ^ deltaStar⌉₊

/-- The fixed positive density reserved after the raw head gap and the
canonical exceptional loss have been separated. -/
def tangentPaperHeadGap (W : ℕ) (r0 : ℝ) : ℝ :=
  roughHeadDensity W * (2 - r0)

/-- One sixteenth of the literal fixed-head gap. -/
def tangentPaperCleanListDensity (W : ℕ) (r0 : ℝ) : ℝ :=
  tangentPaperHeadGap W r0 / 16

/-- The fixed-head gap is positive whenever the endpoint-ratio cap is below
two. -/
theorem tangentPaperHeadGap_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperHeadGap W r0 := by
  unfold tangentPaperHeadGap
  exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0)

/-- The retained one-sixteenth clean-list density is positive under the same
ratio cap. -/
theorem tangentPaperCleanListDensity_pos
    (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperCleanListDensity W r0 := by
  unfold tangentPaperCleanListDensity
  exact div_pos (tangentPaperHeadGap_pos W hr0) (by norm_num)

/-- The natural ceiling dominates the literal real exceptional cutoff. -/
theorem tangentPaperExceptionalCutoff_cast_ge
    (deltaStar : ℝ) (n : ℕ) :
    (n : ℝ) ^ deltaStar ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.le_ceil _

/-- The safe ceiling changes the paper's real cutoff by strictly less than
one. -/
theorem tangentPaperExceptionalCutoff_cast_lt_add_one
    (deltaStar : ℝ) (n : ℕ) :
    (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
      (n : ℝ) ^ deltaStar + 1 := by
  unfold tangentPaperExceptionalCutoff
  exact Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg n) deltaStar)

/-- Passing the safe integral cutoff test implies the literal real
Section 9 test `2n/R_y(a) >= n^deltaStar`. -/
theorem tangentPaperExceptionalCutoff_le_roughScale_implies_real
    {deltaStar : ℝ} {n y a : ℕ}
    (hscale : tangentPaperExceptionalCutoff deltaStar n ≤
      tangentRoughScale n y a) :
    (n : ℝ) ^ deltaStar ≤
      2 * (n : ℝ) / (completeRoughLabel y a : ℝ) := by
  have hscaleCast :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        (tangentRoughScale n y a : ℝ) := by
    exact_mod_cast hscale
  calc
    (n : ℝ) ^ deltaStar ≤
        (tangentPaperExceptionalCutoff deltaStar n : ℝ) :=
      tangentPaperExceptionalCutoff_cast_ge deltaStar n
    _ ≤ (tangentRoughScale n y a : ℝ) := hscaleCast
    _ ≤ ((2 * n : ℕ) : ℝ) / (completeRoughLabel y a : ℝ) := by
      unfold tangentRoughScale
      exact Nat.cast_div_le
    _ = 2 * (n : ℝ) / (completeRoughLabel y a : ℝ) := by
      push_cast
      ring

/-- A nonnegative exponent and positive base make the natural exceptional
cutoff strictly positive. -/
theorem tangentPaperExceptionalCutoff_pos
    {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < tangentPaperExceptionalCutoff deltaStar n := by
  have hone : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdelta
  have hceil := tangentPaperExceptionalCutoff_cast_ge deltaStar n
  have hcast : (1 : ℝ) ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) := hone.trans hceil
  have hnat : 1 ≤ tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast hcast
  omega

/-- The ceiling cutoff has logarithm at most the paper exponent term plus
the single `log 2` ceiling loss. -/
theorem tangentPaperExceptionalCutoff_log_le
    {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
      deltaStar * L n + Real.log 2 := by
  have hcutPos : (0 : ℝ) < tangentPaperExceptionalCutoff deltaStar n := by
    exact_mod_cast tangentPaperExceptionalCutoff_pos hdelta hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast hn) hdelta
  have hcutUpper :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        2 * (n : ℝ) ^ deltaStar := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
          (n : ℝ) ^ deltaStar + 1 :=
        (tangentPaperExceptionalCutoff_cast_lt_add_one
          deltaStar n).le
      _ ≤ 2 * (n : ℝ) ^ deltaStar := by linarith
  calc
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        Real.log (2 * (n : ℝ) ^ deltaStar) :=
      Real.log_le_log hcutPos hcutUpper
    _ = deltaStar * L n + Real.log 2 := by
      rw [Real.log_mul (by norm_num)
        (Real.rpow_pos_of_pos hnPos deltaStar).ne',
        Real.log_rpow hnPos]
      unfold L
      ring

/-! ## The harmonic main term -/

/-- The sum of all literal rough-label interval lengths is bounded by the
full harmonic sum up to `X0`.  This is the Mertens/harmonic main-term layer
of the exceptional deletion, before division by `log y`. -/
theorem tangentCanonicalExceptionalLengthSum_le_harmonic
    {n K h X0 u v : ℕ} (hu : 0 < u) :
    tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      (2 * (n : ℝ) / (u : ℝ)) *
        (1 + Real.log (X0 : ℝ)) := by
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hbroad : tangentBroadUpper n K h ≤ 2 * n := by
    unfold tangentBroadUpper
    exact Nat.sub_le _ _
  have hterm : ∀ b ∈ tangentExceptionalSmoothIndices X0 u,
      (((tangentBroadUpper n K h / (u * b) -
          n / (v * b) : ℕ) : ℝ)) ≤
        (2 * (n : ℝ) / (u : ℝ)) * (1 / (b : ℝ)) := by
    intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbOne : 1 ≤ b := (Finset.mem_Icc.mp hbData.1).1
    have hbPos : 0 < b := Nat.zero_lt_of_lt hbOne
    have hbR : (0 : ℝ) < b := by exact_mod_cast hbPos
    calc
      (((tangentBroadUpper n K h / (u * b) -
          n / (v * b) : ℕ) : ℝ)) ≤
          ((tangentBroadUpper n K h / (u * b) : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le
          (tangentBroadUpper n K h / (u * b)) (n / (v * b))
      _ ≤ (tangentBroadUpper n K h : ℝ) / ((u * b : ℕ) : ℝ) :=
        Nat.cast_div_le
      _ ≤ ((2 * n : ℕ) : ℝ) / ((u * b : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hbroad)
          (Nat.cast_nonneg _)
      _ = (2 * (n : ℝ) / (u : ℝ)) * (1 / (b : ℝ)) := by
        push_cast
        field_simp [huR.ne', hbR.ne']
  have hsubset : tangentExceptionalSmoothIndices X0 u ⊆ Finset.Ioc 0 X0 := by
    intro b hb
    have hbData := Finset.mem_filter.mp hb
    have hbIcc := Finset.mem_Icc.mp hbData.1
    exact Finset.mem_Ioc.mpr ⟨by omega, hbIcc.2⟩
  have hreciprocal :
      (∑ b ∈ tangentExceptionalSmoothIndices X0 u, 1 / (b : ℝ)) ≤
        ∑ b ∈ Finset.Ioc 0 X0, 1 / (b : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro b hb _hnot
    have hbPos : 0 < b := (Finset.mem_Ioc.mp hb).1
    positivity
  have hharmonic :
      (∑ b ∈ tangentExceptionalSmoothIndices X0 u, 1 / (b : ℝ)) ≤
        1 + Real.log (X0 : ℝ) :=
    hreciprocal.trans
      (Erdos390.Full.FriableAsymptotic.harmonic_Ioc_le
        (z := 0) (y := X0))
  unfold tangentCanonicalExceptionalLengthSum
  calc
    (∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (((tangentBroadUpper n K h / (u * b) -
          n / (v * b) : ℕ) : ℝ))) ≤
      ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (2 * (n : ℝ) / (u : ℝ)) * (1 / (b : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = (2 * (n : ℝ) / (u : ℝ)) *
        ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
          1 / (b : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ (2 * (n : ℝ) / (u : ℝ)) *
        (1 + Real.log (X0 : ℝ)) :=
      mul_le_mul_of_nonneg_left hharmonic (by positivity)

/-- Normalizing the harmonic length sum by `n / u` removes the endpoint
scale exactly. -/
theorem tangentCanonicalExceptionalLengthSum_normalized_le_harmonic
    {n K h X0 u v : ℕ} (hn : 0 < n) (hu : 0 < u) :
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      2 * (1 + Real.log (X0 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  calc
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      (u : ℝ) / (n : ℝ) *
        ((2 * (n : ℝ) / (u : ℝ)) *
          (1 + Real.log (X0 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (tangentCanonicalExceptionalLengthSum_le_harmonic hu)
        (div_nonneg huR.le hnR.le)
    _ = 2 * (1 + Real.log (X0 : ℝ)) := by
      field_simp [hnR.ne', huR.ne']

/-! ## Moving-scale negligibility -/

/-- The paper smoothness cutoff `yNat` is `o(n)`.  We derive this from the already
audited stronger estimate `yNat^2 = o(n/log n)`. -/
theorem tangentPaper_yNat_div_self_tendsto_zero :
    Tendsto (fun n : ℕ ↦ (yNat n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := fun n : ℕ ↦ (yNat n : ℝ) ^ 2 / secondOrderScale n)
  · filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  · filter_upwards [eventually_ge_atTop 3] with n hn
    have hnR : (0 : ℝ) < n := by positivity
    have hL : 1 ≤ L n := by
      rw [L]
      have hnCast : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have hexp : Real.exp 1 ≤ (n : ℝ) :=
        Real.exp_one_lt_three.le.trans hnCast
      exact (Real.le_log_iff_exp_le hnR).2 hexp
    have hyOneNat : 1 ≤ yNat n := by
      rw [yNat]
      apply Nat.le_floor
      rw [y]
      have hnOneR : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show 1 ≤ n by omega)
      simpa only [Nat.cast_one] using
        Real.one_le_rpow hnOneR
          (by norm_num : (0 : ℝ) ≤ 2 / 9)
    have hyOne : (1 : ℝ) ≤ yNat n := by exact_mod_cast hyOneNat
    have hySq : (yNat n : ℝ) ≤ (yNat n : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((yNat n : ℝ) - 1)]
    have hySqL : (yNat n : ℝ) ^ 2 ≤
        (yNat n : ℝ) ^ 2 * L n := by
      exact le_mul_of_one_le_right (sq_nonneg _) hL
    have hidentity :
        (yNat n : ℝ) ^ 2 / secondOrderScale n =
          (yNat n : ℝ) ^ 2 * L n / (n : ℝ) := by
      unfold secondOrderScale
      change (yNat n : ℝ) ^ 2 / ((n : ℝ) / L n) = _
      have hLPos : 0 < L n :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL
      field_simp [hnR.ne', hLPos.ne']
    rw [hidentity]
    exact div_le_div_of_nonneg_right (hySq.trans hySqL) hnR.le
  · exact yNat_sq_div_secondOrderScale_tendsto_zero

/-- The sharp paper guard deletion, even after multiplication by the largest
permitted label, is `o(n)`. -/
theorem tangentPaperSharpDeletion_mul_yNat_div_self_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
          (yNat n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
  have hmodelLittle :
      (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 * L n) =o[atTop]
        (fun n : ℕ ↦ (n : ℝ)) := by
    apply (isLittleO_iff_tendsto' ?_).mpr
    · apply yNat_sq_div_secondOrderScale_tendsto_zero.congr'
      filter_upwards [eventually_gt_atTop 1] with n hn
      have hnR : (0 : ℝ) < n := by positivity
      have hL : 0 < L n := L_pos hn
      unfold secondOrderScale
      rw [show Real.log (n : ℝ) = L n by rfl]
      field_simp [hnR.ne', hL.ne']
    · filter_upwards [eventually_gt_atTop 0] with n hn hzero
      have hnNe : (n : ℝ) ≠ 0 := by positivity
      exact (hnNe hzero).elim
  have hproductRaw :=
    bankPaperSharpMarkerBudget_isBigO_yNat_mul_L.mul
      (isBigO_refl (fun n : ℕ ↦ (yNat n : ℝ)) atTop)
  have hproduct :
      (fun n : ℕ ↦
        (bankPaperSharpMarkerBudget n : ℝ) * (yNat n : ℝ))
        =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2 * L n) := by
    apply hproductRaw.congr'
    · exact Eventually.of_forall fun _n ↦ rfl
    · exact Eventually.of_forall fun _n ↦ by ring
  have hbudget : Tendsto
      (fun n : ℕ ↦
        ((bankPaperSharpMarkerBudget n : ℝ) * (yNat n : ℝ)) /
          (n : ℝ)) atTop (nhds 0) :=
    (hproduct.trans_isLittleO hmodelLittle).tendsto_div_nhds_zero
  have hone := tangentPaper_yNat_div_self_tendsto_zero.const_mul (4 : ℝ)
  have hbudgetFour := hbudget.const_mul (4 : ℝ)
  have hsum : Tendsto
      (fun n : ℕ ↦
        4 * ((yNat n : ℝ) / (n : ℝ)) +
          4 * (((bankPaperSharpMarkerBudget n : ℝ) * (yNat n : ℝ)) /
            (n : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using hone.add hbudgetFour
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  push_cast
  ring

/-! ## Eventual exceptional-loss absorption -/

/-- The canonical Mertens/Selberg main term is a fixed small fraction of the
head gap under the one-time `deltaStar` choice.  The constant `80` is a
conservative closed replacement for the paper's implicit sieve constant. -/
theorem eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
    {W : ℕ} {r0 deltaStar : ℝ}
    (hdelta : 0 < deltaStar)
    (hsmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ K h u v : ℕ, 0 < u →
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalLengthSum n K h
              (tangentPaperExceptionalCutoff deltaStar n) u v *
            (tangentSelbergCanonicalMainConstant /
              Real.log (yNat n : ℝ))) ≤
        tangentPaperHeadGap W r0 / 4 := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdeltaL := hLTop.eventually
    (eventually_ge_atTop ((1 + Real.log 2) / deltaStar))
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      hdeltaL] with n hn hlogY hLn
  intro K h u v hu
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hL : 0 < L n := L_pos (by omega)
  have hdeltaLDominates :
      1 + Real.log 2 ≤ deltaStar * L n := by
    have h := (div_le_iff₀ hdelta).mp hLn
    simpa only [mul_comm] using h
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL).trans_le hlogY
  have hcutLog := tangentPaperExceptionalCutoff_log_le hdelta.le
    (show 1 ≤ n by omega)
  have hlength :=
    tangentCanonicalExceptionalLengthSum_normalized_le_harmonic
      (K := K) (h := h) (X0 := tangentPaperExceptionalCutoff deltaStar n)
      (v := v) hnPos hu
  have hlength' :
      (u : ℝ) / (n : ℝ) *
          tangentCanonicalExceptionalLengthSum n K h
            (tangentPaperExceptionalCutoff deltaStar n) u v ≤
        4 * deltaStar * L n := by
    calc
      _ ≤ 2 *
          (1 + Real.log
            (tangentPaperExceptionalCutoff deltaStar n : ℝ)) := hlength
      _ ≤ 2 * (1 + (deltaStar * L n + Real.log 2)) := by
        gcongr
      _ ≤ 4 * deltaStar * L n := by
        nlinarith
  have hinv : 1 / Real.log (yNat n : ℝ) ≤
      1 / ((1 / 5 : ℝ) * L n) :=
    one_div_le_one_div_of_le
      (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hL) hlogY
  have hcoefficient :
      tangentSelbergCanonicalMainConstant / Real.log (yNat n : ℝ) ≤
        5 * tangentSelbergCanonicalMainConstant / L n := by
    calc
      tangentSelbergCanonicalMainConstant / Real.log (yNat n : ℝ) =
          tangentSelbergCanonicalMainConstant *
            (1 / Real.log (yNat n : ℝ)) := by ring
      _ ≤ tangentSelbergCanonicalMainConstant *
          (1 / ((1 / 5 : ℝ) * L n)) :=
        mul_le_mul_of_nonneg_left hinv
          tangentSelbergCanonicalMainConstant_pos.le
      _ = 5 * tangentSelbergCanonicalMainConstant / L n := by
        field_simp [hL.ne']
  have hlengthNonneg : 0 ≤
      (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h
          (tangentPaperExceptionalCutoff deltaStar n) u v := by
    apply mul_nonneg (div_nonneg huR.le hnR.le)
    unfold tangentCanonicalExceptionalLengthSum
    apply Finset.sum_nonneg
    intro b _hb
    exact Nat.cast_nonneg _
  calc
    (u : ℝ) / (n : ℝ) *
        (tangentCanonicalExceptionalLengthSum n K h
            (tangentPaperExceptionalCutoff deltaStar n) u v *
          (tangentSelbergCanonicalMainConstant /
            Real.log (yNat n : ℝ))) =
      ((u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h
          (tangentPaperExceptionalCutoff deltaStar n) u v) *
        (tangentSelbergCanonicalMainConstant /
          Real.log (yNat n : ℝ)) := by ring
    _ ≤ (4 * deltaStar * L n) *
        (5 * tangentSelbergCanonicalMainConstant / L n) :=
      mul_le_mul hlength' hcoefficient
        (div_nonneg tangentSelbergCanonicalMainConstant_pos.le hlogYPos.le)
        (hlengthNonneg.trans hlength')
    _ = 20 * tangentSelbergCanonicalMainConstant * deltaStar := by
      field_simp [hL.ne']
      ring
    _ ≤ tangentPaperHeadGap W r0 / 4 := by linarith

/-- The literal `X0*yNat^4/n` Lambda-squared remainder is uniformly
negligible on the `n/u` scale when `deltaStar<1/18`. -/
theorem eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
    {W : ℕ} {r0 deltaStar : ℝ}
    (hdeltaNonneg : 0 ≤ deltaStar)
    (hdelta : deltaStar < 1 / 18)
    (hgap : 0 < tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℕ, 0 < u →
      (u : ℝ) / (n : ℝ) *
          tangentCanonicalExceptionalRemainder
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u ≤
        tangentPaperHeadGap W r0 / 16 := by
  have hlambdaSq : 0 < tangentSelbergCanonicalLambdaConstant ^ 2 :=
    sq_pos_of_pos tangentSelbergCanonicalLambdaConstant_pos
  have hepsilon : 0 <
      tangentPaperHeadGap W r0 /
        (32 * tangentSelbergCanonicalLambdaConstant ^ 2) := by positivity
  have hpowerSmall :=
    (tangentExceptional_remainderPower_tendsto_zero hdelta).eventually
      (eventually_lt_nhds hepsilon)
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLfive := hLTop.eventually (eventually_ge_atTop (5 : ℝ))
  filter_upwards
    [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      hpowerSmall, hLfive] with n hn hlogY hpower hLnFive
  intro u hu
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by positivity
  have hL : 0 < L n := L_pos (by omega)
  have hlogYOne : 1 ≤ Real.log (yNat n : ℝ) := by
    nlinarith [hlogY]
  have hpowerOne : (1 : ℝ) ≤ (n : ℝ) ^ deltaStar :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ n by omega))
      hdeltaNonneg
  have hcut :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
        2 * (n : ℝ) ^ deltaStar := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
          (n : ℝ) ^ deltaStar + 1 :=
        (tangentPaperExceptionalCutoff_cast_lt_add_one
          deltaStar n).le
      _ ≤ 2 * (n : ℝ) ^ deltaStar := by linarith
  have hyFour := tangentExceptional_yNat_pow_four_le n
  have hpowerIdentity :
      (n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ) / (n : ℝ) =
        (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
    rw [← Real.rpow_add hnR]
    calc
      (n : ℝ) ^ (deltaStar + 8 / 9) / (n : ℝ) =
          (n : ℝ) ^ (deltaStar + 8 / 9) /
            (n : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ (deltaStar + 8 / 9 - 1) :=
        (Real.rpow_sub hnR (deltaStar + 8 / 9) 1).symm
  have hproduct :
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ) ≤
        2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
    calc
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ) ≤
        (2 * (n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ)) /
          (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul hcut hyFour (by positivity) (by positivity)) hnR.le
      _ = 2 *
          ((n : ℝ) ^ deltaStar * (n : ℝ) ^ (8 / 9 : ℝ) /
            (n : ℝ)) := by ring
      _ = 2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1) := by
        rw [hpowerIdentity]
  have hdenom : 1 ≤ Real.log (yNat n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (Real.log (yNat n : ℝ) - 1)]
  have hnormalized := tangentCanonicalExceptionalRemainder_normalized_le
    (X0 := tangentPaperExceptionalCutoff deltaStar n) (y := yNat n)
      hnPos hu
  calc
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalRemainder
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u ≤
      tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 / (n : ℝ)) /
            Real.log (yNat n : ℝ) ^ 2 := hnormalized
    _ ≤ tangentSelbergCanonicalLambdaConstant ^ 2 *
        (2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1)) /
          Real.log (yNat n : ℝ) ^ 2 := by
      gcongr
    _ ≤ tangentSelbergCanonicalLambdaConstant ^ 2 *
        (2 * (n : ℝ) ^ (deltaStar + 8 / 9 - 1)) := by
      exact div_le_self (mul_nonneg (sq_nonneg _) (by positivity)) hdenom
    _ ≤ tangentSelbergCanonicalLambdaConstant ^ 2 *
        (2 * (tangentPaperHeadGap W r0 /
          (32 * tangentSelbergCanonicalLambdaConstant ^ 2))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower.le (by norm_num)) (sq_nonneg _)
    _ = tangentPaperHeadGap W r0 / 16 := by
      field_simp [tangentSelbergCanonicalLambdaConstant_pos.ne']
      norm_num

/-! ## The fixed-head candidate at the paper endpoints -/

/-- Pointwise normalized candidate estimate.  The two hypotheses are exactly
the moving `K*h` loss and the fixed-modulus/floor loss; the eventual theorem
below proves both from the literal paper scales. -/
theorem tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    {W n K h u v : ℕ} {r0 : ℝ}
    (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (hr0one : 1 < r0) (hr0two : r0 < 2)
    (hratio : (u : ℝ) / (v : ℝ) ≤ r0)
    (htail :
      roughHeadDensity W *
          (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤
        tangentPaperHeadGap W r0 / 16)
    (hhead :
      (u : ℝ) / (n : ℝ) *
          (roughHeadDensity W + (roughHeadModulus W : ℝ)) ≤
        tangentPaperHeadGap W r0 / 16) :
    n / v ≤ tangentBroadUpper n K h / u ∧
      3 * tangentPaperHeadGap W r0 / 4 ≤
        (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K h u v := by
  let d : ℝ := roughHeadDensity W
  let P : ℝ := roughHeadModulus W
  let gap : ℝ := tangentPaperHeadGap W r0
  have hd : 0 < d := by
    dsimp only [d]
    exact roughHeadDensity_pos W
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast roughHeadModulus_pos W
  have hgap : 0 < gap := by
    dsimp only [gap, tangentPaperHeadGap]
    exact mul_pos (roughHeadDensity_pos W) (sub_pos.mpr hr0two)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have htail' :
      d * (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤ gap / 16 := by
    simpa only [d, gap] using htail
  have hhead' :
      (u : ℝ) / (n : ℝ) * (d + P) ≤ gap / 16 := by
    simpa only [d, P, gap] using hhead
  have hgapIdentity : gap = d * (2 - r0) := by
    simp only [gap, d, tangentPaperHeadGap]
  have htailRatio :
      (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤ (2 - r0) / 16 := by
    refine le_of_mul_le_mul_left ?_ hd
    calc
      d * (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤ gap / 16 := htail'
      _ = d * ((2 - r0) / 16) := by
        rw [hgapIdentity]
        ring
  have huRatio : (u : ℝ) / (n : ℝ) ≤ (2 - r0) / 16 := by
    have hscaled :
        (u : ℝ) / (n : ℝ) * d ≤ gap / 16 := by
      exact (mul_le_mul_of_nonneg_left
        (show d ≤ d + P by linarith) (div_nonneg huR.le hnR.le)).trans hhead'
    refine le_of_mul_le_mul_right ?_ hd
    calc
      (u : ℝ) / (n : ℝ) * d ≤ gap / 16 := hscaled
      _ = (2 - r0) / 16 * d := by
        rw [hgapIdentity]
        ring
  have htailLtOne : (((K * h : ℕ) : ℝ) / (n : ℝ)) < 1 :=
    htailRatio.trans_lt (by linarith)
  have hKhLt : K * h < n := by
    have hcast : (((K * h : ℕ) : ℝ)) < (n : ℝ) :=
      (div_lt_one hnR).mp htailLtOne
    exact_mod_cast hcast
  have hKhTwo : K * h ≤ 2 * n := by omega
  have hbroadCast : (tangentBroadUpper n K h : ℝ) =
      2 * (n : ℝ) - ((K * h : ℕ) : ℝ) := by
    unfold tangentBroadUpper
    rw [Nat.cast_sub hKhTwo]
    push_cast
    ring
  have hratioScaled :
      (n : ℝ) / (v : ℝ) ≤
        r0 * ((n : ℝ) / (u : ℝ)) := by
    calc
      (n : ℝ) / (v : ℝ) =
          ((n : ℝ) / (u : ℝ)) *
            ((u : ℝ) / (v : ℝ)) := by
        field_simp [huR.ne', hvR.ne']
      _ ≤ ((n : ℝ) / (u : ℝ)) * r0 :=
        mul_le_mul_of_nonneg_left hratio
          (div_nonneg hnR.le huR.le)
      _ = r0 * ((n : ℝ) / (u : ℝ)) := by ring
  have hcoefficient :
      r0 < 2 -
          (((K * h : ℕ) : ℝ) / (n : ℝ)) -
          ((u : ℝ) / (n : ℝ)) := by
    nlinarith
  have hrealGap :
      r0 * ((n : ℝ) / (u : ℝ)) <
        (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 := by
    calc
      r0 * ((n : ℝ) / (u : ℝ)) <
          ((n : ℝ) / (u : ℝ)) *
            (2 - (((K * h : ℕ) : ℝ) / (n : ℝ)) -
              ((u : ℝ) / (n : ℝ))) := by
        simpa only [mul_comm] using
          mul_lt_mul_of_pos_left hcoefficient (div_pos hnR huR)
      _ = (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 := by
        rw [hbroadCast]
        field_simp [hnR.ne', huR.ne']
  have hquotientLower :
      (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 <
        ((tangentBroadUpper n K h / u : ℕ) : ℝ) := by
    rw [sub_lt_iff_lt_add]
    apply (div_lt_iff₀ huR).2
    have hnat := (Nat.div_lt_iff_lt_mul hu).mp
      (Nat.lt_succ_self (tangentBroadUpper n K h / u))
    exact_mod_cast hnat
  have hlowerQuotient :
      ((n / v : ℕ) : ℝ) ≤ (n : ℝ) / (v : ℝ) :=
    Nat.cast_div_le
  have hinterval : n / v ≤ tangentBroadUpper n K h / u := by
    have hcastInterval :
        ((n / v : ℕ) : ℝ) ≤
          ((tangentBroadUpper n K h / u : ℕ) : ℝ) :=
      (hlowerQuotient.trans_lt
        (hratioScaled.trans_lt (hrealGap.trans hquotientLower))).le
    exact_mod_cast hcastInterval
  have hsubLower :
      (2 - r0) * ((n : ℝ) / (u : ℝ)) -
          (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1 ≤
        (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hinterval]
    calc
      (2 - r0) * ((n : ℝ) / (u : ℝ)) -
          (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1 ≤
        (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 -
          (n : ℝ) / (v : ℝ) := by
        calc
          (2 - r0) * ((n : ℝ) / (u : ℝ)) -
              (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1 =
            (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 -
              r0 * ((n : ℝ) / (u : ℝ)) := by
                rw [hbroadCast]
                ring
          _ ≤ (tangentBroadUpper n K h : ℝ) / (u : ℝ) - 1 -
              (n : ℝ) / (v : ℝ) := by linarith
      _ ≤ ((tangentBroadUpper n K h / u : ℕ) : ℝ) -
          ((n / v : ℕ) : ℝ) := by
        linarith
  have halgebra :
      (u : ℝ) / (n : ℝ) *
          (d * ((2 - r0) * ((n : ℝ) / (u : ℝ)) -
              (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1) - P) =
        gap - d * (((K * h : ℕ) : ℝ) / (n : ℝ)) -
          (u : ℝ) / (n : ℝ) * (d + P) := by
    rw [hgapIdentity]
    field_simp [hnR.ne', huR.ne']
    ring
  constructor
  · exact hinterval
  · calc
      3 * gap / 4 ≤ gap - gap / 16 - gap / 16 := by linarith
      _ ≤ gap - d * (((K * h : ℕ) : ℝ) / (n : ℝ)) -
          (u : ℝ) / (n : ℝ) * (d + P) := by linarith
      _ = (u : ℝ) / (n : ℝ) *
          (d * ((2 - r0) * ((n : ℝ) / (u : ℝ)) -
              (((K * h : ℕ) : ℝ) / (u : ℝ)) - 1) - P) :=
        halgebra.symm
      _ ≤ (u : ℝ) / (n : ℝ) *
          (d * (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) - P) := by
        exact mul_le_mul_of_nonneg_left
          (sub_le_sub_right (mul_le_mul_of_nonneg_left hsubLower hd.le) P)
          (div_nonneg huR.le hnR.le)
      _ = (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K h u v := by
        simp only [tangentRoughHeadCandidateMain, d, P]

/-- With `h=ceil(c n/log n)`, the candidate main term retains three quarters
of the fixed head gap, uniformly over every permitted endpoint pair. -/
theorem eventually_tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    (W K : ℕ) {c r0 : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ u v : ℕ,
      0 < u → 0 < v → u ≤ yNat n →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      n / v ≤ tangentBroadUpper n K (upperTailLength c n) / u ∧
        3 * tangentPaperHeadGap W r0 / 4 ≤
          (u : ℝ) / (n : ℝ) *
            tangentRoughHeadCandidateMain
              W n K (upperTailLength c n) u v := by
  let d : ℝ := roughHeadDensity W
  let P : ℝ := roughHeadModulus W
  let gap : ℝ := tangentPaperHeadGap W r0
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact tangentPaperHeadGap_pos W (hr0three.trans (by norm_num))
  have htailT : Tendsto
      (fun n : ℕ ↦ d *
        (((K * upperTailLength c n : ℕ) : ℝ) / (n : ℝ)))
      atTop (nhds 0) := by
    have h := (upperTailLength_ratio_tendsto_zero hc).const_mul
      (d * (K : ℝ))
    simpa only [mul_zero] using h.congr' (Eventually.of_forall fun n ↦ by
      push_cast
      ring)
  have hheadT : Tendsto
      (fun n : ℕ ↦
        ((yNat n : ℝ) / (n : ℝ)) * (d + P))
      atTop (nhds 0) := by
    have h := tangentPaper_yNat_div_self_tendsto_zero.const_mul (d + P)
    simpa only [mul_zero, zero_mul, mul_comm] using h
  have htailSmall := htailT.eventually
    (eventually_lt_nhds (div_pos hgap (by norm_num : (0 : ℝ) < 16)))
  have hheadSmall := hheadT.eventually
    (eventually_lt_nhds (div_pos hgap (by norm_num : (0 : ℝ) < 16)))
  filter_upwards [eventually_gt_atTop 0, htailSmall, hheadSmall]
    with n hn htail hhead
  intro u v hu hv huy hratio
  have hd : 0 < d := by
    dsimp only [d]
    exact roughHeadDensity_pos W
  have hP : 0 < P := by
    dsimp only [P]
    exact_mod_cast roughHeadModulus_pos W
  have huBound :
      (u : ℝ) / (n : ℝ) * (d + P) ≤
        (yNat n : ℝ) / (n : ℝ) * (d + P) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : (u : ℝ) / (n : ℝ) ≤
        (yNat n : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast huy) hnR.le
    exact mul_le_mul_of_nonneg_right hdiv (add_nonneg hd.le hP.le)
  apply tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    (W := W) hn hu hv hr0one (hr0three.trans (by norm_num)) hratio
  · simpa only [d, gap] using htail.le
  · simpa only [d, P, gap] using huBound.trans hhead.le

/-! ## The literal candidate floor absorbs every canonical loss -/

/-- Section 9's literal parameter choices discharge the last arithmetic
comparison left open by `TangentCanonicalCleanListLower`.  The conclusion is
the exact natural-number inequality consumed by the canonical clean-list
bridge; neither it nor a disguised copy is assumed.

The bookkeeping reserves `1/8` of the head gap for the effective-card
ceiling, `3/8` for the canonical exceptional ceiling, and `1/16` for the
sharp deterministic deletion.  Their total `9/16` is strictly below the
`3/4` retained by the fixed-head candidate. -/
theorem eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses
    (W K : ℕ) {c r0 deltaStar : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ u v : ℕ,
      0 < u → 0 < v → v ≤ u → u ≤ yNat n →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      n / v ≤ tangentBroadUpper n K (upperTailLength c n) / u ∧
        tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n v +
            tangentCanonicalExceptionalNatUpper n K
              (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n)
              (yNat n) u v +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K
            (upperTailLength c n) u v := by
  let gap : ℝ := tangentPaperHeadGap W r0
  let density : ℝ := tangentPaperCleanListDensity W r0
  have hgap : 0 < gap := by
    dsimp only [gap]
    exact tangentPaperHeadGap_pos W (hr0three.trans (by norm_num))
  have hdensity : density = gap / 16 := by
    simp only [density, gap, tangentPaperCleanListDensity]
  have hdensityPos : 0 < density := by
    rw [hdensity]
    positivity
  have hcandidate :=
    eventually_tangentRoughHeadCandidateMain_normalized_ge_three_quarters
      W K hc hr0one hr0three
  have hexceptionalMain :=
    eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
      hdelta hmainSmall
  have hexceptionalRemainder :=
    eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
      hdelta.le hdeltaUpper (by simpa only [gap] using hgap)
  have hySmall := tangentPaper_yNat_div_self_tendsto_zero.eventually
    (eventually_lt_nhds (div_pos hgap (by norm_num : (0 : ℝ) < 64)))
  have hsharpSmall :=
    tangentPaperSharpDeletion_mul_yNat_div_self_tendsto_zero.eventually
      (eventually_lt_nhds
        (div_pos hgap (by norm_num : (0 : ℝ) < 16)))
  filter_upwards
    [hcandidate, hexceptionalMain, hexceptionalRemainder,
      hySmall, hsharpSmall, eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hcandidateN hexceptionalMainN hexceptionalRemainderN
        hySmallN hsharpSmallN hn hlogY
  intro u v hu hv hvu huy hratio
  have hnPos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnPos
  have huR : (0 : ℝ) < u := by exact_mod_cast hu
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hfactorPos : 0 < (u : ℝ) / (n : ℝ) := div_pos huR hnR
  have hfactorY :
      (u : ℝ) / (n : ℝ) ≤ (yNat n : ℝ) / (n : ℝ) :=
    div_le_div_of_nonneg_right (by exact_mod_cast huy) hnR.le
  have hfactorSmall :
      (u : ℝ) / (n : ℝ) ≤ gap / 64 := by
    exact hfactorY.trans (by simpa only [gap] using hySmallN.le)
  have hcandidateUV := hcandidateN u v hu hv huy hratio
  refine ⟨hcandidateUV.1, ?_⟩

  have heffectiveArg :
      0 ≤ density * (n : ℝ) / (v : ℝ) := by positivity
  have heffectiveCeil :
      (tangentEffectiveLowerCard density n v : ℝ) ≤
        density * (n : ℝ) / (v : ℝ) + 1 := by
    unfold tangentEffectiveLowerCard
    exact (Nat.ceil_lt_add_one heffectiveArg).le
  have heffectiveNormalized :
      (u : ℝ) / (n : ℝ) *
          (tangentEffectiveLowerCard density n v : ℝ) ≤
        gap / 8 := by
    calc
      (u : ℝ) / (n : ℝ) *
          (tangentEffectiveLowerCard density n v : ℝ) ≤
          (u : ℝ) / (n : ℝ) *
            (density * (n : ℝ) / (v : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left heffectiveCeil hfactorPos.le
      _ = density * ((u : ℝ) / (v : ℝ)) +
          (u : ℝ) / (n : ℝ) := by
        field_simp [hnR.ne', hvR.ne']
      _ ≤ density * r0 + gap / 64 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hratio hdensityPos.le)
          hfactorSmall
      _ ≤ gap / 8 := by
        rw [hdensity]
        calc
          gap / 16 * r0 + gap / 64 ≤
              gap / 16 * (3 / 2 : ℝ) + gap / 64 :=
            add_le_add_left
              (mul_le_mul_of_nonneg_left hr0three.le
                (div_nonneg hgap.le (by norm_num : (0 : ℝ) ≤ 16))) _
          _ ≤ gap / 8 := by linarith

  have hLPos : 0 < L n := L_pos (by omega)
  have hlogYPos : 0 < Real.log (yNat n : ℝ) :=
    (mul_pos (by norm_num : (0 : ℝ) < 1 / 5) hLPos).trans_le hlogY
  have hlengthNonneg : 0 ≤
      tangentCanonicalExceptionalLengthSum n K (upperTailLength c n)
        (tangentPaperExceptionalCutoff deltaStar n) u v := by
    unfold tangentCanonicalExceptionalLengthSum
    positivity
  have hremainderNonneg : 0 ≤
      tangentCanonicalExceptionalRemainder
        (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u := by
    unfold tangentCanonicalExceptionalRemainder
    positivity
  have hexceptionalUpperNonneg : 0 ≤
      tangentCanonicalExceptionalUpper n K (upperTailLength c n)
        (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v := by
    unfold tangentCanonicalExceptionalUpper
    exact add_nonneg
      (mul_nonneg hlengthNonneg
        (div_nonneg tangentSelbergCanonicalMainConstant_pos.le
          hlogYPos.le))
      hremainderNonneg
  have hexceptionalReal :
      (u : ℝ) / (n : ℝ) *
          tangentCanonicalExceptionalUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v ≤
        5 * gap / 16 := by
    have hmain := hexceptionalMainN K (upperTailLength c n) u v hu
    have hremainder := hexceptionalRemainderN u hu
    unfold tangentCanonicalExceptionalUpper
    calc
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalLengthSum n K (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n) u v *
                (tangentSelbergCanonicalMainConstant /
                  Real.log (yNat n : ℝ)) +
            tangentCanonicalExceptionalRemainder
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u) =
          (u : ℝ) / (n : ℝ) *
              (tangentCanonicalExceptionalLengthSum n K
                (upperTailLength c n)
                (tangentPaperExceptionalCutoff deltaStar n) u v *
                  (tangentSelbergCanonicalMainConstant /
                    Real.log (yNat n : ℝ))) +
            (u : ℝ) / (n : ℝ) *
              tangentCanonicalExceptionalRemainder
                (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u := by
        ring
      _ ≤ gap / 4 + gap / 16 := by
        exact add_le_add
          (by simpa only [gap] using hmain)
          (by simpa only [gap] using hremainder)
      _ = 5 * gap / 16 := by ring
  have hexceptionalCeil :
      (tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v : ℝ) ≤
        tangentCanonicalExceptionalUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v + 1 := by
    unfold tangentCanonicalExceptionalNatUpper
    exact (Nat.ceil_lt_add_one hexceptionalUpperNonneg).le
  have hexceptionalNormalized :
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v : ℝ) ≤
        3 * gap / 8 := by
    calc
      (u : ℝ) / (n : ℝ) *
          (tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v : ℝ) ≤
          (u : ℝ) / (n : ℝ) *
            (tangentCanonicalExceptionalUpper n K (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v + 1) :=
        mul_le_mul_of_nonneg_left hexceptionalCeil hfactorPos.le
      _ = (u : ℝ) / (n : ℝ) *
            tangentCanonicalExceptionalUpper n K (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v +
          (u : ℝ) / (n : ℝ) := by ring
      _ ≤ 5 * gap / 16 + gap / 64 :=
        add_le_add hexceptionalReal hfactorSmall
      _ ≤ 3 * gap / 8 := by linarith

  have hsharpNormalized :
      (u : ℝ) / (n : ℝ) *
          ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
        gap / 16 := by
    calc
      (u : ℝ) / (n : ℝ) *
          ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) =
        ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
            (u : ℝ) / (n : ℝ) := by ring
      _ ≤ ((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
            (yNat n : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast huy)
            (Nat.cast_nonneg _)) hnR.le
      _ ≤ gap / 16 := by
        exact (by simpa only [gap] using hsharpSmallN.le)

  let effective : ℕ := tangentEffectiveLowerCard density n v
  let exceptional : ℕ :=
    tangentCanonicalExceptionalNatUpper n K (upperTailLength c n)
      (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v
  let deletion : ℕ := 4 + 4 * bankPaperSharpMarkerBudget n
  have hlossCast :
      (((effective + exceptional + 4 +
          4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ)) =
        (effective : ℝ) + (exceptional : ℝ) + (deletion : ℝ) := by
    dsimp only [deletion]
    push_cast
    ring
  have hlossNormalized :
      (u : ℝ) / (n : ℝ) *
          ((effective + exceptional + 4 +
            4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
        9 * gap / 16 := by
    rw [hlossCast]
    calc
      (u : ℝ) / (n : ℝ) *
          ((effective : ℝ) + (exceptional : ℝ) + (deletion : ℝ)) =
        (u : ℝ) / (n : ℝ) * (effective : ℝ) +
          (u : ℝ) / (n : ℝ) * (exceptional : ℝ) +
          (u : ℝ) / (n : ℝ) * (deletion : ℝ) := by ring
      _ ≤ gap / 8 + 3 * gap / 8 + gap / 16 := by
        exact add_le_add
          (add_le_add
            (by simpa only [effective] using heffectiveNormalized)
            (by simpa only [exceptional] using hexceptionalNormalized))
          (by simpa only [deletion] using hsharpNormalized)
      _ = 9 * gap / 16 := by ring
  have hlossBelowCandidateNormalized :
      (u : ℝ) / (n : ℝ) *
          ((effective + exceptional + 4 +
            4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
        (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K (upperTailLength c n) u v := by
    exact hlossNormalized.trans
      ((by nlinarith : 9 * gap / 16 ≤ 3 * gap / 4).trans
        (by simpa only [gap] using hcandidateUV.2))
  have hlossBelowCandidate :
      ((effective + exceptional + 4 +
        4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) ≤
          tangentRoughHeadCandidateMain W n K (upperTailLength c n) u v :=
    le_of_mul_le_mul_left hlossBelowCandidateNormalized hfactorPos
  change effective + exceptional + 4 + 4 * bankPaperSharpMarkerBudget n ≤
    tangentRoughHeadCandidateLower W n K (upperTailLength c n) u v
  unfold tangentRoughHeadCandidateLower
  apply Nat.le_floor
  exact hlossBelowCandidate.trans (le_max_right 0 _)

/-! ## Paper-facing clean-list theorem with no arithmetic loss premise -/

namespace BankPaperRealization

/-- The sharp-bank clean-list wrapper with all Section 9 numerical choices
fixed literally.  In contrast with the preceding canonical wrapper, this
wrapper has no candidate interval or candidate-floor-versus-loss premise:
both are supplied uniformly by
`eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses`. -/
theorem eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed
    (W K : ℕ) {tailC r0 deltaStar : ℝ}
    (htailC : 0 < tailC) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (anchorC : ℝ) (depth M u v : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate anchorC depth n
          left right changed)
        (fixedExceptional : Finset ℕ),
      fixedExceptional ⊆ Finset.Ioc (2 * n) M →
      2 ≤ W → 2 * depth + 1 ≤ W →
      W < v → v ≤ u → u ≤ yNat n →
      yNat n < centralAnchorCutoff depth n →
      u.Prime → v.Prime →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      0 < tangentEffectiveLowerCard
        (tangentPaperCleanListDensity W r0) n v ∧
      tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v ≤
        (tangentCleanCommonMultiplierList n K (upperTailLength tailC n)
          (roughHeadModulus W)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional)).card ∧
      tangentPaperCleanListDensity W r0 * n ≤
        (tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v : ℝ) * u ∧
      tangentPaperCleanListDensity W r0 * n ≤
        (tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v : ℝ) * v := by
  have hcanonical :=
    eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical
  have habsorption :=
    eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses
      W K htailC hr0one hr0three hdelta hdeltaUpper hmainSmall
  filter_upwards [hcanonical, habsorption]
    with n hcanonicalN habsorptionN
  intro anchorC depth M u v left right changed R certificate fixedExceptional
    hfixedTail hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime hratio
  have hdensity : 0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W (hr0three.trans (by norm_num))
  have harithmetic :=
    habsorptionN u v huPrime.pos hvPrime.pos hvu huy hratio
  exact hcanonicalN anchorC depth M W K (upperTailLength tailC n)
    (tangentPaperExceptionalCutoff deltaStar n) u v left right changed
    R certificate fixedExceptional (tangentPaperCleanListDensity W r0)
    hfixedTail hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
    hdensity harithmetic.1 harithmetic.2

end BankPaperRealization

end

end Erdos390.WholePaper
