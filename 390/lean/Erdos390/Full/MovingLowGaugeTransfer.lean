import Erdos390.Full.PositiveCellTransfer
import Erdos390.Full.MovingLowMomentQuadrature

/-!
# Moving-low arithmetic/continuum gauge transfer

This file isolates the normalization which is delicate at the moving low
cell.  An additive estimate for the arithmetic center is not enough because
the center itself tends to zero.  We first prove a quantitative relative
center estimate from separate estimates for `H` and `H * alpha`.  We then
write the sharp conjugate of the weighted gauge projection exactly and
compare two such projections through their normalized weights
`omega_j = H_j * alpha_j^2`.

No limiting mesh, covariance gap, or inverse is assumed in this module.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.MovingLowGaugeTransfer

open Erdos390.Lemma84
open PositiveCellTransfer
open PrimeSums
open PrimeBandQuadrature
open MovingLowMomentQuadrature

section RelativeCenter

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : ArithmeticBandGeometry.Partition n W Band}

/-- Dividing the center estimate by the continuum center is legitimate and
keeps every denominator visible.  This is the exact `/ alpha_0` step which
cannot be replaced by an additive `o(1)` assertion. -/
theorem center_ratio_error_le_of_mass_moment_errors
    (E : PositiveCellTransfer.IntervalCertificate P) (j : Band)
    {eMass eMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |P.mass j * P.center j - E.continuumMoment j| ≤ eMoment)
    (hContinuumMass : E.continuumMass j ≠ 0)
    (hContinuumCenter : E.continuumCenter j ≠ 0) :
    |P.center j / E.continuumCenter j - 1| ≤
      (eMoment / P.mass j +
        |E.continuumMoment j| * eMass /
          (P.mass j * |E.continuumMass j|)) /
        |E.continuumCenter j| := by
  apply abs_div_sub_one_le hContinuumCenter
  exact E.center_error_le_of_mass_moment_errors j
    hMass hMoment hContinuumMass

/-- If the mass error is at most half of the positive continuum mass, the
preceding exact bound simplifies to the scale-transparent estimate

`relative center error <= 2 eMoment / M_c + 2 eMass / H_c`.

At the moving low cell `M_c` stays bounded away from zero, while `H_c`
grows; hence an ambient-logarithm error for the first moment and a bounded
mass error both become small after division by `alpha_0 = M_c / H_c`. -/
theorem center_ratio_error_le_two_errors
    (E : PositiveCellTransfer.IntervalCertificate P) (j : Band)
    {eMass eMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |P.mass j * P.center j - E.continuumMoment j| ≤ eMoment)
    (hContinuumMass : 0 < E.continuumMass j)
    (hContinuumMoment : 0 < E.continuumMoment j)
    (hMassSmall : eMass ≤ E.continuumMass j / 2) :
    |P.center j / E.continuumCenter j - 1| ≤
      2 * eMoment / E.continuumMoment j +
        2 * eMass / E.continuumMass j := by
  have heMass : 0 ≤ eMass := (abs_nonneg _).trans hMass
  have heMoment : 0 ≤ eMoment := (abs_nonneg _).trans hMoment
  have hmassLower : E.continuumMass j / 2 ≤ P.mass j := by
    have hleft : -eMass ≤ P.mass j - E.continuumMass j :=
      (abs_le.mp hMass).1
    linarith
  have hmass : 0 < P.mass j := P.data.mass_pos j
  have htwoMass : E.continuumMass j ≤ 2 * P.mass j := by linarith
  have hcenter : 0 < E.continuumCenter j := by
    unfold PositiveCellTransfer.IntervalCertificate.continuumCenter
    exact div_pos hContinuumMoment hContinuumMass
  have hraw := center_ratio_error_le_of_mass_moment_errors E j
    hMass hMoment (ne_of_gt hContinuumMass) (ne_of_gt hcenter)
  have hsimplify :
      (eMoment / P.mass j +
          |E.continuumMoment j| * eMass /
            (P.mass j * |E.continuumMass j|)) /
          |E.continuumCenter j| =
        eMoment * E.continuumMass j /
            (P.mass j * E.continuumMoment j) +
          eMass / P.mass j := by
    rw [abs_of_pos hContinuumMoment, abs_of_pos hContinuumMass,
      abs_of_pos hcenter]
    unfold PositiveCellTransfer.IntervalCertificate.continuumCenter
    field_simp [ne_of_gt hmass, ne_of_gt hContinuumMass,
      ne_of_gt hContinuumMoment]
  rw [hsimplify] at hraw
  have hfirst :
      eMoment * E.continuumMass j /
          (P.mass j * E.continuumMoment j) ≤
        2 * eMoment / E.continuumMoment j := by
    have hnum :
        eMoment * E.continuumMass j ≤
          eMoment * (2 * P.mass j) :=
      mul_le_mul_of_nonneg_left htwoMass heMoment
    calc
      eMoment * E.continuumMass j /
          (P.mass j * E.continuumMoment j) ≤
        (eMoment * (2 * P.mass j)) /
          (P.mass j * E.continuumMoment j) :=
        div_le_div_of_nonneg_right hnum
          (mul_pos hmass hContinuumMoment).le
      _ = 2 * eMoment / E.continuumMoment j := by
        field_simp [ne_of_gt hmass, ne_of_gt hContinuumMoment]
  have hsecond :
      eMass / P.mass j ≤ 2 * eMass / E.continuumMass j := by
    apply (div_le_div_iff₀ hmass hContinuumMass).2
    have hscaled := mul_le_mul_of_nonneg_left htwoMass heMass
    nlinarith
  exact hraw.trans (add_le_add hfirst hsecond)

/-- Endpoint-uniform unconditional quadrature for the actual arithmetic
moment `H_j * alpha_j`.  Unlike the older positive-cell bound, the numerator
on the right does not grow with the upper endpoint. -/
theorem exists_mass_mul_center_movingLow_quadrature_bound
    (E : PositiveCellTransfer.IntervalCertificate P) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ j : Band,
      X₀ ≤ E.lower j →
      |P.mass j * P.center j - E.continuumMoment j| ≤
        (2 * C / Real.log (E.lower j : ℝ) ^ 3 +
          C / (2 * Real.log (E.lower j : ℝ) ^ 2)) /
            |Real.log (ArithmeticModel.y n)| := by
  obtain ⟨C, hC, X₀, hbound⟩ :=
    exists_fullLogReciprocalSum_interval_uniform_error_bound
  refine ⟨C, hC, X₀, ?_⟩
  intro j hj
  have hlogy : 0 < Real.log (ArithmeticModel.y n) := by
    rw [Erdos390.Full.Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
  unfold PositiveCellTransfer.IntervalCertificate.continuumMoment
  rw [← sub_div, abs_div]
  exact div_le_div_of_nonneg_right
    (hbound (E.lower j) (E.upper j) hj (E.lower_le_upper j))
    (abs_pos.mpr (ne_of_gt hlogy)).le

/-- Fully explicit `/ alpha_j` conclusion after inserting the unconditional
PNT endpoint errors.  The only remaining hypotheses are elementary endpoint
geometry: positivity of the continuum mass/moment and the displayed
half-mass inequality. -/
theorem center_ratio_error_le_of_endpoint_quadrature
    (E : PositiveCellTransfer.IntervalCertificate P) (j : Band)
    {CMass CMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤
      5 * CMass / Real.log (E.lower j : ℝ) ^ 3)
    (hMoment : |P.mass j * P.center j - E.continuumMoment j| ≤
      (2 * CMoment / Real.log (E.lower j : ℝ) ^ 3 +
        CMoment / (2 * Real.log (E.lower j : ℝ) ^ 2)) /
          |Real.log (ArithmeticModel.y n)|)
    (hContinuumMass : 0 < E.continuumMass j)
    (hContinuumMoment : 0 < E.continuumMoment j)
    (hMassSmall :
      5 * CMass / Real.log (E.lower j : ℝ) ^ 3 ≤
        E.continuumMass j / 2) :
    |P.center j / E.continuumCenter j - 1| ≤
      2 * ((2 * CMoment / Real.log (E.lower j : ℝ) ^ 3 +
        CMoment / (2 * Real.log (E.lower j : ℝ) ^ 2)) /
          |Real.log (ArithmeticModel.y n)|) /
            E.continuumMoment j +
      2 * (5 * CMass / Real.log (E.lower j : ℝ) ^ 3) /
        E.continuumMass j := by
  exact center_ratio_error_le_two_errors E j hMass hMoment
    hContinuumMass hContinuumMoment hMassSmall

end RelativeCenter

section SharpProjection

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- The sharp projection weight from the paper. -/
def sharpWeight (H alpha : Band → ℝ) (j : Band) : ℝ :=
  H j * alpha j ^ 2

def sharpWeightTotal (H alpha : Band → ℝ) : ℝ :=
  ∑ j, sharpWeight H alpha j

def weightedGaugeProjection (H alpha b : Band → ℝ) (j : Band) : ℝ :=
  b j - alpha j *
    ((∑ k, H k * alpha k * b k) / sharpWeightTotal H alpha)

def scaleByCenter (alpha x : Band → ℝ) (j : Band) : ℝ :=
  alpha j * x j

def unscaleByCenter (alpha x : Band → ℝ) (j : Band) : ℝ :=
  x j / alpha j

omit [DecidableEq Band] in
/-- The sharp conjugate is just subtraction of the `omega`-weighted mean.
This is the finite arithmetic identity
`S^{-1} P_{alpha,H} S = I - 1 omega^T/(1^T omega)`. -/
theorem unscale_weightedGaugeProjection_scale_eq
    (H alpha x : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    unscaleByCenter alpha
        (weightedGaugeProjection H alpha (scaleByCenter alpha x)) =
      fun j => x j -
        (∑ k, sharpWeight H alpha k * x k) /
          sharpWeightTotal H alpha := by
  funext j
  have hsum :
      (∑ k, H k * alpha k * (alpha k * x k)) =
        ∑ k, sharpWeight H alpha k * x k := by
    apply Finset.sum_congr rfl
    intro k hk
    unfold sharpWeight
    ring
  unfold unscaleByCenter weightedGaugeProjection scaleByCenter
  rw [hsum]
  field_simp [hAlpha j, hTotal]

/-- The normalized sharp weight. -/
def normalizedSharpWeight (H alpha : Band → ℝ) (j : Band) : ℝ :=
  sharpWeight H alpha j / sharpWeightTotal H alpha

def sharpProjection (H alpha x : Band → ℝ) (j : Band) : ℝ :=
  x j - ∑ k, normalizedSharpWeight H alpha k * x k

omit [Fintype Band] [DecidableEq Band] in
theorem sharpWeight_nonneg_of_mass_nonneg
    (H alpha : Band → ℝ) (hH : ∀ j, 0 ≤ H j) (j : Band) :
    0 ≤ sharpWeight H alpha j := by
  exact mul_nonneg (hH j) (sq_nonneg (alpha j))

omit [DecidableEq Band] in
/-- The discrepancy of the two total sharp weights is bounded by the raw
`l1` discrepancy, with no mesh-dependent factor. -/
theorem abs_sharpWeightTotal_sub_le_l1
    (H alpha Hc alphac : Band → ℝ) :
    |sharpWeightTotal H alpha - sharpWeightTotal Hc alphac| ≤
      ∑ j, |sharpWeight H alpha j - sharpWeight Hc alphac j| := by
  unfold sharpWeightTotal
  rw [← Finset.sum_sub_distrib]
  exact Finset.abs_sum_le_sum_abs _ _

omit [DecidableEq Band] in
/-- Raw `omega` convergence implies normalized-weight convergence.  The
constant `2` is independent of the number and sizes of the cells. -/
theorem normalizedSharpWeight_l1_le_raw_l1
    (H alpha Hc alphac : Band → ℝ)
    (hHc : ∀ j, 0 ≤ Hc j)
    (hTotal : 0 < sharpWeightTotal H alpha)
    (hTotalc : 0 < sharpWeightTotal Hc alphac) :
    (∑ j, |normalizedSharpWeight H alpha j -
        normalizedSharpWeight Hc alphac j|) ≤
      2 * (∑ j, |sharpWeight H alpha j -
        sharpWeight Hc alphac j|) /
          sharpWeightTotal H alpha := by
  let total := sharpWeightTotal H alpha
  let totalc := sharpWeightTotal Hc alphac
  let err := ∑ j, |sharpWeight H alpha j - sharpWeight Hc alphac j|
  have htotal : 0 < total := hTotal
  have htotalc : 0 < totalc := hTotalc
  have htotalError :
      |total - totalc| ≤ err := by
    exact abs_sharpWeightTotal_sub_le_l1 H alpha Hc alphac
  have habsContinuum :
      (∑ j, |sharpWeight Hc alphac j|) = totalc := by
    unfold totalc sharpWeightTotal
    apply Finset.sum_congr rfl
    intro j hj
    rw [abs_of_nonneg (sharpWeight_nonneg_of_mass_nonneg Hc alphac hHc j)]
  have hpoint (j : Band) :
      |normalizedSharpWeight H alpha j -
          normalizedSharpWeight Hc alphac j| ≤
        |sharpWeight H alpha j - sharpWeight Hc alphac j| / total +
          |sharpWeight Hc alphac j| * |total - totalc| /
            (total * |totalc|) := by
    exact abs_div_sub_div_le htotal (ne_of_gt htotalc)
      le_rfl le_rfl
  have hsumSecond :
      (∑ j, |sharpWeight Hc alphac j| * |total - totalc| /
        (total * |totalc|)) = |total - totalc| / total := by
    calc
      (∑ j, |sharpWeight Hc alphac j| * |total - totalc| /
          (total * |totalc|)) =
        (∑ j, |sharpWeight Hc alphac j|) *
          (|total - totalc| / (total * |totalc|)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = totalc * (|total - totalc| /
          (total * |totalc|)) := by rw [habsContinuum]
      _ = |total - totalc| / total := by
        rw [abs_of_pos htotalc]
        field_simp [ne_of_gt htotal, ne_of_gt htotalc]
  have hsum :
      (∑ j, |normalizedSharpWeight H alpha j -
          normalizedSharpWeight Hc alphac j|) ≤
        ∑ j, (|sharpWeight H alpha j - sharpWeight Hc alphac j| / total +
          |sharpWeight Hc alphac j| * |total - totalc| /
            (total * |totalc|)) := by
    apply Finset.sum_le_sum
    intro j hj
    exact hpoint j
  have hfirstSum :
      (∑ j, |sharpWeight H alpha j - sharpWeight Hc alphac j| / total) =
        err / total := by
    unfold err
    rw [Finset.sum_div]
  have hcombined :
      (∑ j, |normalizedSharpWeight H alpha j -
          normalizedSharpWeight Hc alphac j|) ≤
        err / total + |total - totalc| / total := by
    calc
      (∑ j, |normalizedSharpWeight H alpha j -
          normalizedSharpWeight Hc alphac j|) ≤
        ∑ j, (|sharpWeight H alpha j - sharpWeight Hc alphac j| / total +
          |sharpWeight Hc alphac j| * |total - totalc| /
            (total * |totalc|)) := hsum
      _ = (∑ j, |sharpWeight H alpha j - sharpWeight Hc alphac j| / total) +
          ∑ j, |sharpWeight Hc alphac j| * |total - totalc| /
            (total * |totalc|) := Finset.sum_add_distrib
      _ = err / total + |total - totalc| / total := by
        rw [hfirstSum, hsumSecond]
  calc
    (∑ j, |normalizedSharpWeight H alpha j -
        normalizedSharpWeight Hc alphac j|) ≤
      err / total + |total - totalc| / total := hcombined
    _ ≤ err / total + err / total := by
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right htotalError htotal.le)
    _ = 2 * err / total := by ring

/-- Elementary relative-product estimate used to transfer simultaneous
relative errors in `H` and `alpha` to the sharp weight
`omega = H * alpha^2`. -/
lemma abs_mul_sq_sub_one_le {r s eH eAlpha : ℝ}
    (heH : 0 ≤ eH) (heAlpha : 0 ≤ eAlpha)
    (hr : |r - 1| ≤ eH) (hs : |s - 1| ≤ eAlpha) :
    |r * s ^ 2 - 1| ≤
      eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha) := by
  have hsAbs : |s| ≤ 1 + eAlpha := by
    calc
      |s| = |(s - 1) + 1| := by ring_nf
      _ ≤ |s - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ eAlpha + 1 := by norm_num; linarith
      _ = 1 + eAlpha := by ring
  have hsPlus : |s + 1| ≤ 2 + eAlpha := by
    calc
      |s + 1| = |(s - 1) + 2| := by ring_nf
      _ ≤ |s - 1| + |(2 : ℝ)| := abs_add_le _ _
      _ ≤ eAlpha + 2 := by norm_num; linarith
      _ = 2 + eAlpha := by ring
  have hOneAlpha : 0 ≤ 1 + eAlpha := by linarith
  have hTwoAlpha : 0 ≤ 2 + eAlpha := by linarith
  have hsSq : |s| ^ 2 ≤ (1 + eAlpha) ^ 2 := by gcongr
  have hfirst : |(r - 1) * s ^ 2| ≤ eH * (1 + eAlpha) ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hr hsSq (sq_nonneg _) heH
  have hsecond : |s ^ 2 - 1| ≤ eAlpha * (2 + eAlpha) := by
    rw [show s ^ 2 - 1 = (s - 1) * (s + 1) by ring, abs_mul]
    exact mul_le_mul hs hsPlus (abs_nonneg _) heAlpha
  rw [show r * s ^ 2 - 1 = (r - 1) * s ^ 2 + (s ^ 2 - 1) by ring]
  exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

omit [Fintype Band] [DecidableEq Band] in
/-- Pointwise relative mass and center errors imply a pointwise raw sharp
weight error.  This is the quantitative place where the `/ alpha_0`
estimate from `center_ratio_error_le_two_errors` is consumed. -/
theorem abs_sharpWeight_sub_le_of_relative_errors
    (H alpha Hc alphac : Band → ℝ) (j : Band) {eH eAlpha : ℝ}
    (hHc : 0 ≤ Hc j) (hHc0 : Hc j ≠ 0) (hAlphac0 : alphac j ≠ 0)
    (heH : 0 ≤ eH) (heAlpha : 0 ≤ eAlpha)
    (hH : |H j / Hc j - 1| ≤ eH)
    (hAlpha : |alpha j / alphac j - 1| ≤ eAlpha) :
    |sharpWeight H alpha j - sharpWeight Hc alphac j| ≤
      sharpWeight Hc alphac j *
        (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) := by
  let r := H j / Hc j
  let s := alpha j / alphac j
  have hfactor :
      sharpWeight H alpha j = sharpWeight Hc alphac j * r * s ^ 2 := by
    unfold sharpWeight r s
    field_simp [hHc0, hAlphac0]
  have hrelative :
      |r * s ^ 2 - 1| ≤
        eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha) :=
    abs_mul_sq_sub_one_le heH heAlpha hH hAlpha
  have hweightc : 0 ≤ sharpWeight Hc alphac j := by
    unfold sharpWeight
    exact mul_nonneg hHc (sq_nonneg (alphac j))
  rw [hfactor, show sharpWeight Hc alphac j * r * s ^ 2 -
      sharpWeight Hc alphac j =
        sharpWeight Hc alphac j * (r * s ^ 2 - 1) by ring, abs_mul,
    abs_of_nonneg hweightc]
  exact mul_le_mul_of_nonneg_left hrelative hweightc

omit [DecidableEq Band] in
/-- Uniform relative mass/center errors give a mesh-uniform raw `l1`
comparison of all sharp weights. -/
theorem sharpWeight_raw_l1_le_of_uniform_relative_errors
    (H alpha Hc alphac : Band → ℝ) {eH eAlpha : ℝ}
    (hHc : ∀ j, 0 ≤ Hc j) (hHc0 : ∀ j, Hc j ≠ 0)
    (hAlphac0 : ∀ j, alphac j ≠ 0)
    (heH : 0 ≤ eH) (heAlpha : 0 ≤ eAlpha)
    (hH : ∀ j, |H j / Hc j - 1| ≤ eH)
    (hAlpha : ∀ j, |alpha j / alphac j - 1| ≤ eAlpha) :
    (∑ j, |sharpWeight H alpha j - sharpWeight Hc alphac j|) ≤
      sharpWeightTotal Hc alphac *
        (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) := by
  calc
    (∑ j, |sharpWeight H alpha j - sharpWeight Hc alphac j|) ≤
      ∑ j, sharpWeight Hc alphac j *
        (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact abs_sharpWeight_sub_le_of_relative_errors
        H alpha Hc alphac j (hHc j) (hHc0 j) (hAlphac0 j)
          heH heAlpha (hH j) (hAlpha j)
    _ = sharpWeightTotal Hc alphac *
        (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) := by
      unfold sharpWeightTotal
      rw [Finset.sum_mul]

omit [DecidableEq Band] in
/-- Pointwise sharp-projection stability under an `l1` comparison of the
normalized `omega` weights.  The estimate is mesh-independent. -/
theorem abs_sharpProjection_sub_le_normalizedWeightL1
    (H alpha Hc alphac x : Band → ℝ) {B : ℝ}
    (hx : ∀ j, |x j| ≤ B) (j : Band) :
    |sharpProjection H alpha x j - sharpProjection Hc alphac x j| ≤
      B * ∑ k,
        |normalizedSharpWeight H alpha k -
          normalizedSharpWeight Hc alphac k| := by
  have hrewrite :
      sharpProjection H alpha x j - sharpProjection Hc alphac x j =
        -(∑ k, (normalizedSharpWeight H alpha k -
          normalizedSharpWeight Hc alphac k) * x k) := by
    unfold sharpProjection
    calc
      x j - (∑ k, normalizedSharpWeight H alpha k * x k) -
          (x j - ∑ k, normalizedSharpWeight Hc alphac k * x k) =
        -((∑ k, normalizedSharpWeight H alpha k * x k) -
          ∑ k, normalizedSharpWeight Hc alphac k * x k) := by ring
      _ = -(∑ k, (normalizedSharpWeight H alpha k * x k -
          normalizedSharpWeight Hc alphac k * x k)) := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [hrewrite, abs_neg]
  calc
    |∑ k, (normalizedSharpWeight H alpha k -
        normalizedSharpWeight Hc alphac k) * x k| ≤
      ∑ k, |(normalizedSharpWeight H alpha k -
        normalizedSharpWeight Hc alphac k) * x k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |normalizedSharpWeight H alpha k -
        normalizedSharpWeight Hc alphac k| * |x k| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul]
    _ ≤ ∑ k, |normalizedSharpWeight H alpha k -
        normalizedSharpWeight Hc alphac k| * B := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left (hx k) (abs_nonneg _)
    _ = B * ∑ k, |normalizedSharpWeight H alpha k -
        normalizedSharpWeight Hc alphac k| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

omit [DecidableEq Band] in
/-- Combined mesh-uniform comparison of the sharp arithmetic and continuum
gauge projections.  All dependence is through relative mass/center errors
and the harmless ratio of total sharp weights; there is no factor depending
on the number of cells. -/
theorem abs_sharpProjection_sub_le_of_uniform_relative_errors
    (H alpha Hc alphac x : Band → ℝ) {eH eAlpha B : ℝ}
    (hHc : ∀ j, 0 ≤ Hc j) (hHc0 : ∀ j, Hc j ≠ 0)
    (hAlphac0 : ∀ j, alphac j ≠ 0)
    (heH : 0 ≤ eH) (heAlpha : 0 ≤ eAlpha)
    (hH : ∀ j, |H j / Hc j - 1| ≤ eH)
    (hAlpha : ∀ j, |alpha j / alphac j - 1| ≤ eAlpha)
    (hTotal : 0 < sharpWeightTotal H alpha)
    (hTotalc : 0 < sharpWeightTotal Hc alphac)
    (hx : ∀ j, |x j| ≤ B) (j : Band) :
    |sharpProjection H alpha x j - sharpProjection Hc alphac x j| ≤
      B * (2 * sharpWeightTotal Hc alphac *
        (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) /
          sharpWeightTotal H alpha) := by
  have hB : 0 ≤ B := (abs_nonneg (x j)).trans (hx j)
  have hraw := sharpWeight_raw_l1_le_of_uniform_relative_errors
    H alpha Hc alphac hHc hHc0 hAlphac0 heH heAlpha hH hAlpha
  have hnormalized := normalizedSharpWeight_l1_le_raw_l1
    H alpha Hc alphac hHc hTotal hTotalc
  have hscaled :
      2 * (∑ k, |sharpWeight H alpha k - sharpWeight Hc alphac k|) /
          sharpWeightTotal H alpha ≤
        2 * sharpWeightTotal Hc alphac *
          (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) /
            sharpWeightTotal H alpha := by
    apply div_le_div_of_nonneg_right _ hTotal.le
    nlinarith [hraw]
  have hweightL1 :
      (∑ k, |normalizedSharpWeight H alpha k -
        normalizedSharpWeight Hc alphac k|) ≤
        2 * sharpWeightTotal Hc alphac *
          (eH * (1 + eAlpha) ^ 2 + eAlpha * (2 + eAlpha)) /
            sharpWeightTotal H alpha :=
    hnormalized.trans hscaled
  exact (abs_sharpProjection_sub_le_normalizedWeightL1
    H alpha Hc alphac x hx j).trans
      (mul_le_mul_of_nonneg_left hweightL1 hB)

end SharpProjection

end Erdos390.Full.MovingLowGaugeTransfer
