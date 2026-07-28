import Erdos390.Full.PrimeSums

/-!
# Vanishing rate for the actual bridge baseline `L¹` majorant

This is the quantifier-order layer behind the finite theorem in
`PaperBridgeBaselineL1`: first fix the cutoff and effective box, then let
`n` grow.  The only moving quantity is the actual prime-band reciprocal
sum, bounded here directly by the proved Chebyshev estimate.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeBaselineL1Rate

open ArithmeticModel Scale PrimeSums

noncomputable section

/-- The exact first-moment majorant used by the finite bridge theorem, with
all fixed paper constants made explicit. -/
def bridgeFirstMomentMajorant
    (A rho R : ℝ) (W n : ℕ) : ℝ :=
  (2 * A / (rho * L n)) * bandReciprocalSum n W + A * R / L n

/-- For a fixed cutoff, cell-density margin, effective box, and nuisance
radius, the actual arithmetic first-moment majorant tends to zero. -/
theorem tendsto_bridgeFirstMomentMajorant_zero
    (A rho R : ℝ) (W : ℕ)
    (hA : 0 ≤ A) (hrho : 0 < rho) :
    Tendsto (bridgeFirstMomentMajorant A rho R W) atTop (nhds 0) := by
  let medium : ℕ → ℝ := fun n ↦
    (2 * A / (rho * L n)) * bandReciprocalSum n W
  let nuisance : ℕ → ℝ := fun n ↦ A * R / L n
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto
      (fun n : ℕ ↦ (24 * A / rho) * (Real.log (L n) / L n))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hratio
  have hmedium0 : ∀ᶠ n : ℕ in atTop, 0 ≤ medium n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hL : 0 < L n := L_pos hn
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    dsimp only [medium]
    exact mul_nonneg (by positivity) hband
  have hmediumMajor : ∀ᶠ n : ℕ in atTop,
      medium n ≤ (24 * A / rho) * (Real.log (L n) / L n) := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      Filter.eventually_gt_atTop 1] with n hband hn
    have hL : 0 < L n := L_pos hn
    have hcoef : 0 ≤ 2 * A / (rho * L n) := by positivity
    dsimp only [medium]
    calc
      (2 * A / (rho * L n)) * bandReciprocalSum n W ≤
          (2 * A / (rho * L n)) * (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef
      _ = (24 * A / rho) * (Real.log (L n) / L n) := by ring
  have hmedium : Tendsto medium atTop (nhds 0) :=
    squeeze_zero' hmedium0 hmediumMajor hmajor
  have hInv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  have hnuisance : Tendsto nuisance atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ A * R) atTop (nhds (A * R)) :=
      tendsto_const_nhds
    have hraw := hconst.mul hInv
    have h : Tendsto (fun n : ℕ ↦ (A * R) * (L n)⁻¹)
        atTop (nhds 0) := by simpa only [mul_zero] using hraw
    apply h.congr'
    filter_upwards with n
    dsimp only [nuisance]
    ring
  have hsum := hmedium.add hnuisance
  have hsum0 : Tendsto (fun n ↦ medium n + nuisance n)
      atTop (nhds 0) := by simpa only [zero_add] using hsum
  apply hsum0.congr'
  filter_upwards with n
  unfold bridgeFirstMomentMajorant
  rfl

/-- Once the fixed pointwise score box is chosen, normalization is
eventually legitimate uniformly throughout that box. -/
theorem eventually_exp_mul_bridgeFirstMomentMajorant_lt_one
    (A rho R K : ℝ) (W : ℕ)
    (hA : 0 ≤ A) (hrho : 0 < rho) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp K * bridgeFirstMomentMajorant A rho R W n < 1 := by
  have hM := tendsto_bridgeFirstMomentMajorant_zero A rho R W hA hrho
  have hsmall : ∀ᶠ n : ℕ in atTop,
      bridgeFirstMomentMajorant A rho R W n < Real.exp (-K) :=
    hM (Iio_mem_nhds (Real.exp_pos (-K)))
  filter_upwards [hsmall] with n hn
  calc
    Real.exp K * bridgeFirstMomentMajorant A rho R W n <
        Real.exp K * Real.exp (-K) :=
      mul_lt_mul_of_pos_left hn (Real.exp_pos K)
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The explicit normalized `L¹` upper bound from the finite bridge
theorem. -/
def bridgeL1UpperMajorant
    (A rho R K : ℝ) (W n : ℕ) : ℝ :=
  let M := Real.exp K * bridgeFirstMomentMajorant A rho R W n
  2 * M / (1 - M)

/-- The full normalized `L¹` upper bound also tends to zero. -/
theorem tendsto_bridgeL1UpperMajorant_zero
    (A rho R K : ℝ) (W : ℕ)
    (hA : 0 ≤ A) (hrho : 0 < rho) :
    Tendsto (bridgeL1UpperMajorant A rho R K W) atTop (nhds 0) := by
  have hbase := tendsto_bridgeFirstMomentMajorant_zero A rho R W hA hrho
  have hscaled : Tendsto
      (fun n : ℕ ↦ Real.exp K * bridgeFirstMomentMajorant A rho R W n)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hbase
  have hnum : Tendsto
      (fun n : ℕ ↦
        2 * (Real.exp K * bridgeFirstMomentMajorant A rho R W n))
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hscaled
  have hden : Tendsto
      (fun n : ℕ ↦
        1 - Real.exp K * bridgeFirstMomentMajorant A rho R W n)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hscaled
  have hquot := hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot0 : Tendsto
      ((fun n : ℕ ↦
          2 * (Real.exp K * bridgeFirstMomentMajorant A rho R W n)) /
        (fun n : ℕ ↦
          1 - Real.exp K * bridgeFirstMomentMajorant A rho R W n))
      atTop (nhds 0) := by simpa only [zero_div] using hquot
  apply hquot0.congr'
  filter_upwards with n
  unfold bridgeL1UpperMajorant
  rfl

/-- Hence any fixed positive covariance tolerance eventually absorbs the
`L¹` perturbation, including the fixed nuisance-diameter square. -/
theorem eventually_bridgeL1UpperMajorant_mul_sq_le
    (A rho R K D gamma : ℝ) (W : ℕ)
    (hA : 0 ≤ A) (hrho : 0 < rho) (hgamma : 0 < gamma) :
    ∀ᶠ n : ℕ in atTop,
      bridgeL1UpperMajorant A rho R K W n * D ^ 2 ≤ gamma / 2 := by
  have hupperRaw :=
    (tendsto_bridgeL1UpperMajorant_zero A rho R K W hA hrho).mul_const
      (D ^ 2)
  have hupper : Tendsto
      (fun n ↦ bridgeL1UpperMajorant A rho R K W n * D ^ 2)
      atTop (nhds 0) := by simpa only [zero_mul] using hupperRaw
  have hhalf : 0 < gamma / 2 := by positivity
  have hevent : ∀ᶠ n : ℕ in atTop,
      bridgeL1UpperMajorant A rho R K W n * D ^ 2 < gamma / 2 :=
    hupper (Iio_mem_nhds hhalf)
  exact hevent.mono (fun n hn ↦ hn.le)

end

end Erdos390.Full.PaperBridgeBaselineL1Rate
