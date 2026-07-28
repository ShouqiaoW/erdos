import Erdos390.Full.PrimeBandQuadrature

/-!
# Endpoint-uniform first logarithmic prime moment

For the moving low cell the lower cutoff is fixed while the upper endpoint
grows.  Keeping the integrable `1/(x log^3 x)` PNT majorant, rather than
freezing `log x` at the lower endpoint, gives an error independent of the
upper endpoint.  Division by the ambient logarithmic scale therefore tends
to zero and supplies the relative low-center transfer.
-/

open Set

noncomputable section

namespace Erdos390.Full.MovingLowMomentQuadrature

open MeasureTheory PrimeSums PrimeBandQuadrature

def logMomentTailMajorant (C x : ℝ) : ℝ :=
  C / (x * Real.log x ^ 3)

def logMomentTailPrimitive (C x : ℝ) : ℝ :=
  -C / (2 * Real.log x ^ 2)

lemma hasDerivAt_logMomentTailPrimitive (C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (logMomentTailPrimitive C)
      (logMomentTailMajorant C x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hpow := (Real.hasDerivAt_log hx0).pow 2
  have hinv := hpow.inv (pow_ne_zero 2 hlog0)
  have hmul := (hasDerivAt_const x (-(C / 2))).mul hinv
  convert hmul using 1
  · unfold logMomentTailPrimitive
    funext z
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.pow_apply]
    ring_nf
  · unfold logMomentTailMajorant
    simp only [Pi.pow_apply]
    field_simp [hx0, hlog0]
    ring

lemma continuousOn_logMomentTailMajorant (C : ℝ) {A Y : ℝ}
    (hA : 1 < A) :
    ContinuousOn (logMomentTailMajorant C) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold logMomentTailMajorant
  exact continuousAt_const.div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 3))
    (mul_ne_zero hx0 (pow_ne_zero 3 hlog0)) |>.continuousWithinAt

lemma integral_logMomentTailMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, logMomentTailMajorant C x) =
      logMomentTailPrimitive C Y - logMomentTailPrimitive C A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_logMomentTailPrimitive C (by linarith [hx.1, hA])
  · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_logMomentTailMajorant C (A := A) (Y := Y)
        (by linarith [hA]))

lemma intervalIntegrable_logReciprocalErrorKernel
    {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable logReciprocalErrorKernel volume A Y := by
  have htheta := PrimeSums.intervalIntegrable_theta_div_sq
    (hA.trans hAY)
  have hthetaCell : IntervalIntegrable
      (fun x : ℝ => Chebyshev.theta x / x ^ 2) volume A Y := by
    apply htheta.mono_set
    rw [uIcc_of_le hAY, uIcc_of_le (hA.trans hAY)]
    intro x hx
    exact ⟨hA.trans hx.1, hx.2⟩
  have hmain : IntervalIntegrable (fun x : ℝ => 1 / x) volume A Y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hAY
    intro x hx
    exact (continuousAt_const.div continuousAt_id
      (by simpa only [id_eq] using
        (ne_of_gt (show 0 < x by linarith [hA, hx.1])))).continuousWithinAt
  apply (hthetaCell.sub hmain).congr
  intro x hx
  have hx0 : x ≠ 0 := by
    have hx' : x ∈ uIcc A Y := uIoc_subset_uIcc hx
    rw [uIcc_of_le hAY] at hx'
    exact ne_of_gt (by linarith [hA, hx'.1])
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]

lemma abs_logReciprocalErrorKernel_le_tail (C : ℝ)
    {x : ℝ} (hx : 2 ≤ x)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |logReciprocalErrorKernel x| ≤ logMomentTailMajorant C x := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  unfold logReciprocalErrorKernel logMomentTailMajorant
  rw [abs_div, abs_of_pos (sq_pos_of_pos hxpos)]
  calc
    |thetaError x| / x ^ 2 ≤
        (C * x / Real.log x ^ 3) / x ^ 2 := by gcongr
    _ = C / (x * Real.log x ^ 3) := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

theorem fullLogReciprocalSum_interval_uniform_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * C / Real.log (A : ℝ) ^ 3 +
        C / (2 * Real.log (A : ℝ) ^ 2) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := hApos.trans_le hAYR
  have hlogApos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < A by omega))
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < Y by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt := intervalIntegrable_logReciprocalErrorKernel hAR hAYR
  have hmajorInt : IntervalIntegrable (logMomentTailMajorant C) volume
      (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_logMomentTailMajorant C (by linarith [hAR]))
  have hIntBound :
      |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
        C / (2 * Real.log (A : ℝ) ^ 2) := by
    calc
      |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y, |logReciprocalErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y, logMomentTailMajorant C x := by
        exact intervalIntegral.integral_mono_on hAYR herrInt.abs hmajorInt
          (fun x hx => abs_logReciprocalErrorKernel_le_tail C
            (hAR.trans hx.1) (hTheta x hx))
      _ = logMomentTailPrimitive C (Y : ℝ) -
          logMomentTailPrimitive C (A : ℝ) :=
        integral_logMomentTailMajorant C hAR hAYR
      _ ≤ C / (2 * Real.log (A : ℝ) ^ 2) := by
        unfold logMomentTailPrimitive
        have hnonneg : 0 ≤ C / (2 * Real.log (Y : ℝ) ^ 2) := by positivity
        have heq :
            -C / (2 * Real.log (Y : ℝ) ^ 2) -
                (-C / (2 * Real.log (A : ℝ) ^ 2)) =
              C / (2 * Real.log (A : ℝ) ^ 2) -
                C / (2 * Real.log (Y : ℝ) ^ 2) := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  rw [fullLogReciprocalSum_interval_error_identity hA hAY]
  have hAterm : |thetaError (A : ℝ) / (A : ℝ)| ≤
      C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hApos]
    calc
      _ ≤ (C * (A : ℝ) / Real.log (A : ℝ) ^ 3) / (A : ℝ) := by
        exact div_le_div_of_nonneg_right
          (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩) hApos.le
      _ = _ := by field_simp [ne_of_gt hApos]
  have hYterm : |thetaError (Y : ℝ) / (Y : ℝ)| ≤
      C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hYpos]
    calc
      _ ≤ (C * (Y : ℝ) / Real.log (Y : ℝ) ^ 3) / (Y : ℝ) := by
        exact div_le_div_of_nonneg_right
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩) hYpos.le
      _ = C / Real.log (Y : ℝ) ^ 3 := by field_simp [ne_of_gt hYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by gcongr
  calc
    |thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
      |thetaError (Y : ℝ) / (Y : ℝ)| +
        |thetaError (A : ℝ) / (A : ℝ)| +
        |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| := by
      have h₁ := abs_add_le
        (thetaError (Y : ℝ) / (Y : ℝ) - thetaError (A : ℝ) / (A : ℝ))
        (∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x)
      have h₂ := abs_sub (thetaError (Y : ℝ) / (Y : ℝ))
        (thetaError (A : ℝ) / (A : ℝ))
      linarith
    _ ≤ 2 * C / Real.log (A : ℝ) ^ 3 +
        C / (2 * Real.log (A : ℝ) ^ 2) := by
      calc
        _ ≤ C / Real.log (A : ℝ) ^ 3 +
              C / Real.log (A : ℝ) ^ 3 +
              C / (2 * Real.log (A : ℝ) ^ 2) :=
          add_le_add (add_le_add hYterm hAterm) hIntBound
        _ = _ := by ring

/-- After division by any ambient logarithmic scale, the endpoint-uniform
error decays like the reciprocal of that scale.  This is the precise form
needed for the moving low cell: the lower cutoff may stay fixed while the
ambient smoothness scale tends to infinity. -/
theorem normalized_fullLogReciprocalSum_interval_uniform_error_bound
    {A Y : ℕ} {z C : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) (hz : 1 < z) (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |(fullLogReciprocalSum Y - fullLogReciprocalSum A) / Real.log z -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) / Real.log z| ≤
      (2 * C / Real.log (A : ℝ) ^ 3 +
        C / (2 * Real.log (A : ℝ) ^ 2)) / Real.log z := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  rw [← sub_div, abs_div, abs_of_pos hlogz]
  exact div_le_div_of_nonneg_right
    (fullLogReciprocalSum_interval_uniform_error_bound
      hA hAY hC hTheta) hlogz.le

theorem exists_fullLogReciprocalSum_interval_uniform_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullLogReciprocalSum Y - fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * C / Real.log (A : ℝ) ^ 3 +
          C / (2 * Real.log (A : ℝ) ^ 2) := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨C, hC, max N 2, ?_⟩
  intro A Y hA hAY
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  apply fullLogReciprocalSum_interval_uniform_error_bound hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  exact (le_of_lt hX₀N).trans (hNAR.trans hx.1)

/-- A named global witness for the first-logarithmic-moment PNT constant. -/
noncomputable def fullLogReciprocalSumUniformConstant : ℝ :=
  Classical.choose exists_fullLogReciprocalSum_interval_uniform_error_bound

theorem fullLogReciprocalSumUniformConstant_pos :
    0 < fullLogReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullLogReciprocalSum_interval_uniform_error_bound).1

/-- The corresponding named arithmetic cutoff.  Both this cutoff and the
preceding constant are independent of every later regular mesh. -/
noncomputable def fullLogReciprocalSumUniformCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      exists_fullLogReciprocalSum_interval_uniform_error_bound).2

theorem fullLogReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullLogReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * fullLogReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 +
        fullLogReciprocalSumUniformConstant /
          (2 * Real.log (A : ℝ) ^ 2) :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullLogReciprocalSum_interval_uniform_error_bound).2)
    A Y hA hAY

/-- Uniform normalized version, with `C` and the arithmetic threshold chosen
before the two moving endpoints and before the ambient scale. -/
theorem exists_normalized_fullLogReciprocalSum_interval_uniform_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ, ∀ z : ℝ,
      X₀ ≤ A → A ≤ Y → 1 < z →
      |(fullLogReciprocalSum Y - fullLogReciprocalSum A) / Real.log z -
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) / Real.log z| ≤
        (2 * C / Real.log (A : ℝ) ^ 3 +
          C / (2 * Real.log (A : ℝ) ^ 2)) / Real.log z := by
  obtain ⟨C, hC, X₀, hbound⟩ :=
    exists_fullLogReciprocalSum_interval_uniform_error_bound
  refine ⟨C, hC, X₀, ?_⟩
  intro A Y z hA hAY hz
  have hraw := hbound A Y hA hAY
  have hlogz : 0 < Real.log z := Real.log_pos hz
  rw [← sub_div, abs_div, abs_of_pos hlogz]
  exact div_le_div_of_nonneg_right hraw hlogz.le

end Erdos390.Full.MovingLowMomentQuadrature
