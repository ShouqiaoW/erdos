import Erdos390.WholePaper.RoughSaiasCorrectionObstruction

/-!
# Absorbing the elementary Dickman Riemann term

Under `log X / log y ≤ 5`, the explicit Dickman cell error is at most
`2 X (6 + 40 log y) / y`.  The standard fact `log(y)^k / y → 0`
therefore absorbs it into `X / log(y)^2` beyond an unconditional cutoff.
-/

namespace Erdos390.WholePaper

open Filter

noncomputable section

theorem exists_roughSaiasRiemannAbsorptionCutoff :
    ∃ Y₀ : ℕ, ∀ y : ℕ, Y₀ ≤ y →
      2 * (6 + 40 * Real.log (y : ℝ)) * Real.log (y : ℝ) ^ 2 ≤
        (y : ℝ) := by
  have hcast : Tendsto (fun y : ℕ ↦ (y : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsq : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) ^ 2 / (y : ℝ))
      atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  have hcube : Tendsto
      (fun y : ℕ ↦ Real.log (y : ℝ) ^ 3 / (y : ℝ))
      atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hcast
  have hlimit : Tendsto
      (fun y : ℕ ↦
        12 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 3 / (y : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      (tendsto_const_nhds.mul hsq).add (tendsto_const_nhds.mul hcube)
  have hnormalized : Tendsto
      (fun y : ℕ ↦
        (2 * (6 + 40 * Real.log (y : ℝ)) *
          Real.log (y : ℝ) ^ 2) / (y : ℝ))
      atTop (nhds 0) := by
    apply hlimit.congr'
    filter_upwards [eventually_gt_atTop 0] with y hy
    have hyne : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
    field_simp [hyne]
    ring
  have hevent : ∀ᶠ y : ℕ in atTop,
      (2 * (6 + 40 * Real.log (y : ℝ)) *
        Real.log (y : ℝ) ^ 2) / (y : ℝ) < 1 :=
    hnormalized.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rw [eventually_atTop] at hevent
  obtain ⟨Y₀, hY₀⟩ := hevent
  use Y₀
  intro y hy
  have hyratio := (hY₀ y hy).le
  by_cases hyzero : y = 0
  · subst y
    norm_num
  · have hypos : 0 < (y : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero hyzero)
    exact (div_le_one hypos).mp hyratio

noncomputable def roughSaiasRiemannAbsorptionCutoff : ℕ :=
  Classical.choose exists_roughSaiasRiemannAbsorptionCutoff

theorem roughSaiasRiemannAbsorptionCutoff_spec
    {y : ℕ} (hY : roughSaiasRiemannAbsorptionCutoff ≤ y) :
    2 * (6 + 40 * Real.log (y : ℝ)) * Real.log (y : ℝ) ^ 2 ≤
      (y : ℝ) :=
  Classical.choose_spec exists_roughSaiasRiemannAbsorptionCutoff y hY

/-- The explicit envelope for the Dickman right-endpoint Riemann error is
itself absorbed at the target scale. -/
theorem roughSaiasDickmanRiemannEnvelope_le_invLogSq
    {X y : ℕ} (hY : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hy2 : 2 ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) ≤
      (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) :=
    (div_le_iff₀ hlogy).mp hu5
  have hcoefficient :
      6 + 8 * Real.log (X : ℝ) ≤
        6 + 40 * Real.log (y : ℝ) := by
    linarith
  have habsorb := roughSaiasRiemannAbsorptionCutoff_spec hY
  have habsorb' :
      2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) ^ 2 ≤
        (y : ℝ) := by
    have hscaled := mul_le_mul_of_nonneg_left hcoefficient
      (by norm_num : (0 : ℝ) ≤ 2)
    have hscaled' := mul_le_mul_of_nonneg_right hscaled
      (sq_nonneg (Real.log (y : ℝ)))
    exact hscaled'.trans habsorb
  apply (div_le_iff₀ hypos).2
  rw [show (X : ℝ) / Real.log (y : ℝ) ^ 2 * (y : ℝ) =
    ((X : ℝ) * (y : ℝ)) / Real.log (y : ℝ) ^ 2 by ring]
  apply (le_div_iff₀ (sq_pos_of_pos hlogy)).2
  have hmul := mul_le_mul_of_nonneg_left habsorb'
    (show (0 : ℝ) ≤ (X : ℝ) by positivity)
  convert hmul using 1; ring_nf

/-- The explicit Dickman Riemann block is absorbed at the target scale. -/
theorem roughSaiasDickmanBuchstabBlockRemainder_abs_le_invLogSq
    {X y M : ℕ} (hY : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyM : y ≤ M) (hMX : M ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasDickmanBuchstabBlockRemainder X y M| ≤
      (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hraw := roughSaiasDickmanBuchstabBlockRemainder_abs_le
    hX hy2 hyM hMX hu5
  exact hraw.trans
    (roughSaiasDickmanRiemannEnvelope_le_invLogSq hY hy2 hu5)

/-- Beyond the unconditional absorption cutoff, the complete sharp defect
is reduced to one signed correction obstruction and no other unestimated
term. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_obstruction
    {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hYriemann : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (4 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      |roughSaiasCanonicalCorrectionObstruction X y| := by
  have hbase :=
    roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_riemann_add_obstruction
      hy2 hyX hYtheta hu5
  have hriemann := roughSaiasDickmanRiemannEnvelope_le_invLogSq
    hYriemann hy2 hu5
  calc
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) +
        |roughSaiasCanonicalCorrectionObstruction X y| := hbase
    _ ≤ (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        ((X : ℝ) / Real.log (y : ℝ) ^ 2) +
        |roughSaiasCanonicalCorrectionObstruction X y| := by
      exact add_le_add (add_le_add le_rfl hriemann) le_rfl
    _ = (4 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasCanonicalCorrectionObstruction X y| := by ring

end

end Erdos390.WholePaper
