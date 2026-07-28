import Erdos390.WholePaper.ThirteenLayerLowerBound
import Erdos390.WholePaper.UpperScale
import Erdos390.WholePaper.MainTargetEquivalence
import Erdos390.WholePaper.BankPaperCanonicalUpperConstructionEventually
import Erdos390.WholePaper.RoughSaiasEndpointApproximation

/-!
# Final main-asymptotic reduction

This file performs the last analytic normalization after an eventual family
of paper upper endpoints has been constructed.  The unconditional
thirteen-layer lower bound supplies every lower neighborhood of `C0`; for an
upper neighborhood `b > C0`, an intermediate scale
`c = (C0 + b) / 2` and the exact ceiling asymptotic for
`upperEndpoint n (upperTailLength c n)` supply the matching upper bound.

The final two theorems isolate exactly the inputs which are not yet closed by
the present upper construction:

* the inverse-log-square bound for the explicit Saias normal-form defect;
* a selector/geometry continuation which consumes the resulting endpoint
  approximation and returns the literal post-tangent continuation at every
  required scale and depth.

Neither input mentions `MainAsymptotic` or `MainNormalizedLimit`.  All lower
bounds, endpoint ceiling normalization, and passage between the two exact
main targets are discharged here.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-! ## Exact normalization of the extremal excess -/

/-- For `n > 1`, the displayed normalized excess is literally division by
the second-order scale. -/
theorem normalized_f_sub_two_mul_eq_div_secondOrderScale
    {n : ℕ} (hn : 1 < n) :
    (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ) =
      ((f n : ℝ) - 2 * (n : ℝ)) / secondOrderScale n := by
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  simp only [secondOrderScale]
  field_simp [hnR, hlog]

/-- An eventual natural endpoint bound gives the corresponding real
normalized upper bound, with the totalized scale removed explicitly. -/
theorem eventually_normalized_f_sub_two_mul_le_upperScaledEndpoint_excess
    {c : ℝ}
    (hupper : ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n)) :
    ∀ᶠ n : ℕ in atTop,
      (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ) ≤
        ((upperEndpoint n (upperTailLength c n) : ℝ) -
            2 * (n : ℝ)) /
          secondOrderScale n := by
  filter_upwards [hupper, eventually_gt_atTop 1] with n hupperN hn
  have hscale : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hupperReal : (f n : ℝ) ≤
      (upperEndpoint n (upperTailLength c n) : ℝ) := by
    exact_mod_cast hupperN
  have hdiff : (f n : ℝ) - 2 * (n : ℝ) ≤
      (upperEndpoint n (upperTailLength c n) : ℝ) -
        2 * (n : ℝ) :=
    sub_le_sub_right hupperReal _
  rw [normalized_f_sub_two_mul_eq_div_secondOrderScale hn]
  exact div_le_div_of_nonneg_right hdiff hscale.le

/-! ## Two-sided limit from the endpoint family -/

/-- The unconditional lower bound together with eventual scaled upper
endpoints for every `c > C0` proves the exact normalized limit. -/
theorem mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint
    (hupper : ∀ c : ℝ, C0 < c →
      ∀ᶠ n : ℕ in atTop,
        f n ≤ upperEndpoint n (upperTailLength c n)) :
    MainNormalizedLimit := by
  unfold MainNormalizedLimit
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    let ε : ℝ := (C0 - a) / 2
    have hε : 0 < ε := by
      dsimp only [ε]
      linarith
    have hlower :=
      eventually_C0_sub_eps_le_normalized_f_sub_two_mul hε
    filter_upwards [hlower] with n hlowerN
    have haMid : a < C0 - ε := by
      dsimp only [ε]
      linarith
    exact haMid.trans_le hlowerN
  · intro b hb
    let c : ℝ := (C0 + b) / 2
    have hcLower : C0 < c := by
      dsimp only [c]
      linarith
    have hcUpper : c < b := by
      dsimp only [c]
      linarith
    have hC0 : 0 < C0 := by
      norm_num [C0]
    have hcPos : 0 < c := hC0.trans hcLower
    have hnormalizedUpper :=
      eventually_normalized_f_sub_two_mul_le_upperScaledEndpoint_excess
        (hupper c hcLower)
    have hendpointLt :
        ∀ᶠ n : ℕ in atTop,
          ((upperEndpoint n (upperTailLength c n) : ℝ) -
                2 * (n : ℝ)) /
              secondOrderScale n < b :=
      (upperScaledEndpoint_excess_normalized_tendsto hcPos).eventually
        (Iio_mem_nhds hcUpper)
    filter_upwards [hnormalizedUpper, hendpointLt]
      with n hnormalizedN hendpointN
    exact hnormalizedN.trans_lt hendpointN

/-- The same endpoint-family reduction with the paper's literal small-`o`
target as its conclusion. -/
theorem mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
    (hupper : ∀ c : ℝ, C0 < c →
      ∀ᶠ n : ℕ in atTop,
        f n ≤ upperEndpoint n (upperTailLength c n)) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint hupper)

/-! ## Specialization to the canonical upper construction -/

/-- If the exact canonical post-tangent continuation is available at every
paper scale above `C0` and every capacity-permitted depth, the weakest
capacity connector gives the whole endpoint family and hence the exact
normalized limit. -/
theorem mainNormalizedLimit_of_canonicalPostTangentContinuation
    (hcontinuation : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  obtain ⟨depth, hdepth, hbridge⟩ :=
    exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
      hc
  exact hbridge (hcontinuation c hc depth hdepth)

/-- Canonical-continuation form of the exact small-`o` main theorem. -/
theorem mainAsymptotic_of_canonicalPostTangentContinuation
    (hcontinuation : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_canonicalPostTangentContinuation hcontinuation)

/-! ## Honest sharp-defect and selector/geometry terminal -/

/-- The explicit sharp Saias defect plus one selector/geometry continuation
from its endpoint approximation imply the exact normalized main limit.  The
selector/geometry premise concludes only the already-audited post-tangent
continuation; it contains no asymptotic target. -/
theorem mainNormalizedLimit_of_sharpSaiasDefect_and_selectorGeometryContinuation
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ c : ℝ, C0 < c →
          ∀ depth : ℕ, 201 ≤ depth →
            BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_canonicalPostTangentContinuation
  exact hselectorGeometry
    (roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect hC hdefect)

/-- The literal small-`o` main theorem under exactly the same two remaining
inputs. -/
theorem mainAsymptotic_of_sharpSaiasDefect_and_selectorGeometryContinuation
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ c : ℝ, C0 < c →
          ∀ depth : ℕ, 201 ≤ depth →
            BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_sharpSaiasDefect_and_selectorGeometryContinuation
      hC hdefect hselectorGeometry)

end

end Erdos390.WholePaper
