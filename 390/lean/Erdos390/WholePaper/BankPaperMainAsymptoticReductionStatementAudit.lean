import Erdos390.WholePaper.BankPaperMainAsymptoticReduction

/-! # Expanded statement audit for the final main-asymptotic reduction -/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

noncomputable section

#check normalized_f_sub_two_mul_eq_div_secondOrderScale
#check eventually_normalized_f_sub_two_mul_le_upperScaledEndpoint_excess
#check mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint
#check mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
#check mainNormalizedLimit_of_canonicalPostTangentContinuation
#check mainAsymptotic_of_canonicalPostTangentContinuation
#check mainNormalizedLimit_of_sharpSaiasDefect_and_selectorGeometryContinuation
#check mainAsymptotic_of_sharpSaiasDefect_and_selectorGeometryContinuation

example {n : ℕ} (hn : 1 < n) :
    (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ) =
      ((f n : ℝ) - 2 * (n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ)) := by
  simpa only [secondOrderScale] using
    normalized_f_sub_two_mul_eq_div_secondOrderScale hn

example {c : ℝ}
    (hupper : ∀ᶠ n : ℕ in atTop,
      f n ≤ 2 * n +
        Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))) :
    ∀ᶠ n : ℕ in atTop,
      (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ) ≤
        (((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ))) : ℕ) : ℝ) -
            2 * (n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
  have hupper' : ∀ᶠ n : ℕ in atTop,
      f n ≤ upperEndpoint n (upperTailLength c n) := by
    simpa only [upperEndpoint, upperTailLength, secondOrderScale] using hupper
  simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
    eventually_normalized_f_sub_two_mul_le_upperScaledEndpoint_excess hupper'

example
    (hupper : ∀ c : ℝ,
      ((4029639598 : ℝ) / 25970038185) < c →
        ∀ᶠ n : ℕ in atTop,
          f n ≤ 2 * n +
            Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds ((4029639598 : ℝ) / 25970038185)) := by
  have hupper' : ∀ c : ℝ, C0 < c →
      ∀ᶠ n : ℕ in atTop,
        f n ≤ upperEndpoint n (upperTailLength c n) := by
    intro c hc
    have hc' : ((4029639598 : ℝ) / 25970038185) < c := by
      simpa only [C0] using hc
    simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
      hupper c hc'
  simpa only [MainNormalizedLimit, C0] using
    mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint hupper'

example
    (hupper : ∀ c : ℝ,
      ((4029639598 : ℝ) / 25970038185) < c →
        ∀ᶠ n : ℕ in atTop,
          f n ≤ 2 * n +
            Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))) :
    (fun n : ℕ =>
        (f n : ℝ) -
          (2 * (n : ℝ) +
            ((4029639598 : ℝ) / 25970038185) *
              ((n : ℝ) / Real.log (n : ℝ))))
      =o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hupper' : ∀ c : ℝ, C0 < c →
      ∀ᶠ n : ℕ in atTop,
        f n ≤ upperEndpoint n (upperTailLength c n) := by
    intro c hc
    have hc' : ((4029639598 : ℝ) / 25970038185) < c := by
      simpa only [C0] using hc
    simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
      hupper c hc'
  simpa only [MainAsymptotic, mainError, C0, secondOrderScale] using
    mainAsymptotic_of_eventually_f_le_upperScaledEndpoint hupper'

example
    (hcontinuation : ∀ c : ℝ,
      ((4029639598 : ℝ) / 25970038185) < c →
        ∀ depth : ℕ, 201 ≤ depth →
          BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds ((4029639598 : ℝ) / 25970038185)) := by
  have hcontinuation' : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalPostTangentContinuationAtDepth c depth := by
    intro c hc depth hdepth
    exact hcontinuation c (by simpa only [C0] using hc) depth hdepth
  simpa only [MainNormalizedLimit, C0] using
    mainNormalizedLimit_of_canonicalPostTangentContinuation hcontinuation'

example
    (hcontinuation : ∀ c : ℝ,
      ((4029639598 : ℝ) / 25970038185) < c →
        ∀ depth : ℕ, 201 ≤ depth →
          BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    (fun n : ℕ =>
        (f n : ℝ) -
          (2 * (n : ℝ) +
            ((4029639598 : ℝ) / 25970038185) *
              ((n : ℝ) / Real.log (n : ℝ))))
      =o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hcontinuation' : ∀ c : ℝ, C0 < c →
      ∀ depth : ℕ, 201 ≤ depth →
        BankPaperCanonicalPostTangentContinuationAtDepth c depth := by
    intro c hc depth hdepth
    exact hcontinuation c (by simpa only [C0] using hc) depth hdepth
  simpa only [MainAsymptotic, mainError, C0, secondOrderScale] using
    mainAsymptotic_of_canonicalPostTangentContinuation hcontinuation'

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : ∀ {X y : ℕ}, Y₀ ≤ y → 2 ≤ y → y < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
        |roughSaiasReverseNormalFormDefect X y X| ≤
          C * (X : ℝ) / Real.log (y : ℝ) ^ 2)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ c : ℝ, C0 < c →
          ∀ depth : ℕ, 201 ≤ depth →
            BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds ((4029639598 : ℝ) / 25970038185)) := by
  have hdefect' :
      RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀ := by
    intro X y hY h2 hxy hlog
    exact hdefect (X := X) (y := y) hY h2 hxy hlog
  simpa only [MainNormalizedLimit, C0] using
    mainNormalizedLimit_of_sharpSaiasDefect_and_selectorGeometryContinuation
      hC hdefect' hselectorGeometry

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : ∀ {X y : ℕ}, Y₀ ≤ y → 2 ≤ y → y < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
        |roughSaiasReverseNormalFormDefect X y X| ≤
          C * (X : ℝ) / Real.log (y : ℝ) ^ 2)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ c : ℝ, C0 < c →
          ∀ depth : ℕ, 201 ≤ depth →
            BankPaperCanonicalPostTangentContinuationAtDepth c depth) :
    (fun n : ℕ =>
        (f n : ℝ) -
          (2 * (n : ℝ) +
            ((4029639598 : ℝ) / 25970038185) *
              ((n : ℝ) / Real.log (n : ℝ))))
      =o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  have hdefect' :
      RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀ := by
    intro X y hY h2 hxy hlog
    exact hdefect (X := X) (y := y) hY h2 hxy hlog
  simpa only [MainAsymptotic, mainError, C0, secondOrderScale] using
    mainAsymptotic_of_sharpSaiasDefect_and_selectorGeometryContinuation
      hC hdefect' hselectorGeometry

end

end Erdos390.WholePaper
