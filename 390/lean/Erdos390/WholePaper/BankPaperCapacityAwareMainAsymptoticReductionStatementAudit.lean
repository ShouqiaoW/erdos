import Erdos390.WholePaper.BankPaperCapacityAwareMainAsymptoticReduction

/-!
# Statement audit for the capacity-aware main-asymptotic reduction

The census contains all six public declarations.  The examples unfold the
selected-depth definition, repeat the bridge specification and every
terminal premise verbatim, and unfold the two final target abbreviations.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

noncomputable section

/-! ## Complete public declaration census -/

#check bankPaperCapacitySelectedDepth
#check bankPaperCapacitySelectedDepth_spec
#check mainNormalizedLimit_of_capacityAwareCanonicalPostTangentContinuation
#check mainAsymptotic_of_capacityAwareCanonicalPostTangentContinuation
#check
  mainNormalizedLimit_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation
#check
  mainAsymptotic_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation

/-! ## Exact selected-depth interface -/

example (c : ℝ) (hc : C0 < c) :
    bankPaperCapacitySelectedDepth c hc =
      (by
        classical
        exact Nat.find
          (exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
            hc)) := by
  rfl

example {c : ℝ} (hc : C0 < c) :
    201 ≤ bankPaperCapacitySelectedDepth c hc ∧
      (BankPaperCanonicalPostTangentContinuationAtDepth c
            (bankPaperCapacitySelectedDepth c hc) →
        ∀ᶠ n : ℕ in atTop,
          f n ≤ upperEndpoint n (upperTailLength c n)) :=
  bankPaperCapacitySelectedDepth_spec hc

/-! ## Selected-depth canonical continuation -/

example
    (hcontinuation :
      ∀ (c : ℝ) (hc : C0 < c),
        BankPaperCanonicalPostTangentContinuationAtDepth c
          (bankPaperCapacitySelectedDepth c hc)) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds C0) := by
  simpa only [MainNormalizedLimit] using
    mainNormalizedLimit_of_capacityAwareCanonicalPostTangentContinuation
      hcontinuation

example
    (hcontinuation :
      ∀ (c : ℝ) (hc : C0 < c),
        BankPaperCanonicalPostTangentContinuationAtDepth c
          (bankPaperCapacitySelectedDepth c hc)) :
    mainError =o[atTop] secondOrderScale := by
  simpa only [MainAsymptotic] using
    mainAsymptotic_of_capacityAwareCanonicalPostTangentContinuation
      hcontinuation

/-! ## Sharp-defect selected-depth terminal -/

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ (c : ℝ) (hc : C0 < c),
          BankPaperCanonicalPostTangentContinuationAtDepth c
            (bankPaperCapacitySelectedDepth c hc)) :
    Tendsto
      (fun n : ℕ =>
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds C0) := by
  simpa only [MainNormalizedLimit] using
    mainNormalizedLimit_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation
      hC hdefect hselectorGeometry

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ (c : ℝ) (hc : C0 < c),
          BankPaperCanonicalPostTangentContinuationAtDepth c
            (bankPaperCapacitySelectedDepth c hc)) :
    mainError =o[atTop] secondOrderScale := by
  simpa only [MainAsymptotic] using
    mainAsymptotic_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation
      hC hdefect hselectorGeometry

end

end Erdos390.WholePaper
