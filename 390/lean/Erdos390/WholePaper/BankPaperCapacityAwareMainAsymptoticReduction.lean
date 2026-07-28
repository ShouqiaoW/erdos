import Erdos390.WholePaper.BankPaperMainAsymptoticReduction

/-!
# Capacity-aware final main-asymptotic reduction

The existing capacity theorem chooses one admissible depth separately for
each paper scale `c > C0`.  The older final reduction asks for a canonical
post-tangent continuation at every depth at least `201`, although its proof
uses the continuation only at the depth chosen by that capacity theorem.

This file preserves the dependency order exposed by
`exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation`.
It canonically names one depth satisfying the theorem's existential
conclusion and records:

* the selected depth and its lower bound;
* the exact bridge saying that continuation at this depth yields the
  eventual upper endpoint bound.

The remaining supplier premise asks for continuation only at this named
depth.  It contains no universal depth quantifier and assumes neither an
eventual upper bound nor an asymptotic conclusion.
-/

open Filter

namespace Erdos390.WholePaper

noncomputable section

/-! ## One named capacity-selected depth -/

/-- The least depth satisfying the exact public bridge returned
existentially by the capacity theorem.  Naming this witness lets downstream
Section 9 construction target one depth without using a universal
continuation premise. -/
def bankPaperCapacitySelectedDepth
    (c : ℝ) (hc : C0 < c) : ℕ := by
  classical
  exact Nat.find
    (exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
      hc)

/-- The named capacity-selected depth retains both its paper lower bound and
the exact continuation-to-upper-endpoint bridge. -/
theorem bankPaperCapacitySelectedDepth_spec
    {c : ℝ} (hc : C0 < c) :
    201 ≤ bankPaperCapacitySelectedDepth c hc ∧
      (BankPaperCanonicalPostTangentContinuationAtDepth c
            (bankPaperCapacitySelectedDepth c hc) →
        ∀ᶠ n : ℕ in atTop,
          f n ≤ upperEndpoint n (upperTailLength c n)) := by
  classical
  unfold bankPaperCapacitySelectedDepth
  exact Nat.find_spec
    (exists_depth_bankPaper_f_le_upperEndpoint_of_canonicalPostTangentContinuation
      hc)

/-! ## Selected-depth canonical continuation -/

/-- Canonical post-tangent continuation at only the named capacity-selected
depth for each paper scale suffices for the exact normalized limit. -/
theorem mainNormalizedLimit_of_capacityAwareCanonicalPostTangentContinuation
    (hcontinuation :
      ∀ (c : ℝ) (hc : C0 < c),
        BankPaperCanonicalPostTangentContinuationAtDepth c
          (bankPaperCapacitySelectedDepth c hc)) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  exact (bankPaperCapacitySelectedDepth_spec hc).2
    (hcontinuation c hc)

/-- Capacity-selected continuation form of the paper's literal small-`o`
main theorem. -/
theorem mainAsymptotic_of_capacityAwareCanonicalPostTangentContinuation
    (hcontinuation :
      ∀ (c : ℝ) (hc : C0 < c),
        BankPaperCanonicalPostTangentContinuationAtDepth c
          (bankPaperCapacitySelectedDepth c hc)) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_capacityAwareCanonicalPostTangentContinuation
      hcontinuation)

/-! ## Sharp-defect terminal with selected-depth geometry -/

/-- The explicit sharp Saias defect together with selector/geometry
construction only at the capacity-selected depth implies the exact
normalized main limit. -/
theorem
    mainNormalizedLimit_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ (c : ℝ) (hc : C0 < c),
          BankPaperCanonicalPostTangentContinuationAtDepth c
            (bankPaperCapacitySelectedDepth c hc)) :
    MainNormalizedLimit := by
  apply mainNormalizedLimit_of_capacityAwareCanonicalPostTangentContinuation
  exact hselectorGeometry
    (roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect hC hdefect)

/-- The same sharp-defect and capacity-selected selector/geometry reduction
with the paper's literal small-`o` conclusion. -/
theorem
    mainAsymptotic_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hselectorGeometry :
      RoughSaiasEndpointApproximationUpToFive
          (roughSaiasInvLogSqEndpointRate C)
          (roughSaiasInvLogSqEndpointCutoff Y₀) →
        ∀ (c : ℝ) (hc : C0 < c),
          BankPaperCanonicalPostTangentContinuationAtDepth c
            (bankPaperCapacitySelectedDepth c hc)) :
    MainAsymptotic :=
  mainAsymptotic_iff_mainNormalizedLimit.mpr
    (mainNormalizedLimit_of_sharpSaiasDefect_and_capacityAwareSelectorGeometryContinuation
      hC hdefect hselectorGeometry)

end

end Erdos390.WholePaper
