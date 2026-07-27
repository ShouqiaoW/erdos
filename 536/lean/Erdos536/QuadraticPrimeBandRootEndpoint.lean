import Erdos536.QuadraticPrimeBandRankWindow

/-!
# Analytic endpoint package for the quadratic root estimate

This module collects the purely analytic data used after the canonical
nine-mark rank decomposition.  The finite combinatorics only has to
produce the rank-two, rank-one, and rank-zero majorant displayed in
`quadraticRootMass_le_of_canonical_decomposition`.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos536

/-- The explicit constant obtained from the moving-rank window constant,
the summable delayed-pivot profile, and unit endpoint decay. -/
def quadraticRootEndpointConstant (η : ℝ) : ℝ :=
  primeBandRootSmallBallConstant
    ((quadraticDelayedRankWindowConstant η) ^ 2)
    (quadraticDelayedRankWindowConstant η)
    quadraticDelayedPivotSeriesBound 1 1

theorem quadraticRootEndpointConstant_nonneg
    {η : ℝ} (hη : 0 < η) :
    0 ≤ quadraticRootEndpointConstant η := by
  have hwindow :
      0 ≤ quadraticDelayedRankWindowConstant η :=
    quadraticDelayedRankWindowConstant_nonneg hη
  have hseries :
      0 ≤ quadraticDelayedPivotSeriesBound :=
    quadraticDelayedPivotSeriesBound_nonneg
  unfold quadraticRootEndpointConstant
    primeBandRootSmallBallConstant
  positivity

/-- All eventual analytic facts consumed by the canonical root-mass
decomposition, at a fixed quadratic parameter `T`. -/
structure QuadraticRootEndpointData (T : ℕ) (η : ℝ) : Prop where
  width_nonneg :
    0 ≤ quadraticAnchorWidth T η
  endpoint_mem :
    quadraticDelayedProfileEndpointDepth T ∈
      quadraticDelayedProfileDepths T
        (quadraticDelayedProfileHorizon T)
  endpoint_threshold_pos :
    1 ≤ quadraticDelayedProfileThresholdAtDepth
      (quadraticDelayedProfileEndpointDepth T)
  pivot_lower_pos :
    ∀ i <
        quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T),
      0 < quadraticDelayedPivotLower i
  pivot_series_le :
    pivotRankSeries quadraticDelayedPivotLower
        (quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T)) ≤
      quadraticDelayedPivotSeriesBound
  endpoint_decay :
    (1 / 3 : ℝ) ^
        quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T) ≤
      quadraticAnchorWidth T η
  rank_window :
    ∀ i : ℕ,
      i <
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T) →
      ∀ x : ℝ,
        reciprocalWindowMassAlong
            Finset.univ
            (fun p : ↥(quadraticProfilePrimeBand T) => p.1)
            (fun p : ↥(quadraticProfilePrimeBand T) =>
              normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
            (fun p : ↥(quadraticProfilePrimeBand T) =>
              quadraticDelayedPivotLower i ≤
                normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
            x (4 * quadraticAnchorWidth T η) ≤
          quadraticDelayedRankWindowConstant η *
              quadraticAnchorWidth T η /
            quadraticDelayedPivotLower i

/-- The endpoint, rank-series, and moving-window estimates hold
simultaneously for the concrete delayed quadratic profile. -/
theorem eventually_quadraticRootEndpointData
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, QuadraticRootEndpointData T η := by
  filter_upwards [
    eventually_quadraticDelayedProfileEndpointData hη,
    eventually_quadraticDelayedRank_reciprocalWindow_le hη
  ] with T hendpoint hwindow
  refine
    { width_nonneg := ?_
      endpoint_mem := hendpoint.1
      endpoint_threshold_pos := hendpoint.2.1
      pivot_lower_pos := ?_
      pivot_series_le := ?_
      endpoint_decay := ?_
      rank_window := hwindow }
  · unfold quadraticAnchorWidth
    exact div_nonneg hη.le (Nat.cast_nonneg _)
  · intro i _hi
    exact quadraticDelayedPivotLower_pos i
  · exact quadraticDelayedPivotRankSeries_le _
  · simpa only [
      quadraticAnchorWidth,
      quadraticDelayedProfileEndpointDepth,
      quadraticDelayedProfileThresholdAtDepth_eq,
      quadraticDelayedPivotCount] using hendpoint.2.2

/-- Once finite combinatorics supplies the canonical three-term
decomposition, the analytic endpoint package turns it into the desired
quadratic small-ball bound. -/
theorem quadraticRootMass_le_of_canonical_decomposition
    {T : ℕ} {η rootMass : ℝ}
    (hη : 0 < η)
    (hdata : QuadraticRootEndpointData T η)
    (hdecompose :
      rootMass ≤
        twoPivotRankContribution quadraticDelayedPivotLower
            (quadraticDelayedPivotCount
              (quadraticDelayedProfileHorizon T))
            ((quadraticDelayedRankWindowConstant η) ^ 2)
            (quadraticAnchorWidth T η) +
          onePivotRankContribution quadraticDelayedPivotLower
            (quadraticDelayedPivotCount
              (quadraticDelayedProfileHorizon T))
            (quadraticDelayedRankWindowConstant η)
            (quadraticAnchorWidth T η) +
          quadraticAnchorWidth T η ^ 2) :
    rootMass ≤
      quadraticRootEndpointConstant η *
        quadraticAnchorWidth T η ^ 2 := by
  have hbound :=
    rootSmallBall_le_explicit_constant
      (rootMass := rootMass)
      (ell := quadraticDelayedPivotLower)
      (K := quadraticDelayedPivotCount
        (quadraticDelayedProfileHorizon T))
      (Ctwo := (quadraticDelayedRankWindowConstant η) ^ 2)
      (Cone := quadraticDelayedRankWindowConstant η)
      (w := quadraticAnchorWidth T η)
      (L := quadraticDelayedPivotSeriesBound)
      (Eone := 1) (Ezero := 1)
      hdata.pivot_lower_pos
      (sq_nonneg _)
      (quadraticDelayedRankWindowConstant_nonneg hη)
      hdata.width_nonneg
      quadraticDelayedPivotSeriesBound_nonneg
      (by norm_num)
      hdata.pivot_series_le
      (by simpa using hdata.endpoint_decay)
      (by simpa using hdecompose)
  simpa only [quadraticRootEndpointConstant] using hbound

/-- Eventual form of
`quadraticRootMass_le_of_canonical_decomposition`.  The decomposition may
itself hold only eventually, which is the natural interface for the
prime-band estimates. -/
theorem eventually_quadraticRootMass_le_of_canonical_decomposition
    {η : ℝ} (hη : 0 < η)
    (rootMass : ℕ → ℝ)
    (hdecompose :
      ∀ᶠ T : ℕ in atTop,
        rootMass T ≤
          twoPivotRankContribution quadraticDelayedPivotLower
              (quadraticDelayedPivotCount
                (quadraticDelayedProfileHorizon T))
              ((quadraticDelayedRankWindowConstant η) ^ 2)
              (quadraticAnchorWidth T η) +
            onePivotRankContribution quadraticDelayedPivotLower
              (quadraticDelayedPivotCount
                (quadraticDelayedProfileHorizon T))
              (quadraticDelayedRankWindowConstant η)
              (quadraticAnchorWidth T η) +
            quadraticAnchorWidth T η ^ 2) :
    ∀ᶠ T : ℕ in atTop,
      rootMass T ≤
        quadraticRootEndpointConstant η *
          quadraticAnchorWidth T η ^ 2 := by
  filter_upwards [
    eventually_quadraticRootEndpointData hη,
    hdecompose
  ] with T hdataT hdecomposeT
  exact quadraticRootMass_le_of_canonical_decomposition
    hη hdataT hdecomposeT

end Erdos536
