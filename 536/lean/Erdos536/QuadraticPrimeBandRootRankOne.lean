import Erdos536.PrimeBandRootRankOneMass
import Erdos536.QuadraticPrimeBandRootEndpoint

/-!
# Concrete quadratic rank-one root mass

This is the direct specialization of the canonical one-pivot window
estimate to the delayed quadratic profile.
-/

noncomputable section

namespace Erdos536

theorem quadraticPrimeBandRootGoodRankOneBeforeMass_le
    {T : ℕ} {η : ℝ} (hT : 0 < T)
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    (hdata : QuadraticRootEndpointData T η)
    (s : Fin 3) {i : ℕ}
    (hi :
      i < quadraticDelayedPivotCount
        (quadraticDelayedProfileHorizon T)) :
    annealedPrimeBandRootGoodRankOneBeforeMass
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ)
        (quadraticAnchorWidth T η)
        (quadraticDelayedProfileDepths T
          (quadraticDelayedProfileHorizon T))
        quadraticDelayedProfileThresholdAtDepth s i
        (quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T)) ≤
      8 * quadraticDelayedRankWindowConstant η *
        quadraticAnchorWidth T η *
        (1 / 3 : ℝ) ^
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T) *
        (pivotRankDecay i /
          quadraticDelayedPivotLower i) := by
  apply annealedPrimeBandRootGoodRankOneBeforeMass_le_of_window
    (quadraticPrimeBand_prime T 1)
    hdata.width_nonneg hi
  · intro S m hgood
    exact quadraticRootGood_pivotCount_le_support_card
      (hchecks _ le_rfl) hgood
  · intro S m q _hq hgood hrank
    exact quadraticRootGood_depthRank_weight_lower
      hT hchecks hgood hrank hi
  · exact hdata.rank_window i hi

end Erdos536
