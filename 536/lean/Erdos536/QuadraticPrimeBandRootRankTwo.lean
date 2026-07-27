import Erdos536.PrimeBandRootRankTwoMassBound
import Erdos536.QuadraticPrimeBandRootEndpoint

/-!
# Concrete quadratic rank-two root mass

This specializes the exact two-pivot marking count and asymmetric
reciprocal-window estimate to the delayed quadratic profile.
-/

noncomputable section

namespace Erdos536

theorem quadraticPrimeBandRootGoodRankTwoMass_le
    {T : ℕ} {η : ℝ} (hT : 0 < T)
    (hη : 0 < η)
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    (hdata : QuadraticRootEndpointData T η)
    (s : Fin 3) {i j : ℕ}
    (hij : i < j)
    (hj :
      j < quadraticDelayedPivotCount
        (quadraticDelayedProfileHorizon T)) :
    annealedPrimeBandRootGoodRankTwoMass
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ)
        (quadraticAnchorWidth T η)
        (quadraticDelayedProfileDepths T
          (quadraticDelayedProfileHorizon T))
        quadraticDelayedProfileThresholdAtDepth s i j ≤
      16 * (quadraticDelayedRankWindowConstant η) ^ 2 *
        quadraticAnchorWidth T η ^ 2 *
        ((pivotRankDecay i /
            quadraticDelayedPivotLower i) *
          (pivotRankDecay j /
            quadraticDelayedPivotLower j)) := by
  let C := quadraticDelayedRankWindowConstant η
  let width := quadraticAnchorWidth T η
  let ell := quadraticDelayedPivotLower
  let K :=
    quadraticDelayedPivotCount
      (quadraticDelayedProfileHorizon T)
  have hi : i < K := hij.trans hj
  have hC : 0 ≤ C := by
    exact quadraticDelayedRankWindowConstant_nonneg hη
  have hLP : 0 ≤ C * width / ell i := by
    exact div_nonneg (mul_nonneg hC hdata.width_nonneg)
      (hdata.pivot_lower_pos i hi).le
  have hLQ : 0 ≤ C * width / ell j := by
    exact div_nonneg (mul_nonneg hC hdata.width_nonneg)
      (hdata.pivot_lower_pos j hj).le
  have hbound :=
    annealedPrimeBandRootGoodRankTwoMass_le_decay_mul_windows
      (quadraticPrimeBand_prime T 1)
      (quadraticDelayedProfileDepths T
        (quadraticDelayedProfileHorizon T))
      quadraticDelayedProfileThresholdAtDepth s
      (K := K) hij hj hdata.width_nonneg hLP hLQ
      (fun p : ↥(quadraticProfilePrimeBand T) =>
        ell i ≤
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
      (fun p : ↥(quadraticProfilePrimeBand T) =>
        ell j ≤
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
      (by
        intro S m hgood
        exact quadraticRootGood_pivotCount_le_support_card
          (hchecks _ le_rfl) hgood)
      (by
        intro S m p _hp hgood hrank
        exact quadraticRootGood_depthRank_weight_lower
          hT hchecks hgood hrank hi)
      (by
        intro S m p _hp hgood hrank
        exact quadraticRootGood_depthRank_weight_lower
          hT hchecks hgood hrank hj)
      (hdata.rank_window i hi)
      (hdata.rank_window j hj)
  dsimp only [C, width, ell, K] at hbound ⊢
  calc
    annealedPrimeBandRootGoodRankTwoMass
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ)
          (quadraticAnchorWidth T η)
          (quadraticDelayedProfileDepths T
            (quadraticDelayedProfileHorizon T))
          quadraticDelayedProfileThresholdAtDepth s i j ≤
        (16 * pivotRankDecay i * pivotRankDecay j) *
          ((quadraticDelayedRankWindowConstant η *
                quadraticAnchorWidth T η /
              quadraticDelayedPivotLower i) *
            (quadraticDelayedRankWindowConstant η *
                quadraticAnchorWidth T η /
              quadraticDelayedPivotLower j)) := hbound
    _ = _ := by ring

end Erdos536
