import Erdos536.PrimeBandRootRankZeroMass
import Erdos536.QuadraticPrimeBandRootEndpoint

/-!
# Concrete quadratic rank-zero root mass

Endpoint decay turns the exact zero-prefix probability `9⁻ᴷ` into the
required square of the quadratic anchor width.
-/

open scoped BigOperators

noncomputable section

namespace Erdos536

theorem quadraticPrimeBandRootGoodRankZeroBeforeMass_le_width_sq
    {T : ℕ} {η : ℝ}
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    (hendpoint :
      (1 / 3 : ℝ) ^
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T) ≤
        quadraticAnchorWidth T η)
    (hwidth : 0 ≤ quadraticAnchorWidth T η)
    (s : Fin 3) :
    annealedPrimeBandRootGoodRankZeroBeforeMass
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ)
        (quadraticAnchorWidth T η)
        (quadraticDelayedProfileDepths T
          (quadraticDelayedProfileHorizon T))
        quadraticDelayedProfileThresholdAtDepth s
        (quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T)) ≤
      quadraticAnchorWidth T η ^ 2 := by
  classical
  let K :=
    quadraticDelayedPivotCount
      (quadraticDelayedProfileHorizon T)
  have hzero :
      annealedPrimeBandRootGoodRankZeroBeforeMass
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ)
          (quadraticAnchorWidth T η)
          (quadraticDelayedProfileDepths T
            (quadraticDelayedProfileHorizon T))
          quadraticDelayedProfileThresholdAtDepth s K ≤
        (1 / 9 : ℝ) ^ K := by
    apply annealedPrimeBandRootGoodRankZeroBeforeMass_le
      (quadraticPrimeBand_prime T 1)
    intro S m hgood
    exact quadraticRootGood_pivotCount_le_support_card
      (hchecks (quadraticDelayedProfileHorizon T) le_rfl)
      hgood
  have hidentity :
      (1 / 9 : ℝ) ^ K =
        ((1 / 3 : ℝ) ^ K) ^ 2 := by
    calc
      (1 / 9 : ℝ) ^ K =
          ((1 / 3 : ℝ) ^ 2) ^ K := by
        congr 1
        norm_num
      _ = ((1 / 3 : ℝ) ^ K) ^ 2 := by
        rw [← pow_mul, ← pow_mul]
        congr 1
        omega
  have hdecay :
      (1 / 3 : ℝ) ^ K ≤
        quadraticAnchorWidth T η := by
    simpa only [K] using hendpoint
  have hsquare :
      ((1 / 3 : ℝ) ^ K) ^ 2 ≤
        quadraticAnchorWidth T η ^ 2 :=
    (sq_le_sq₀ (pow_nonneg (by norm_num) K) hwidth).2
      hdecay
  exact hzero.trans (hidentity ▸ hsquare)

end Erdos536
