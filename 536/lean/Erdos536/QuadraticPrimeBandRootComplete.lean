import Erdos536.QuadraticPrimeBandRootMass
import Erdos536.QuadraticPrimeBandRootRankOne
import Erdos536.QuadraticPrimeBandRootRankTwo
import Erdos536.QuadraticPrimeBandCollisionFinal

/-!
# Complete quadratic exposed-root estimate

This module packages the concrete fixed-rank estimates into
`QuadraticRootRankBounds`, deduces the eventual exposed-root estimate,
and closes Erdős Problem 536.
-/

open Filter

noncomputable section

namespace Erdos536

/-- The concrete rank-one and rank-two estimates give the complete
rank-bound package at every sufficiently large quadratic cutoff. -/
theorem eventually_quadraticRootRankBounds_complete
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
      QuadraticRootRankBounds T η s := by
  filter_upwards [
    eventually_gt_atTop 0,
    eventually_quadraticDelayedProfileHorizon_checks,
    eventually_quadraticRootEndpointData hη
  ] with T hT hchecks hdata
  intro s
  refine
    { rankTwo := ?_
      rankOne := ?_ }
  · intro i _hi j hj hij
    exact quadraticPrimeBandRootGoodRankTwoMass_le
      hT hη hchecks hdata s hij hj
  · intro i hi
    exact quadraticPrimeBandRootGoodRankOneBeforeMass_le
      hT hchecks hdata s hi

/-- The concrete quadratic exposed-root masses are eventually bounded
by a uniform constant times the square of the anchor width. -/
theorem quadraticRootGoodMassBounds_complete :
    HasEventuallyQuadraticRootGoodMassBounds := by
  intro η hη
  refine
    ⟨quadraticRootEndpointConstant η,
      quadraticRootEndpointConstant_nonneg hη, ?_⟩
  have hmass :=
    eventually_quadraticPrimeBandRootGoodMass_le_of_rankBounds
      hη (eventually_quadraticRootRankBounds_complete hη)
  filter_upwards [hmass] with T hmassT
  intro s
  simpa only [quadraticPrimeBandRootGoodMass] using hmassT s

/-- Erdős Problem 536. -/
theorem erdos536_complete : MainTheorem :=
  mainTheorem_of_eventuallyQuadraticRootGoodMass
    quadraticRootGoodMassBounds_complete

end Erdos536
