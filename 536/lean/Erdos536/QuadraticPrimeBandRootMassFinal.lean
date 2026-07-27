import Erdos536.QuadraticPrimeBandRootMass
import Erdos536.QuadraticPrimeBandRootRankOne
import Erdos536.QuadraticPrimeBandRootRankTwo
import Erdos536.QuadraticPrimeBandCollisionFinal

/-!
# Final concrete quadratic root estimate

This module inserts the exact fixed-rank factorial-insertion bounds into
the quadratic endpoint assembly and exports the unconditional rooted
small-ball estimate.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos536

/-- The concrete one- and two-pivot bounds hold simultaneously at all
sufficiently large quadratic cutoffs. -/
theorem eventually_quadraticRootRankBounds
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
      QuadraticRootRankBounds T η s := by
  filter_upwards [
    eventually_quadraticRootEndpointData hη,
    eventually_quadraticDelayedProfileHorizon_checks,
    eventually_gt_atTop 0
  ] with T hdata hchecks hT
  intro s
  refine
    { rankTwo := ?_
      rankOne := ?_ }
  · intro i hi j hj hij
    exact quadraticPrimeBandRootGoodRankTwoMass_le
      hT hη hchecks hdata s hij hj
  · intro i hi
    exact quadraticPrimeBandRootGoodRankOneBeforeMass_le
      hT hchecks hdata s hi

/-- Unconditional eventual exposed-root estimate at the quadratic
cutoff. -/
theorem hasEventuallyQuadraticRootGoodMassBounds :
    HasEventuallyQuadraticRootGoodMassBounds := by
  intro η hη
  refine
    ⟨quadraticRootEndpointConstant η,
      quadraticRootEndpointConstant_nonneg hη, ?_⟩
  have hmass :=
    eventually_quadraticPrimeBandRootGoodMass_le_of_rankBounds
      hη (eventually_quadraticRootRankBounds hη)
  filter_upwards [hmass] with T hmassT
  intro s
  simpa only [quadraticPrimeBandRootGoodMass] using hmassT s

/-- Erdős Problem 536. -/
theorem erdos536_mainTheorem : MainTheorem :=
  mainTheorem_of_eventuallyQuadraticRootGoodMass
    hasEventuallyQuadraticRootGoodMassBounds

end Erdos536
