import Erdos536.QuadraticPrimeBandFirstMomentConcrete
import Erdos536.PrimeBandProfileEndpoint

/-!
# Final quadratic moment assembly

The first-moment construction is already fully concrete.  This module
isolates the exact remaining collision interface and proves that it
implies the quadratic moment hypothesis, hence the main theorem.
-/

open Filter

noncomputable section

namespace Erdos536

/-- Exact collision estimate still required of the concrete quadratic
anchor event.  The constant may depend on the requested balance
tolerance, but not on the scale or the missing-petal index. -/
def HasEventuallyQuadraticAnchorCollisionBounds : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
        fiveRootCollision
            (quadraticProfilePrimeBand T) reciprocalBernoulli
            (quadraticAnchorEvent T
              (quadraticDelayedProfileHorizon T) η) s ≤
          C * quadraticAnchorWidth T η ^ 4

/-- The concrete first moment and the displayed collision interface give
the precise uniform quadratic prime-band moment bounds. -/
theorem eventuallyUniformQuadraticPrimeBandMomentBounds_of_anchorCollision
    (hcollision : HasEventuallyQuadraticAnchorCollisionBounds) :
    HasEventuallyUniformQuadraticPrimeBandMomentBounds := by
  intro η hη
  obtain ⟨C, hC, hcollisionη⟩ := hcollision η hη
  let c : ℝ :=
    quadraticConcreteAnchorBaseMassLower *
        (1 / 400 : ℝ) ^ 2 / 4
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos
      (mul_pos quadraticConcreteAnchorBaseMassLower_pos
        (sq_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 400)))
      (by norm_num)
  have hfirst :=
    eventually_quadraticConcreteAnchorFirstMomentPackage
      hη quadraticDelayedProfileHorizon
  have hboth :
      ∀ᶠ T : ℕ in atTop,
        (0 < quadraticAnchorWidth T η ∧
          FiveEventHasPetals
            (quadraticProfilePrimeBand T)
            (quadraticAnchorEvent T
              (quadraticDelayedProfileHorizon T) η) ∧
          FiveEventPetalLogBalanced
            (quadraticProfilePrimeBand T)
            (quadraticAnchorEvent T
              (quadraticDelayedProfileHorizon T) η) η ∧
          c * quadraticAnchorWidth T η ^ 2 ≤
            fiveEventMass
              (quadraticProfilePrimeBand T) reciprocalBernoulli
              (quadraticAnchorEvent T
                (quadraticDelayedProfileHorizon T) η)) ∧
        (∀ s : Fin 3,
          fiveRootCollision
              (quadraticProfilePrimeBand T) reciprocalBernoulli
              (quadraticAnchorEvent T
                (quadraticDelayedProfileHorizon T) η) s ≤
            C * quadraticAnchorWidth T η ^ 4) := by
    filter_upwards [hfirst, hcollisionη] with T hfirstT hcollisionT
    simpa only [c] using ⟨hfirstT, hcollisionT⟩
  rw [Filter.eventually_atTop] at hboth
  obtain ⟨T₀, hT₀⟩ := hboth
  refine ⟨1, c, C, T₀, hc, hC, ?_⟩
  intro T hT
  have hTdata := hT₀ T hT
  refine
    ⟨quadraticAnchorWidth T η,
      quadraticAnchorEvent T
        (quadraticDelayedProfileHorizon T) η,
      hTdata.1.1, ?_, ?_, ?_, ?_⟩
  · simpa only [quadraticProfilePrimeBand] using hTdata.1.2.1
  · simpa only [quadraticProfilePrimeBand] using hTdata.1.2.2.1
  · simpa only [quadraticProfilePrimeBand] using hTdata.1.2.2.2
  · intro s
    simpa only [quadraticProfilePrimeBand] using hTdata.2 s

/-- Once the concrete anchor collision estimate is proved, Erdős 536
follows with no further analytic input. -/
theorem mainTheorem_of_eventuallyQuadraticAnchorCollision
    (hcollision : HasEventuallyQuadraticAnchorCollisionBounds) :
    MainTheorem :=
  mainTheorem_of_quadraticPrimeBandMomentBounds
    (eventuallyUniformQuadraticPrimeBandMomentBounds_of_anchorCollision
      hcollision)

end Erdos536
