import Erdos536.QuadraticPrimeBandMomentFinal
import Erdos536.QuadraticPrimeBandCollision

set_option maxHeartbeats 800000

/-!
# From the exposed-root estimate to the concrete collision bound

This module discharges the missing-petal part of the collision argument
at the fixed first delayed depth.  It leaves only the canonical
nine-mark root small-ball estimate.
-/

open Filter

noncomputable section

namespace Erdos536

/-- Exact remaining root-small-ball interface. -/
noncomputable def HasEventuallyQuadraticRootGoodMassBounds : Prop := by
  classical
  exact
    ∀ η : ℝ, 0 < η →
      ∃ Croot : ℝ, 0 ≤ Croot ∧
        ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
          (∑ o : FiveRootObservation (quadraticProfilePrimeBand T),
            if PrimeBandRootGood
                (quadraticProfilePrimeBand T)
                ((T ^ 2 : ℕ) : ℝ)
                (quadraticAnchorWidth T η)
                (quadraticDelayedProfileDepths T
                  (quadraticDelayedProfileHorizon T))
                quadraticDelayedProfileThresholdAtDepth s o
            then
              finiteFiberMass
                (fiveRootPairAtom
                  (quadraticProfilePrimeBand T)
                  reciprocalBernoulli s)
                (fiveRootObservation
                  (quadraticProfilePrimeBand T) s)
                o (fun _ ↦ True)
            else 0) ≤
          Croot * quadraticAnchorWidth T η ^ 2

/-- A uniform root-small-ball estimate gives the complete concrete
anchor collision estimate. -/
theorem eventuallyQuadraticAnchorCollision_of_rootGoodMass
    (hroot : HasEventuallyQuadraticRootGoodMassBounds) :
    HasEventuallyQuadraticAnchorCollisionBounds := by
  classical
  intro η hη
  obtain ⟨Croot, hCroot, hrootη⟩ := hroot η hη
  let Cwindow : ℝ :=
    quadraticMissingWindowConstant η
      quadraticDelayedProfileFirstDepth
  let C : ℝ := Croot * Cwindow ^ 2
  have hCwindow : 0 ≤ Cwindow := by
    dsimp only [Cwindow]
    exact quadraticMissingWindowConstant_nonneg hη
  have hC : 0 ≤ C :=
    mul_nonneg hCroot (sq_nonneg Cwindow)
  have hfirst :=
    eventually_quadraticDelayedProfileFirstDepth
  have hwindow :=
    eventually_quadraticPrimeBand_reciprocalWindow_le
      (a := (1 : ℝ))
      (η := η) (d := quadraticDelayedProfileFirstDepth) hη
  refine ⟨C, hC, ?_⟩
  filter_upwards [
    hrootη, hfirst, hwindow, eventually_gt_atTop 0
  ] with T hrootT hfirstT hwindowT hT
  intro s
  have hrootT' :
      (∑ o : FiveRootObservation (quadraticPrimeBand T 1),
        if PrimeBandRootGood
            (quadraticPrimeBand T 1)
            ((T ^ 2 : ℕ) : ℝ)
            (η / ((T ^ 2 : ℕ) : ℝ))
            (quadraticDelayedProfileDepths T
              (quadraticDelayedProfileHorizon T))
            quadraticDelayedProfileThresholdAtDepth s o
        then
          finiteFiberMass
            (fiveRootPairAtom
              (quadraticPrimeBand T 1) reciprocalBernoulli s)
            (fiveRootObservation (quadraticPrimeBand T 1) s)
            o (fun _ ↦ True)
        else 0) ≤
      primeBandRootSmallBallConstant 0 0 0 0 Croot *
        (η / ((T ^ 2 : ℕ) : ℝ)) ^ 2 := by
    simpa [quadraticProfilePrimeBand, quadraticAnchorWidth,
      primeBandRootSmallBallConstant] using hrootT s
  have hcollision :=
    quadraticPrimeBandCollision_le_of_twoPivot_and_window
      hT (1 : ℝ) (9 / 20 : ℝ) (11 / 20 : ℝ) η hη
      (quadraticDelayedProfileDepths T
        (quadraticDelayedProfileHorizon T))
      quadraticDelayedProfileThresholdAtDepth
      (hfirstT (quadraticDelayedProfileHorizon T)).1
      (hfirstT (quadraticDelayedProfileHorizon T)).2
      s 0 0 0 0 Croot
      hrootT'
      (hwindowT)
  simpa [
    quadraticProfilePrimeBand,
    quadraticAnchorEvent,
    quadraticAnchorWidth,
    Cwindow, C,
    primeBandRootSmallBallConstant
  ] using hcollision

/-- The canonical exposed-root bound is the last theorem needed for
Erdős 536. -/
theorem mainTheorem_of_eventuallyQuadraticRootGoodMass
    (hroot : HasEventuallyQuadraticRootGoodMassBounds) :
    MainTheorem :=
  mainTheorem_of_eventuallyQuadraticAnchorCollision
    (eventuallyQuadraticAnchorCollision_of_rootGoodMass hroot)

end Erdos536
