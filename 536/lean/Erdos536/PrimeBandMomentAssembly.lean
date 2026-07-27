import Erdos536.PrimeBandAssembly
import Erdos536.FiveStateRooted

/-!
# Assembly from first moments and rooted collisions

The analytic part of the prime-band argument naturally produces an event
mass of order `w^2` and an annealed rooted collision of order `w^4`.
Their ratio is the uniform conditioned rooted second moment required by
alternative-band flattening.  This file makes that last calculation exact.
-/

namespace Erdos536

open PrimeBandTimeChange

/-- Exact eventual input in the natural first-moment/collision scale. -/
def HasEventuallyUniformPrimeBandMomentBounds : Prop :=
  ∀ (η : ℝ), 0 < η →
    ∃ (a c C : ℝ) (T₀ : ℕ),
      0 < c ∧ 0 ≤ C ∧
      ∀ T : ℕ, T₀ ≤ T →
        ∃ (w : ℝ)
          (B : FiveConfiguration (broadPrimeBand T a) → Bool),
          0 < w ∧
          FiveEventHasPetals (broadPrimeBand T a) B ∧
          FiveEventPetalLogBalanced
            (broadPrimeBand T a) B η ∧
          c * w ^ 2 ≤
            fiveEventMass
              (broadPrimeBand T a) reciprocalBernoulli B ∧
          ∀ s : Fin 3,
            fiveRootCollision
              (broadPrimeBand T a) reciprocalBernoulli B s ≤
                C * w ^ 4

theorem broadPrimeBand_prime (T : ℕ) (a : ℝ) :
    IsPrimeSupport (broadPrimeBand T a) := by
  intro p hp
  exact (mem_broadPrimeBand.mp hp).1

/-- Uniform first moments and rooted collisions imply the precise
conditioned-second-moment interface used by the finite assembly. -/
theorem eventuallyUniformPrimeBandEstimates_of_momentBounds
    (hmoment : HasEventuallyUniformPrimeBandMomentBounds) :
    HasEventuallyUniformPrimeBandEstimates := by
  intro η hη
  obtain ⟨a, c, C, T₀, hc, hC, hmomentη⟩ :=
    hmoment η hη
  refine ⟨a, C / c ^ 2, T₀, div_nonneg hC (sq_nonneg c), ?_⟩
  intro T hT
  obtain ⟨w, B, hw, hpetals, hbalanced, hmass, hcollision⟩ :=
    hmomentη T hT
  have hP : IsPrimeSupport (broadPrimeBand T a) :=
    broadPrimeBand_prime T a
  have hr0 :
      ∀ p ∈ broadPrimeBand T a,
        0 ≤ reciprocalBernoulli p :=
    fun p _hp ↦ reciprocalBernoulli_nonneg p
  have hr1 :
      ∀ p ∈ broadPrimeBand T a,
        reciprocalBernoulli p ≤ 1 := by
    intro p hp
    exact (reciprocalBernoulli_lt_one (hP p hp).pos).le
  have hμ :
      ∀ S : Finset ↥(broadPrimeBand T a),
        subtypeBernoulliWeight
          (broadPrimeBand T a) reciprocalBernoulli S ≠ 0 := by
    intro S
    exact (subtypeBernoulliWeight_pos
      (fun _p _hp ↦ reciprocalBernoulli_pos)
      (fun p hp ↦ reciprocalBernoulli_lt_one
        (hP p hp).pos) S).ne'
  have hpositive :
      0 < fiveEventMass
        (broadPrimeBand T a) reciprocalBernoulli B := by
    have hcw : 0 < c * w ^ 2 := mul_pos hc (sq_pos_of_pos hw)
    exact hcw.trans_le hmass
  refine ⟨B, hpetals, hpositive, hbalanced, ?_⟩
  intro s
  exact fiveConditionedRootDensity_secondMoment_le_of_scale
    hr0 hr1 hμ hc hw hmass (hcollision s)

/-- Final theorem-facing form of the natural moment estimates. -/
theorem mainTheorem_of_eventuallyUniformPrimeBandMomentBounds
    (hmoment : HasEventuallyUniformPrimeBandMomentBounds) :
    MainTheorem :=
  mainTheorem_of_eventuallyUniformPrimeBandEstimates
    (eventuallyUniformPrimeBandEstimates_of_momentBounds hmoment)

end Erdos536
