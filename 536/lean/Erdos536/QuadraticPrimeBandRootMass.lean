import Erdos536.PrimeBandRootRankZeroMass
import Erdos536.QuadraticPrimeBandRootEndpoint

/-!
# Concrete quadratic exposed-root mass

This module specializes the canonical support-rank decomposition to the
polynomial cutoff `T^6 < p ≤ exp(T^2)`.  The only translated-prime input
is the moving-rank reciprocal-window estimate already packaged in
`QuadraticRootEndpointData`.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos536

/-- Concrete observation-level root-good mass at the quadratic anchor
scale. -/
noncomputable def quadraticPrimeBandRootGoodMass
    (T : ℕ) (η : ℝ) (s : Fin 3) : ℝ := by
  classical
  exact
    ∑ o : FiveRootObservation (quadraticProfilePrimeBand T),
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
          o (fun _ => True)
      else 0

/-- At the concrete delayed endpoint, every root-good support contains
all advertised canonical pivot ranks. -/
theorem quadraticRootGood_supportCard
    {T : ℕ} {η : ℝ}
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    {s : Fin 3}
    {S : Finset ↥(quadraticProfilePrimeBand T)}
    {m : SupportNineMarking S}
    (hgood :
      PrimeBandRootGood
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ)
        (quadraticAnchorWidth T η)
        (quadraticDelayedProfileDepths T
          (quadraticDelayedProfileHorizon T))
        quadraticDelayedProfileThresholdAtDepth s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m)) :
    quadraticDelayedPivotCount
        (quadraticDelayedProfileHorizon T) ≤ S.card := by
  exact quadraticRootGood_pivotCount_le_support_card
    (hchecks _ le_rfl) hgood

/-- Concrete profile eligibility for any canonical support rank below
the delayed pivot count. -/
theorem quadraticRootGood_rankEligible
    {T : ℕ} (hT : 0 < T)
    {η : ℝ}
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    {s : Fin 3}
    {S : Finset ↥(quadraticProfilePrimeBand T)}
    {m : SupportNineMarking S}
    (hgood :
      PrimeBandRootGood
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ)
        (quadraticAnchorWidth T η)
        (quadraticDelayedProfileDepths T
          (quadraticDelayedProfileHorizon T))
        quadraticDelayedProfileThresholdAtDepth s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m))
    {p : ↥(quadraticProfilePrimeBand T)}
    {i : ℕ}
    (hrank :
      supportDepthRank ((T ^ 2 : ℕ) : ℝ) S p = i)
    (hi :
      i < quadraticDelayedPivotCount
        (quadraticDelayedProfileHorizon T)) :
    quadraticDelayedPivotLower i ≤
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 := by
  exact quadraticRootGood_depthRank_weight_lower
    hT hchecks hgood hrank hi

/-- The truncated-zero part has the required quadratic small-ball
scale, with unit constant. -/
theorem quadraticPrimeBandRootGoodRankZeroMass_le_width_sq
    {T : ℕ} {η : ℝ}
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    (hdata : QuadraticRootEndpointData T η)
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
    exact quadraticRootGood_supportCard hchecks hgood
  have hpow :
      (1 / 9 : ℝ) ^ K =
        ((1 / 3 : ℝ) ^ K) ^ 2 := by
    rw [pow_two, ← mul_pow]
    norm_num
  calc
    annealedPrimeBandRootGoodRankZeroBeforeMass
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ)
          (quadraticAnchorWidth T η)
          (quadraticDelayedProfileDepths T
            (quadraticDelayedProfileHorizon T))
          quadraticDelayedProfileThresholdAtDepth s K ≤
        (1 / 9 : ℝ) ^ K := hzero
    _ = ((1 / 3 : ℝ) ^ K) ^ 2 := hpow
    _ ≤ quadraticAnchorWidth T η ^ 2 := by
      exact (sq_le_sq₀
        (pow_nonneg (by norm_num) K)
        hdata.width_nonneg).2 hdata.endpoint_decay

/-- The two nonzero truncated-rank estimates at one concrete scale. -/
structure QuadraticRootRankBounds
    (T : ℕ) (η : ℝ) (s : Fin 3) : Prop where
  rankTwo :
    ∀ i <
        quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T),
      ∀ j <
        quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T),
        i < j →
        annealedPrimeBandRootGoodRankTwoMass
            (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ)
            (quadraticAnchorWidth T η)
            (quadraticDelayedProfileDepths T
              (quadraticDelayedProfileHorizon T))
            quadraticDelayedProfileThresholdAtDepth
            s i j ≤
          16 *
            (quadraticDelayedRankWindowConstant η) ^ 2 *
            quadraticAnchorWidth T η ^ 2 *
            ((pivotRankDecay i /
                quadraticDelayedPivotLower i) *
              (pivotRankDecay j /
                quadraticDelayedPivotLower j))
  rankOne :
    ∀ i <
        quadraticDelayedPivotCount
          (quadraticDelayedProfileHorizon T),
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
            quadraticDelayedPivotLower i)

/-- Finite concrete assembly once the two fixed-rank estimates and the
truncated-zero estimate have been supplied. -/
theorem quadraticPrimeBandRootGoodMass_le_of_rankBounds
    {T : ℕ} {η : ℝ} (hη : 0 < η)
    (hdata : QuadraticRootEndpointData T η)
    (s : Fin 3)
    (htwo :
      ∀ i <
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T),
        ∀ j <
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T),
          i < j →
          annealedPrimeBandRootGoodRankTwoMass
              (quadraticProfilePrimeBand T)
              ((T ^ 2 : ℕ) : ℝ)
              (quadraticAnchorWidth T η)
              (quadraticDelayedProfileDepths T
                (quadraticDelayedProfileHorizon T))
              quadraticDelayedProfileThresholdAtDepth
              s i j ≤
            16 *
              (quadraticDelayedRankWindowConstant η) ^ 2 *
              quadraticAnchorWidth T η ^ 2 *
              ((pivotRankDecay i /
                  quadraticDelayedPivotLower i) *
                (pivotRankDecay j /
                  quadraticDelayedPivotLower j)))
    (hone :
      ∀ i <
          quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T),
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
              quadraticDelayedPivotLower i))
    (hzero :
      annealedPrimeBandRootGoodRankZeroBeforeMass
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ)
          (quadraticAnchorWidth T η)
          (quadraticDelayedProfileDepths T
            (quadraticDelayedProfileHorizon T))
          quadraticDelayedProfileThresholdAtDepth s
          (quadraticDelayedPivotCount
            (quadraticDelayedProfileHorizon T)) ≤
        quadraticAnchorWidth T η ^ 2) :
    quadraticPrimeBandRootGoodMass T η s ≤
      quadraticRootEndpointConstant η *
        quadraticAnchorWidth T η ^ 2 := by
  classical
  let K :=
    quadraticDelayedPivotCount
      (quadraticDelayedProfileHorizon T)
  have hdecompose :
      quadraticPrimeBandRootGoodMass T η s ≤
        twoPivotRankContribution
            quadraticDelayedPivotLower K
            ((quadraticDelayedRankWindowConstant η) ^ 2)
            (quadraticAnchorWidth T η) +
          onePivotRankContribution
            quadraticDelayedPivotLower K
            (quadraticDelayedRankWindowConstant η)
            (quadraticAnchorWidth T η) +
          quadraticAnchorWidth T η ^ 2 := by
    unfold quadraticPrimeBandRootGoodMass
    have hbound :=
      primeBandRootGoodMass_le_rankContributions
        (quadraticPrimeBand_prime T 1)
        ((T ^ 2 : ℕ) : ℝ)
        (quadraticAnchorWidth T η)
        (quadraticDelayedProfileDepths T
          (quadraticDelayedProfileHorizon T))
        quadraticDelayedProfileThresholdAtDepth s
        quadraticDelayedPivotLower K
        ((quadraticDelayedRankWindowConstant η) ^ 2)
        (quadraticDelayedRankWindowConstant η) 1
        (by
          intro i hi j hj hij
          exact htwo i hi j hj hij)
        (by
          intro i hi
          exact hone i hi)
        (by simpa only [one_mul] using hzero)
    simpa only [K, quadraticProfilePrimeBand,
      one_mul] using hbound
  exact quadraticRootMass_le_of_canonical_decomposition
    hη hdata hdecompose

/-- Structure-valued wrapper around
`quadraticPrimeBandRootGoodMass_le_of_rankBounds`. -/
theorem quadraticPrimeBandRootGoodMass_le_of_rankBoundData
    {T : ℕ} {η : ℝ} (hη : 0 < η)
    (hchecks :
      ∀ k ≤ quadraticDelayedProfileHorizon T,
        k ∈ quadraticDelayedProfileChecks T
          (quadraticDelayedProfileHorizon T))
    (hdata : QuadraticRootEndpointData T η)
    (s : Fin 3)
    (hranks : QuadraticRootRankBounds T η s) :
    quadraticPrimeBandRootGoodMass T η s ≤
      quadraticRootEndpointConstant η *
        quadraticAnchorWidth T η ^ 2 := by
  apply quadraticPrimeBandRootGoodMass_le_of_rankBounds
    hη hdata s hranks.rankTwo hranks.rankOne
  exact quadraticPrimeBandRootGoodRankZeroMass_le_width_sq
    hchecks hdata s

/-- Eventual quadratic root-small-ball bound from eventual fixed-rank
data. -/
theorem eventually_quadraticPrimeBandRootGoodMass_le_of_rankBounds
    {η : ℝ} (hη : 0 < η)
    (hranks :
      ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
        QuadraticRootRankBounds T η s) :
    ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
      quadraticPrimeBandRootGoodMass T η s ≤
        quadraticRootEndpointConstant η *
          quadraticAnchorWidth T η ^ 2 := by
  filter_upwards [
    eventually_quadraticRootEndpointData hη,
    eventually_quadraticDelayedProfileHorizon_checks,
    hranks
  ] with T hdata hchecks hranksT
  intro s
  exact quadraticPrimeBandRootGoodMass_le_of_rankBoundData
    hη hchecks hdata s (hranksT s)

end Erdos536
