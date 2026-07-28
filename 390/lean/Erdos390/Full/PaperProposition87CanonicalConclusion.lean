import Erdos390.Full.PaperProposition87CanonicalTwoStageAssembly

/-!
# Literal endpoint package for paper Proposition 8.7

This is only a name for the conjunction proved by the exact finite ODE
assembly.  Every field is stated with the actual `BridgeData` moments,
weights, and valuation statistics.  In particular this is not a stylized
surrogate for Proposition 8.7; it is the reusable paper-level endpoint which
the canonical eventual theorem will produce.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The complete literal conclusion of the physically centered
fixed-partition fit.  The path clauses retain the stronger information used
to prove feasibility, while the endpoint clauses are exactly the paper's
moment, residual, frozen-layer, mass, and quota conclusions. -/
def HasPhysicallyCenteredFixedPartitionFit
    [Nonempty Head]
    {Fixed : Type*} [Fintype Fixed]
    (Delta : Band → ℝ) (a : NNReal)
    (monitoredPrimes : Finset ℕ)
    (markedTarget : ℕ → ℝ) (N Cpost : ℝ)
    (fixedValue : Fixed → ℕ) (fixedWeight : Fixed → ℝ)
    (quota : ℤ) : Prop :=
  ∃ path : ℝ → B.ParamSpace,
    path 0 = 0 ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt path
        (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
        (Icc (0 : ℝ) 1) t) ∧
    (∀ j : Band,
      B.paperMoment (B.bandScore j) (path 1) =
        B.paperMoment (B.bandScore j) 0 + Delta j) ∧
    B.paperMoment B.physicalScore (path 1) =
      B.paperMoment B.physicalScore 0 ∧
    B.paperMoment B.ordinaryLogScore (path 1) =
      B.paperMoment B.ordinaryLogScore 0 ∧
    (∀ h : B.HeadIndex,
      B.paperMoment (B.headIndicator h.1) (path 1) =
        B.paperMoment (B.headIndicator h.1) 0) ∧
    (∀ p : ℕ, p.Prime → p ≤ B.sampleData.W →
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0) ∧
    B.paperMoment B.primeLogScore (path 1) =
      B.paperMoment B.primeLogScore 0 ∧
    (∀ p ∈ monitoredPrimes,
      |markedTarget p - B.paperMoment (B.markedValuation p) (path 1)| ≤
        Cpost * N / ((p : ℝ) * B.L)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ x : ℕ,
      B.ambientCombinedWeight
          (frozenAmbientWeight fixedValue fixedWeight)
          (path t) x ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ f : Fixed,
      B.combinedWeight fixedWeight (path t) (Sum.inl f) =
        B.combinedWeight fixedWeight 0 (Sum.inl f)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      (∑ m : B.sampleData.Sample,
        B.activeCoordinateWeight (path t) m) = B.q) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      (∑ x : Fixed ⊕ B.sampleData.Sample,
        B.combinedWeight fixedWeight (path t) x) = (quota : ℝ)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
