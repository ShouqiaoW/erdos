import Erdos390.Full.PaperCanonicalHeadPhysicalTarget

/-!
# Literal-active-mass variant of the canonical barycentric baseline

`BarycentricTarget.baseline` is the normalized probability allocation used
throughout the existing covariance chain.  The paper's actual bridge uses
the same normalized cell law with total mass `q_n`, generally of order
`n / log n`.  This backward-compatible module supplies that scaled
allocation without changing `BarycentricTarget` or any existing theorem
signature.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit

noncomputable section

namespace PaperGuardCensus.BarycentricTarget

variable {Head : Type*} [Fintype Head] [Nonempty Head]
  {D : StructuredSampleData Head} (T : BarycentricTarget D)

/-- The literal unnormalized baseline with total active mass `q_n`. -/
def activeMassBaseline (q : Real) (hq : 0 < q) : BaselineAllocation D where
  cellMass := fun c => q * T.cellProbability c
  cellMass_pos := fun c => mul_pos hq (T.cellProbability_pos c)

omit [Nonempty Head] in
/-- Scaling changes the total mass from one to the supplied `q_n`. -/
theorem activeMassBaseline_totalMass (q : Real) (hq : 0 < q) :
    (T.activeMassBaseline q hq).totalMass = q := by
  unfold activeMassBaseline BaselineAllocation.totalMass
  rw [← Finset.mul_sum, T.sum_cellProbability, mul_one]

omit [Nonempty Head] in
/-- Scaling leaves the normalized law on the structured cells unchanged. -/
theorem activeMassBaseline_normalizedCellMass
    (q : Real) (hq : 0 < q) (c : Cell Head) :
    (T.activeMassBaseline q hq).normalizedCellMass c =
      T.cellProbability c := by
  unfold BaselineAllocation.normalizedCellMass
  change (q * T.cellProbability c) /
      (T.activeMassBaseline q hq).totalMass = T.cellProbability c
  rw [T.activeMassBaseline_totalMass q hq]
  field_simp [ne_of_gt hq]

omit [Nonempty Head] in
/-- Coordinate weights are scaled by exactly the same active-mass factor. -/
theorem activeMassBaseline_baseWeight
    (q : Real) (hq : 0 < q) (m : D.Sample) :
    (T.activeMassBaseline q hq).baseWeight m =
      q * T.baseline.baseWeight m := by
  unfold BaselineAllocation.baseWeight activeMassBaseline baseline
  ring

omit [Nonempty Head] in
/-- The explicit uniform coordinate realization sums to the literal active
mass. -/
theorem activeMassBaseline_baseWeight_sum (q : Real) (hq : 0 < q) :
    ∑ m, (T.activeMassBaseline q hq).baseWeight m = q := by
  rw [BaselineAllocation.baseWeight_sum,
    T.activeMassBaseline_totalMass q hq]

omit [Nonempty Head] in
/-- For a genuinely unnormalized active mass, the literal allocation cannot
satisfy the old probability-baseline equality.  This pinpoints the interface
which a scaled canonical Proposition 8.7 wrapper must generalize. -/
theorem activeMassBaseline_ne_baseline_of_ne_one
    (q : Real) (hq : 0 < q) (hqOne : q ≠ 1) :
    T.activeMassBaseline q hq ≠ T.baseline := by
  intro hsame
  have hmass := congrArg BaselineAllocation.totalMass hsame
  rw [T.activeMassBaseline_totalMass q hq, T.baseline_totalMass] at hmass
  exact hqOne hmass

end PaperGuardCensus.BarycentricTarget

namespace PaperBridgeFit.BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band] [Nonempty Head]
  (B : BridgeData Head Band)

omit [Nonempty Head] in
/-- A `BridgeData` using the scaled canonical allocation has literal active
mass `q_n`, rather than the normalization artifact `1`. -/
theorem q_eq_of_baseline_eq_activeMassBaseline
    (T : BarycentricTarget B.sampleData)
    (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq) :
    B.q = q := by
  unfold BridgeData.q
  rw [hbaseline, T.activeMassBaseline_totalMass q hq]

/-- The unnormalized physical moment is `q_n` times the prescribed
normalized logarithmic mean. -/
theorem paperMoment_physicalScore_zero_eq_activeMass_mul_mu
    (T : BarycentricTarget B.sampleData)
    (q : Real) (hq : 0 < q)
    (hbaseline : B.baseline = T.activeMassBaseline q hq) :
    B.paperMoment B.physicalScore 0 = q * T.mu := by
  rw [B.paperMoment_physicalScore_zero_eq_cellLogMean_sum]
  rw [B.q_eq_of_baseline_eq_activeMassBaseline T q hq hbaseline]
  have hnormalized : ∀ c : Cell Head,
      B.baseline.normalizedCellMass c =
        T.baseline.normalizedCellMass c := by
    intro c
    rw [hbaseline, T.activeMassBaseline_normalizedCellMass q hq c,
      T.baseline_normalizedCellMass]
  simp_rw [hnormalized]
  rw [T.physicalLogMoment]

/-- Specialization to the paper's explicit head-simplex reserve: its stored
`activeMass` is exactly the total bridge mass. -/
theorem paperMoment_physicalScore_zero_eq_reserveActiveMass_mul_mu
    {P : Finset Nat}
    (Bpaper : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, Bpaper.sampleData.lo sigma =
      ArithmeticModel.physicalBound (I.lower sigma) Bpaper.sampleData.n)
    (hhi : ∀ sigma, Bpaper.sampleData.hi sigma =
      ArithmeticModel.physicalBound (I.upper sigma) Bpaper.sampleData.n)
    (R : HeadSimplexReserve P)
    (K : PhysicalInterpolationTarget I)
    (hbaseline : Bpaper.baseline =
      (Bpaper.barycentricTargetOfPaperData I hlo hhi R K).activeMassBaseline
        R.activeMass R.activeMass_pos) :
    Bpaper.paperMoment Bpaper.physicalScore 0 = R.activeMass * K.mu := by
  exact Bpaper.paperMoment_physicalScore_zero_eq_activeMass_mul_mu
    (Bpaper.barycentricTargetOfPaperData I hlo hhi R K)
    R.activeMass R.activeMass_pos hbaseline

end PaperBridgeFit.BridgeData

end


end Erdos390.Full
