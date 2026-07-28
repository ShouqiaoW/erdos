import Erdos390.Full.PaperCanonicalBaseline
import Erdos390.Full.PaperBridgeCellTiltDecomposition

/-!
# The canonical baseline inside the literal bridge law

This file identifies the finite-cell logarithmic averages used by the
barycentric construction with the actual conditional physical means and
with the physical moment of the bridge probability law at parameter zero.
-/

open scoped BigOperators

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

namespace PaperBridgeFit.BridgeData

/-- The actual coarse conditional physical mean is the literal uniform
average over the corresponding guard-deleted cell.  In particular, it is
independent of the positive baseline mass assigned to that cell. -/
theorem cellPhysicalMean_eq_cellLogMean [Nonempty Head]
    (B : BridgeData Head Band) (c : Cell Head) :
    B.cellPhysicalMean c = cellLogMean B.sampleData c := by
  have hmoment := B.cellPhysicalMean_mul_weight c
  rw [B.nuisanceCoarseBaseline_weight c] at hmoment
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) =
        B.baseline.normalizedCellMass c * cellLogMean B.sampleData c := by
    change (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
        B.sampleData.cellOf m = c,
      B.vectorFamily.probabilityMass 0 m * B.physicalScore m) = _
    simp_rw [B.probabilityMass_zero]
    rw [Finset.sum_filter, Fintype.sum_sigma]
    simp only [StructuredSampleData.cellOf]
    rw [Finset.sum_eq_single c]
    · simp only [if_true, BaselineAllocation.baseWeight,
        BaselineAllocation.normalizedCellMass, BridgeData.q,
        BridgeData.physicalScore, StructuredSampleData.value, cellLogMean]
      have hcard :
          (Fintype.card (B.sampleData.SampleAt c) : ℝ) ≠ 0 := by
        exact_mod_cast
          (Nat.ne_of_gt (B.sampleData.sampleAt_card_pos c))
      have hmass : B.baseline.totalMass ≠ 0 :=
        ne_of_gt B.baseline.totalMass_pos
      simp only [StructuredSampleData.cellOf]
      rw [← Finset.mul_sum]
      field_simp [hcard, hmass]
    · intro c' hc' hne
      simp [hne]
    · intro hc
      exact (hc (Finset.mem_univ c)).elim
  rw [hsum] at hmoment
  exact mul_left_cancel₀ (ne_of_gt
    (B.baseline.normalizedCellMass_pos c)) hmoment

/-- The uniform law on a literal guarded bridge cell has physical expectation
equal to the counting average used in `cellLogMean`. -/
theorem guardedCellProbability_expect_physicalScore_eq_cellLogMean
    [Nonempty Head] (B : BridgeData Head Band) (c : Cell Head) :
    (B.guardedCellProbability c).expect
        (fun m ↦ B.physicalScore ⟨c, m⟩) =
      cellLogMean B.sampleData c := by
  unfold BridgeData.guardedCellProbability
  rw [FiniteProbability.uniformOnFinset_expect_eq]
  unfold cellLogMean BridgeData.physicalScore StructuredSampleData.value
  rw [Fintype.card_coe]

/-- At parameter zero, the active physical moment is the active mass times
the barycentric average of the actual guarded-cell logarithmic means. -/
theorem paperMoment_physicalScore_zero_eq_cellLogMean_sum
    [Nonempty Head] (B : BridgeData Head Band) :
    B.paperMoment B.physicalScore 0 =
      B.q * ∑ c : Cell Head,
        B.baseline.normalizedCellMass c * cellLogMean B.sampleData c := by
  unfold BridgeData.paperMoment
  rw [FiniteExponentialFamily.moment_eq_baseMass_mul_expectation]
  change B.vectorFamily.baseMass *
      (B.tiltedLaw 0).expect B.physicalScore = _
  rw [B.vectorFamily_baseMass]
  rw [← B.baselineSigmaProbability_eq_tiltedLaw_zero]
  unfold BridgeData.baselineSigmaProbability
  rw [FiniteProbability.sigmaMixture_expect]
  apply congrArg (B.q * ·)
  apply Finset.sum_congr rfl
  intro c hc
  rw [B.baselineCellProbability_mass,
    B.guardedCellProbability_expect_physicalScore_eq_cellLogMean c]

/-- For the canonical barycentric baseline, the literal bridge moment at zero
is exactly the prescribed physical target. -/
theorem paperMoment_physicalScore_zero_eq_mu
    [Nonempty Head] (B : BridgeData Head Band)
    (T : BarycentricTarget B.sampleData)
    (hbaseline : B.baseline = T.baseline) :
    B.paperMoment B.physicalScore 0 = T.mu := by
  rw [B.paperMoment_physicalScore_zero_eq_cellLogMean_sum]
  have hq : B.q = 1 := by
    unfold BridgeData.q
    rw [hbaseline, T.baseline_totalMass]
  rw [hq, one_mul]
  have hnormalized : ∀ c : Cell Head,
      B.baseline.normalizedCellMass c =
        T.baseline.normalizedCellMass c := by
    intro c
    rw [hbaseline]
  simp_rw [hnormalized]
  exact T.physicalLogMoment

end PaperBridgeFit.BridgeData

end

end Erdos390.Full
