import Erdos390.Full.PaperEffectiveScoreBound
import Erdos390.Full.PaperActualCompensatedRegression
import Erdos390.Full.FiniteProbabilityMixtureTilt
import Erdos390.Full.UniformFiniteProbability

/-!
# Exact cell-mixture decomposition of the paper bridge tilt

The analytic marked-cell estimates are stated for uniform probability laws on
individual structured cells and their finite tagged mixtures.  This file proves
the exact identification with the probability law carried by `BridgeData`.
Nothing asymptotic is used: the guard-deleted cells, their actual cardinalities,
the baseline cell masses, and the global partition-function reweighting all
remain literal.

This is also the place where the remaining nuisance tilt is exposed.  After the
medium-prime score has been split off, the physical/head factor is an explicit
second exponential tilt; it is not silently absorbed into the prime fugacity.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open FiniteProbability ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

private theorem finiteProbability_ext
    {Omega : Type*} [Fintype Omega]
    {mu nu : FiniteProbability Omega} (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk massMu nonnegMu sumMu =>
      cases nu with
      | mk massNu nonnegNu sumNu =>
          dsimp only at h
          subst massNu
          rfl

/-- The literal normalized baseline masses of the finitely many tagged
head/physical cells. -/
def baselineCellProbability [Nonempty Head] :
    FiniteProbability (Cell Head) where
  mass := B.baseline.normalizedCellMass
  mass_nonneg c := (B.baseline.normalizedCellMass_pos c).le
  mass_sum := B.baseline.normalizedCellMass_sum

@[simp] theorem baselineCellProbability_mass [Nonempty Head]
    (c : Cell Head) :
    B.baselineCellProbability.mass c =
      B.baseline.normalizedCellMass c := rfl

/-- Uniform probability on one *actual guard-deleted* bridge cell. -/
def guardedCellProbability (c : Cell Head) :
    FiniteProbability (B.sampleData.SampleAt c) :=
  uniformOnFinset (B.sampleData.cellFinset c)
    (B.sampleData.cell_nonempty c)

@[simp] theorem guardedCellProbability_mass
    (c : Cell Head) (m : B.sampleData.SampleAt c) :
    (B.guardedCellProbability c).mass m =
      1 / (B.sampleData.cellFinset c).card := rfl

/-- The exact baseline probability law obtained by tagging the individual
uniform guard-deleted cell laws. -/
def baselineSigmaProbability [Nonempty Head] :
    FiniteProbability B.sampleData.Sample :=
  sigmaMixture B.baselineCellProbability B.guardedCellProbability

/-- Pointwise equality between the probability law at parameter zero and the
literal tagged mixture.  This checks the cell cardinality normalization rather
than appealing to an informal "uniform within cells" statement. -/
theorem baselineSigmaProbability_mass_eq [Nonempty Head]
    (m : B.sampleData.Sample) :
    B.baselineSigmaProbability.mass m = (B.tiltedLaw 0).mass m := by
  rcases m with ⟨c, m⟩
  change
    (B.baseline.normalizedCellMass c) *
        (1 / ((B.sampleData.cellFinset c).card : ℝ)) =
      B.vectorFamily.probabilityMass 0 ⟨c, m⟩
  rw [B.probabilityMass_zero]
  unfold BaselineAllocation.normalizedCellMass
    BaselineAllocation.baseWeight BridgeData.q
  have hcard : ((B.sampleData.cellFinset c).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (B.sampleData.cell_nonempty c)
  have hq : B.baseline.totalMass ≠ 0 := by
    exact ne_of_gt B.baseline.totalMass_pos
  simp only [StructuredSampleData.cellOf, Fintype.card_coe]
  field_simp [hcard, hq]

/-- Equality of the actual finite baseline law and the tagged mixture. -/
theorem baselineSigmaProbability_eq_tiltedLaw_zero [Nonempty Head] :
    B.baselineSigmaProbability = B.tiltedLaw 0 := by
  apply finiteProbability_ext
  funext m
  exact B.baselineSigmaProbability_mass_eq m

/-- The actual scalar score divided by the paper scale `L`. -/
def scaledBridgeScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : ℝ :=
  B.vectorFamily.scalarFamily.score m xi / B.L

/-- The medium-prime part of the scaled score. -/
def scaledMediumScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    (B.effectivePrimeCoefficient xi p / B.L) *
      valuation p.1 (B.sampleData.value m)

/-- The residual physical/head part of the scaled score. -/
def scaledNuisanceScore [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) : ℝ :=
  inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) / B.L

theorem scaledBridgeScore_eq_medium_add_nuisance [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.scaledBridgeScore xi m =
      B.scaledMediumScore xi m + B.scaledNuisanceScore xi m := by
  rw [scaledBridgeScore, scaledMediumScore, scaledNuisanceScore,
    B.vectorScore_eq_effectivePrime_add_nuisance xi m]
  rw [add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The normalized finite-exponential-family law is exactly the exponential
tilt of its normalized baseline probability. -/
theorem tiltedLaw_eq_exponentialTilt_baseline [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      (B.baselineSigmaProbability).exponentialTilt
        (B.scaledBridgeScore xi) := by
  apply finiteProbability_ext
  funext m
  have hbase := B.baselineSigmaProbability_mass_eq m
  change B.vectorFamily.probabilityMass xi m =
    B.baselineSigmaProbability.mass m *
        Real.exp (B.scaledBridgeScore xi m) /
      B.baselineSigmaProbability.expPartition
        (B.scaledBridgeScore xi)
  rw [hbase]
  simp only [tiltedLaw, FiniteExponentialFamily.tiltedProbability]
  change B.vectorFamily.probabilityMass xi m =
    B.vectorFamily.probabilityMass 0 m *
        Real.exp (B.scaledBridgeScore xi m) /
      B.baselineSigmaProbability.expPartition
        (B.scaledBridgeScore xi)
  rw [B.probabilityMass_zero m]
  unfold VectorExponentialFamily.probabilityMass
    FiniteExponentialFamily.probabilityMass
    FiniteExponentialFamily.unnormalizedWeight scaledBridgeScore
  have hpart :
      B.baselineSigmaProbability.expPartition
          (B.scaledBridgeScore xi) =
        B.vectorFamily.scalarFamily.partition xi /
          B.vectorFamily.scalarFamily.baseMass := by
    unfold FiniteProbability.expPartition FiniteProbability.expect
    rw [B.baselineSigmaProbability_eq_tiltedLaw_zero]
    simp only [tiltedLaw,
      FiniteExponentialFamily.tiltedProbability,
      FiniteExponentialFamily.probabilityMass]
    have hpartZero : B.vectorFamily.scalarFamily.partition 0 =
        B.vectorFamily.scalarFamily.baseMass := by
      unfold FiniteExponentialFamily.partition
        FiniteExponentialFamily.unnormalizedWeight
        FiniteExponentialFamily.baseMass
      simp
    rw [hpartZero]
    calc
      (∑ x,
          B.vectorFamily.scalarFamily.unnormalizedWeight 0 x /
              B.vectorFamily.scalarFamily.baseMass *
            Real.exp (B.scaledBridgeScore xi x)) =
          (∑ x,
            B.vectorFamily.scalarFamily.unnormalizedWeight xi x) /
              B.vectorFamily.scalarFamily.baseMass := by
        calc
          _ = ∑ x,
              (B.vectorFamily.scalarFamily.unnormalizedWeight 0 x *
                Real.exp (B.scaledBridgeScore xi x)) /
                  B.vectorFamily.scalarFamily.baseMass := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = (∑ x,
              B.vectorFamily.scalarFamily.unnormalizedWeight 0 x *
                Real.exp (B.scaledBridgeScore xi x)) /
                  B.vectorFamily.scalarFamily.baseMass := by
            rw [Finset.sum_div]
          _ = _ := by
            apply congrArg (fun z : ℝ ↦ z /
              B.vectorFamily.scalarFamily.baseMass)
            apply Finset.sum_congr rfl
            intro k hk
            unfold FiniteExponentialFamily.unnormalizedWeight
              scaledBridgeScore
            simp only [map_zero, zero_div, Real.exp_zero, mul_one]
            rfl
      _ = B.vectorFamily.scalarFamily.partition xi /
          B.vectorFamily.scalarFamily.baseMass := by
        rfl
  have hpart' :
      B.baselineSigmaProbability.expPartition
          (fun k => B.vectorFamily.scalarFamily.score k xi / B.L) =
        B.vectorFamily.scalarFamily.partition xi /
          B.vectorFamily.scalarFamily.baseMass := by
    simpa only [scaledBridgeScore] using hpart
  rw [hpart']
  have hbaseMass :
      B.vectorFamily.scalarFamily.baseMass = B.q := by
    simpa only [VectorExponentialFamily.scalarFamily] using
      B.vectorFamily_baseMass
  rw [hbaseMass]
  field_simp [ne_of_gt B.q_pos,
    B.vectorFamily.scalarFamily.partition_ne_zero xi]
  change B.baseline.baseWeight m *
      Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L) =
    B.baseline.baseWeight m *
      Real.exp (B.vectorFamily.scalarFamily.score m xi / B.L)
  rfl

/-- The actual bridge law, with the global cell partition functions handled
correctly, is a tagged mixture of the componentwise tilted guard-deleted
cell laws. -/
theorem tiltedLaw_eq_tiltedSigmaMixture [Nonempty Head]
    (xi : B.ParamSpace) :
    B.tiltedLaw xi =
      sigmaMixture
        (tiltedSigmaWeight B.baselineCellProbability
          B.guardedCellProbability (B.scaledBridgeScore xi))
        (fun c ↦ (B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline]
  exact exponentialTilt_sigmaMixture _ _ _

/-- On each tagged cell the global score splits exactly into its medium
valuation part and the remaining physical/head part. -/
theorem sigmaCellScore_scaledBridge_eq [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    (m : B.sampleData.SampleAt c) :
    sigmaCellScore (B.scaledBridgeScore xi) c m =
      sigmaCellScore (B.scaledMediumScore xi) c m +
        sigmaCellScore (B.scaledNuisanceScore xi) c m := by
  exact B.scaledBridgeScore_eq_medium_add_nuisance xi ⟨c, m⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
