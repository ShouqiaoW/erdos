import Erdos390.Full.PaperBridgeNuisanceTiltFallback
import Erdos390.Full.PaperEffectiveScoreBound
import Erdos390.Full.OmittedScoreTilt
import Erdos390.Full.PrimeSums

/-!
# Uniform baseline-to-actual `L¹` control for the paper bridge

The nuisance covariance argument in Lemma 8.4 needs the *actual* tilted
finite law to remain close to the actual finite baseline law throughout a
fixed effective parameter box.  The medium-prime score is not uniformly
small pointwise, so this cannot be proved by a sup-norm estimate alone.

This file proves the needed finite statement from literal arithmetic-cell
data.  A positive cell-density bound gives an `O(sum_{W<p<=y} 1/p / L)`
first absolute moment for the medium valuation score.  The fixed-dimensional
nuisance score contributes `O(1/L)`.  A fixed pointwise score envelope then
converts that first-moment estimate to normalized `L¹` distance.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open ValuationScoreDomination DivisibilityMomentBounds
open Erdos390.Full.OmittedScoreCell
open Erdos390.Full.PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- First absolute moment of the literal medium-prime score on one actual
guard-deleted cell.  The right side contains the actual moving-band harmonic
mass; no dimension or least-band-mass factor is introduced. -/
theorem guardedCell_expect_abs_scaledMediumScore_le [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {A rho : ℝ}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) :
    (B.guardedCellProbability c).expect
        (fun m ↦ |sigmaCellScore (B.scaledMediumScore xi) c m|) ≤
      (2 * A / (rho * B.L)) *
        bandReciprocalSum B.sampleData.n B.sampleData.W := by
  let S := B.sampleData.cellFinset c
  let P := primeBand B.sampleData.n B.sampleData.W
  let M := B.sampleData.hi c.2
  let R := primePowerModuli P M
  have hS : S.Nonempty := B.sampleData.cell_nonempty c
  have hM : 0 < M := by
    simpa only [M] using B.cell_hi_pos c
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (by simpa only [P] using hp)
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  have hSle : ∀ m ∈ S, m ≤ M := by
    intro m hm
    let sample : B.sampleData.Sample := ⟨c, ⟨m, hm⟩⟩
    simpa only [sample, M, StructuredSampleData.value,
      StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa only [R] using ha)
  have havgR : uniformAverage S (divisorScore R) ≤
      (1 / rho) * ∑ a ∈ R, 1 / (a : ℝ) := by
    have hraw := uniformAverage_marked_divisorScore_le S R
      (M := M) (D := 1) (c := rho) (by norm_num) hM hrho
      (by simpa only [S, M] using hcard) hSpos hSle hRpos
      (fun a ha ↦ by simp)
    simpa [divInd] using hraw
  have hsumR : (∑ a ∈ R, 1 / (a : ℝ)) ≤
      2 * bandReciprocalSum B.sampleData.n B.sampleData.W := by
    simpa only [R, P] using sum_inv_primePowerModuli_le P M hprime
  have havgR' : uniformAverage S (divisorScore R) ≤
      (2 / rho) * bandReciprocalSum B.sampleData.n B.sampleData.W := by
    calc
      uniformAverage S (divisorScore R) ≤
          (1 / rho) * ∑ a ∈ R, 1 / (a : ℝ) := havgR
      _ ≤ (1 / rho) *
          (2 * bandReciprocalSum B.sampleData.n B.sampleData.W) :=
        mul_le_mul_of_nonneg_left hsumR (by positivity)
      _ = (2 / rho) *
          bandReciprocalSum B.sampleData.n B.sampleData.W := by ring
  have hetaNat : ∀ p ∈ P, |B.effectiveNatCoefficient xi p| ≤ A := by
    intro p hp
    rw [B.effectiveNatCoefficient_of_mem xi (by simpa only [P] using hp)]
    exact heta ⟨p, by simpa only [P] using hp⟩
  have hdom : ∀ m ∈ S,
      |valuationScore P (B.effectiveNatCoefficient xi) B.L m| ≤
        (A / B.L) * divisorScore R m := by
    intro m hm
    simpa only [R, P, M] using
      abs_valuationScore_le_divisorScore P
        (B.effectiveNatCoefficient xi) hprime (hSpos m hm) (hSle m hm)
        B.L_pos hetaNat
  have hexpect :
      (uniformOnFinset S hS).expect
          (fun m : S ↦
            |valuationScore P (B.effectiveNatCoefficient xi) B.L m|) ≤
        (A / B.L) * uniformAverage S (divisorScore R) := by
    calc
      (uniformOnFinset S hS).expect
          (fun m : S ↦
            |valuationScore P (B.effectiveNatCoefficient xi) B.L m|) ≤
          (uniformOnFinset S hS).expect
            (fun m : S ↦ (A / B.L) * divisorScore R m) :=
        (uniformOnFinset S hS).expect_mono _ _
          (fun m ↦ hdom m m.property)
      _ = (A / B.L) * uniformAverage S (divisorScore R) := by
        rw [FiniteProbability.expect_smul]
        congr 1
        exact uniform_expect_eq_uniformAverage S hS (divisorScore R)
  have hexpect' :
      (uniformOnFinset S hS).expect
          (fun m : S ↦
            |valuationScore P (B.effectiveNatCoefficient xi) B.L m|) ≤
        (A / B.L) * ((2 / rho) *
          bandReciprocalSum B.sampleData.n B.sampleData.W) :=
    hexpect.trans (mul_le_mul_of_nonneg_left havgR'
      (div_nonneg hA B.L_pos.le))
  change (uniformOnFinset S hS).expect
      (fun m : S ↦ |sigmaCellScore (B.scaledMediumScore xi) c m|) ≤ _
  rw [show (fun m : S ↦
      |sigmaCellScore (B.scaledMediumScore xi) c m|) =
      (fun m : S ↦
        |valuationScore P (B.effectiveNatCoefficient xi) B.L m|) by
    funext m
    rw [B.sigmaCellScore_scaledMedium_eq_valuationScore xi c m]]
  calc
    _ ≤ (A / B.L) * ((2 / rho) *
        bandReciprocalSum B.sampleData.n B.sampleData.W) := hexpect'
    _ = (2 * A / (rho * B.L)) *
        bandReciprocalSum B.sampleData.n B.sampleData.W := by ring

/-- The one-cell estimate survives the literal baseline tagged mixture with
no dependence on the number or relative masses of the cells. -/
theorem baseline_expect_abs_scaledMediumScore_le [Nonempty Head]
    (xi : B.ParamSpace) {A rho : ℝ}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) :
    B.baselineSigmaProbability.expect
        (fun m ↦ |B.scaledMediumScore xi m|) ≤
      (2 * A / (rho * B.L)) *
        bandReciprocalSum B.sampleData.n B.sampleData.W := by
  exact sigmaMixture_expect_le_common
    B.baselineCellProbability B.guardedCellProbability
    (fun m ↦ |B.scaledMediumScore xi m|)
    ((2 * A / (rho * B.L)) *
      bandReciprocalSum B.sampleData.n B.sampleData.W)
    (fun c ↦ B.guardedCell_expect_abs_scaledMediumScore_le
      xi c hA hrho (hcard c) heta)

/-- Fixed-dimensional nuisance first moment.  Unlike the medium score this
bound is pointwise; the important feature is the explicit division by `L`. -/
theorem baseline_expect_abs_scaledNuisanceScore_le [Nonempty Head]
    (xi : B.ParamSpace) {A R : ℝ}
    (hA : 0 ≤ A)
    (hxi : ‖B.nuisanceParameter xi‖ ≤ A)
    (hstat : ∀ m : B.sampleData.Sample,
      ‖B.nuisanceStatistic m‖ ≤ R) :
    B.baselineSigmaProbability.expect
        (fun m ↦ |B.scaledNuisanceScore xi m|) ≤ A * R / B.L := by
  calc
    B.baselineSigmaProbability.expect
        (fun m ↦ |B.scaledNuisanceScore xi m|) ≤
        B.baselineSigmaProbability.expect (fun _ ↦ A * R / B.L) := by
      apply B.baselineSigmaProbability.expect_mono
      intro m
      rw [scaledNuisanceScore, abs_div, abs_of_pos B.L_pos]
      apply (div_le_div_iff_of_pos_right B.L_pos).2
      calc
        |inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m)| ≤
            ‖B.nuisanceParameter xi‖ * ‖B.nuisanceStatistic m‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ A * R := mul_le_mul hxi (hstat m) (norm_nonneg _) hA
    _ = A * R / B.L := by
      unfold FiniteProbability.expect
      rw [← Finset.sum_mul, B.baselineSigmaProbability.mass_sum,
        one_mul]

/-- Exact first-moment estimate for the full bridge score under the actual
finite baseline mixture. -/
theorem baseline_expect_abs_scaledBridgeScore_le [Nonempty Head]
    (xi : B.ParamSpace) {A rho R : ℝ}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A)
    (hxi : ‖B.nuisanceParameter xi‖ ≤ A)
    (hstat : ∀ m : B.sampleData.Sample,
      ‖B.nuisanceStatistic m‖ ≤ R) :
    B.baselineSigmaProbability.expect
        (fun m ↦ |B.scaledBridgeScore xi m|) ≤
      (2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * R / B.L := by
  have hpoint : ∀ m : B.sampleData.Sample,
      |B.scaledBridgeScore xi m| ≤
        |B.scaledMediumScore xi m| + |B.scaledNuisanceScore xi m| := by
    intro m
    rw [B.scaledBridgeScore_eq_medium_add_nuisance]
    exact abs_add_le _ _
  calc
    B.baselineSigmaProbability.expect
        (fun m ↦ |B.scaledBridgeScore xi m|) ≤
        B.baselineSigmaProbability.expect
          (fun m ↦ |B.scaledMediumScore xi m| +
            |B.scaledNuisanceScore xi m|) :=
      B.baselineSigmaProbability.expect_mono _ _ hpoint
    _ = B.baselineSigmaProbability.expect
          (fun m ↦ |B.scaledMediumScore xi m|) +
        B.baselineSigmaProbability.expect
          (fun m ↦ |B.scaledNuisanceScore xi m|) := by
      rw [B.baselineSigmaProbability.expect_add]
    _ ≤ (2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * R / B.L := add_le_add
      (B.baseline_expect_abs_scaledMediumScore_le xi hA hrho hcard heta)
      (B.baseline_expect_abs_scaledNuisanceScore_le xi hA hxi hstat)

/-- Finite-`n`, box-uniform `L¹` comparison of the actual bridge law with
its actual baseline law.  The premise is precisely the displayed arithmetic
first-moment majorant being small after the fixed score envelope is applied. -/
theorem l1Distance_tiltedLaw_baseline_le [Nonempty Head]
    (xi : B.ParamSpace) {A rho R K : ℝ}
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A)
    (hxi : ‖B.nuisanceParameter xi‖ ≤ A)
    (hstat : ∀ m : B.sampleData.Sample,
      ‖B.nuisanceStatistic m‖ ≤ R)
    (hscore : ∀ m : B.sampleData.Sample,
      |B.scaledBridgeScore xi m| ≤ K)
    (hsmall : Real.exp K *
      ((2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * R / B.L) < 1) :
    B.baselineSigmaProbability.l1Distance (B.tiltedLaw xi) ≤
      (2 * (Real.exp K *
        ((2 * A / (rho * B.L)) *
            bandReciprocalSum B.sampleData.n B.sampleData.W +
          A * R / B.L))) /
      (1 - Real.exp K *
        ((2 * A / (rho * B.L)) *
            bandReciprocalSum B.sampleData.n B.sampleData.W +
          A * R / B.L)) := by
  rw [B.tiltedLaw_eq_exponentialTilt_baseline xi]
  let E := B.baselineSigmaProbability.expect
    (fun m ↦ |B.scaledBridgeScore xi m|)
  let M := (2 * A / (rho * B.L)) *
      bandReciprocalSum B.sampleData.n B.sampleData.W + A * R / B.L
  have hEM : E ≤ M := by
    simpa only [E, M] using
      B.baseline_expect_abs_scaledBridgeScore_le xi hA hrho hcard
        heta hxi hstat
  have hE0 : 0 ≤ E := B.baselineSigmaProbability.expect_nonneg _
    (fun m ↦ abs_nonneg _)
  have hM0 : 0 ≤ M := hE0.trans hEM
  have htotal : Real.exp K * E < 1 :=
    (mul_le_mul_of_nonneg_left hEM (Real.exp_pos K).le).trans_lt
      (by simpa only [M] using hsmall)
  have hraw := B.baselineSigmaProbability
    |>.l1Distance_exponentialTilt_le_of_bounded_score
      (B.scaledBridgeScore xi) hscore htotal
  have hdenE : 0 < 1 - Real.exp K * E := sub_pos.mpr htotal
  have hdenM : 0 < 1 - Real.exp K * M := by
    apply sub_pos.mpr
    simpa only [M] using hsmall
  calc
    B.baselineSigmaProbability.l1Distance
        (B.baselineSigmaProbability.exponentialTilt
          (B.scaledBridgeScore xi)) ≤
        2 * (Real.exp K * E) / (1 - Real.exp K * E) := by
      simpa only [E] using hraw
    _ ≤ 2 * (Real.exp K * M) / (1 - Real.exp K * M) := by
      apply (div_le_div_iff₀ hdenE hdenM).2
      have hXM : Real.exp K * E ≤ Real.exp K * M :=
        mul_le_mul_of_nonneg_left hEM (Real.exp_pos K).le
      nlinarith
    _ = _ := by rfl

/-! ## Fixed-interval/effective-box specialization -/

/-- The fixed physical intervals bound every literal cell endpoint by the
single endpoint `physicalBound U n`. -/
theorem hi_le_physicalBound_of_fixedIntervals
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n) :
    ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound U B.sampleData.n := by
  intro sigma
  rw [hhi]
  unfold physicalBound
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right (hupperU sigma) (Nat.cast_nonneg _)

/-- A paper-effective ball directly supplies both coefficient bounds used by
the finite `L¹` theorem. -/
theorem effective_bounds_of_paperEffectiveSize
    (xi : B.ParamSpace) {A : ℝ}
    (hbox : B.paperEffectiveSize xi ≤ A) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi p| ≤ A) ∧
      ‖B.nuisanceParameter xi‖ ≤ A := by
  have hprimeNorm :
      ‖fun p ↦ B.effectivePrimeCoefficient xi p‖ ≤
        B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg (B.nuisanceParameter xi),
      abs_nonneg (xi MomentCoord.slow)]
  have hnuisance : ‖B.nuisanceParameter xi‖ ≤
      B.paperEffectiveSize xi := by
    unfold paperEffectiveSize
    linarith [norm_nonneg
      (fun p ↦ B.effectivePrimeCoefficient xi p),
      abs_nonneg (xi MomentCoord.slow)]
  constructor
  · intro p
    calc
      |B.effectivePrimeCoefficient xi p| ≤
          ‖fun q ↦ B.effectivePrimeCoefficient xi q‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm
            (fun q ↦ B.effectivePrimeCoefficient xi q) p
      _ ≤ B.paperEffectiveSize xi := hprimeNorm
      _ ≤ A := hbox
  · exact hnuisance.trans hbox

/-- The `L¹` distance used by the nuisance pattern-mixture perturbation is
literally the finite-probability `L¹` distance controlled above. -/
theorem nuisanceFineBaseline_weightL1Distance_eq_l1Distance
    [Nonempty Head] (xi : B.ParamSpace) :
    B.nuisanceFineBaseline.weightL1Distance
        (B.vectorFamily.probabilityMass xi) =
      B.baselineSigmaProbability.l1Distance (B.tiltedLaw xi) := by
  unfold PatternMixture.weightL1Distance FiniteProbability.l1Distance
    nuisanceFineBaseline
  apply Finset.sum_congr rfl
  intro m hm
  rw [B.baselineSigmaProbability_mass_eq m]
  exact abs_sub_comm _ _

/-- Fixed-interval, fixed-effective-box form of the actual-law `L¹` bound.
All constants on the right are independent of the moving band mesh.  The
only remaining finite-`n` hypothesis is the concrete guard-deleted cell
density and the displayed explicit smallness inequality. -/
theorem l1Distance_tiltedLaw_baseline_fixedIntervals_le [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals)
    (xi : B.ParamSpace) {U A rho : ℝ}
    (hU : 1 ≤ U) (hW : 1 < B.sampleData.W)
    (hA : 0 ≤ A) (hrho : 0 < rho)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (hbox : B.paperEffectiveSize xi ≤ A)
    (hsmall : Real.exp
        ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U) * A) *
      ((2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * B.fixedIntervalNuisanceRadius U / B.L) < 1) :
    B.baselineSigmaProbability.l1Distance (B.tiltedLaw xi) ≤
      (2 * (Real.exp
        ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U) * A) *
        ((2 * A / (rho * B.L)) *
            bandReciprocalSum B.sampleData.n B.sampleData.W +
          A * B.fixedIntervalNuisanceRadius U / B.L))) /
      (1 - Real.exp
        ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U) * A) *
        ((2 * A / (rho * B.L)) *
            bandReciprocalSum B.sampleData.n B.sampleData.W +
          A * B.fixedIntervalNuisanceRadius U / B.L)) := by
  let K : ℝ :=
    (PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
      B.nuisanceStatisticCoefficient U) * A
  let R : ℝ := B.fixedIntervalNuisanceRadius U
  obtain ⟨heta, hxi⟩ := B.effective_bounds_of_paperEffectiveSize xi hbox
  have hhiU : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound U B.sampleData.n :=
    B.hi_le_physicalBound_of_fixedIntervals I hupperU hhi
  have hstat : ∀ m : B.sampleData.Sample,
      ‖B.nuisanceStatistic m‖ ≤ R := by
    intro m
    simpa only [R] using B.nuisanceStatistic_norm_le_fixedIntervals
      I hlowerOne hupperU hlo hhi m
  have hscore : ∀ m : B.sampleData.Sample,
      |B.scaledBridgeScore xi m| ≤ K := by
    intro m
    simpa only [scaledBridgeScore, K] using
      B.effectiveScoreBound_of_paperEffectiveSize hU hW hhiU xi hbox m
  simpa only [K, R] using B.l1Distance_tiltedLaw_baseline_le xi hA hrho
    hcard heta hxi hstat hscore (by simpa only [K, R] using hsmall)

/-- Direct attachment of the actual bridge `L¹` estimate to the explicit
finite-`n` nuisance covariance gap.  In particular this theorem never passes
through an assumed limiting covariance `Gamma_0`. -/
theorem nuisanceCovarianceOperator_fixedIntervals_half_gap_of_bridgeL1
    [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals)
    (xi : B.ParamSpace) {U A rho lambda : ℝ}
    (hU : 1 ≤ U) (hW : 1 < B.sampleData.W)
    (hA : 0 ≤ A) (hrho : 0 < rho) (hlambda : 0 < lambda)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hcard : ∀ c : Cell Head,
      rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ))
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (hbox : B.paperEffectiveSize xi ≤ A)
    (htiltSmall : Real.exp
        ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U) * A) *
      ((2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * B.fixedIntervalNuisanceRadius U / B.L) < 1)
    (hgapSmall :
      ((2 * (Real.exp
        ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U) * A) *
        ((2 * A / (rho * B.L)) *
            bandReciprocalSum B.sampleData.n B.sampleData.W +
          A * B.fixedIntervalNuisanceRadius U / B.L))) /
      (1 - Real.exp
        ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
          B.nuisanceStatisticCoefficient U) * A) *
        ((2 * A / (rho * B.L)) *
            bandReciprocalSum B.sampleData.n B.sampleData.W +
          A * B.fixedIntervalNuisanceRadius U / B.L))) *
        B.fixedIntervalNuisanceDiameter U ^ 2 ≤
      B.uniformNuisanceGap lambda
        (Real.log (I.lower .plus) - Real.log (I.upper .minus))
        (Real.log U) / 2)
    (x : B.NuisanceSpace) :
    (B.uniformNuisanceGap lambda
        (Real.log (I.lower .plus) - Real.log (I.upper .minus))
        (Real.log U) / 2) * ‖x‖ ^ 2 ≤
      inner ℝ x (B.nuisanceCovarianceOperator xi x) := by
  let epsilon : ℝ :=
    (2 * (Real.exp
      ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
        B.nuisanceStatisticCoefficient U) * A) *
      ((2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * B.fixedIntervalNuisanceRadius U / B.L))) /
    (1 - Real.exp
      ((PaperStatisticNorm.valuationLogCoefficient U B.sampleData.W +
        B.nuisanceStatisticCoefficient U) * A) *
      ((2 * A / (rho * B.L)) *
          bandReciprocalSum B.sampleData.n B.sampleData.W +
        A * B.fixedIntervalNuisanceRadius U / B.L))
  have hl1prob : B.baselineSigmaProbability.l1Distance (B.tiltedLaw xi) ≤
      epsilon := by
    simpa only [epsilon] using
      B.l1Distance_tiltedLaw_baseline_fixedIntervals_le I xi hU hW hA
        hrho hlowerOne hupperU hlo hhi hcard hbox htiltSmall
  have hl1 : B.nuisanceFineBaseline.weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon := by
    rw [B.nuisanceFineBaseline_weightL1Distance_eq_l1Distance]
    exact hl1prob
  exact B.nuisanceCovarianceOperator_fixedIntervals_half_gap_of_l1 I
    hlambda hlowerOne hupperU hlo hhi hweight xi hl1
    (by simpa only [epsilon] using hgapSmall) x

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
