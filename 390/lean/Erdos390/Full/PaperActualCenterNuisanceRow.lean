import Erdos390.Full.PaperActualSchurMarkedRow
import Erdos390.Full.PaperCanonicalActualFullQuotientNullIdentification

/-!
# The exact nuisance correction for the band-centre score

The slow right column in Lemma 8.6 may be replaced, after the exact
prime-log null relation, by the literal band-centre score

`sum_j alpha_j Omega_j`.

This file carries out the finite nuisance regression for that score from
the reciprocal marked-prime family.  In particular, the source norm and the
output row are conclusions; neither is packaged as an analytic assumption.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The literal arithmetic band-centre score used after eliminating the
prime-log nuisance direction. -/
def bandCenterScore (m : B.sampleData.Sample) : ℝ :=
  ∑ j : Band, B.bandCenter j * B.bandScore j m

/-- Reindex the literal band-centre score onto the actual medium primes. -/
theorem bandCenterScore_eq_primeSum (m : B.sampleData.Sample) :
    B.bandCenterScore m =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandCenter (B.partition.band p) *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
  unfold bandCenterScore bandScore
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p : BandPrime B.sampleData.n B.sampleData.W ↦
      B.bandCenter (B.partition.band p) *
        ArithmeticModel.valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j :=
    (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
      B.partition.data).mp hp
  rw [hpj]

/-- The full-valuation row with coefficient `alpha_{j(p)}` is literally the
normalized covariance row of `bandCenterScore`. -/
theorem fullBandRow_bandCenter_eq_normalizedBandCovarianceRow
    [Nonempty Head]
    (xi : B.ParamSpace) (i : Band) :
    PrimePowerSharpBandTransfer.fullBandRow
        (B.actualValuationLaw xi) B.partition B.bandCenter i =
      B.normalizedBandCovarianceRow xi B.bandCenterScore i := by
  have hscore : B.bandCenterScore =
      fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandCenter (B.partition.band p) *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) := by
    funext m
    exact B.bandCenterScore_eq_primeSum m
  rw [hscore]
  unfold PrimePowerSharpBandTransfer.fullBandRow
    normalizedBandCovarianceRow bandScore
    PrimePowerCovariance.BoundedValuationLaw.covVV
    PrimePowerCovariance.BoundedValuationLaw.V
    actualValuationLaw
  rw [FiniteProbability.covariance_sum_left]
  simp_rw [FiniteProbability.covariance_sum_right,
    FiniteProbability.covariance_smul_right]
  change (1 / B.harmonicMass i) * _ = _ / B.harmonicMass i
  ring

/-- A reciprocal marked-prime family bounds the nuisance covariance vector
of the literal band-centre score.  The exact arithmetic first moment is kept
in the conclusion. -/
theorem nuisanceCovarianceVector_bandCenterScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi B.bandCenterScore‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked *
          (∑ j : Band, B.harmonicMass j * B.bandCenter j)) := by
  let moment : ℝ :=
    ∑ j : Band, B.harmonicMass j * B.bandCenter j
  have hmoment : 0 ≤ moment := by
    dsimp only [moment]
    exact Finset.sum_nonneg fun j _ ↦
      mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hK : 0 ≤ Cmarked * moment := mul_nonneg hCmarked hmoment
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi B.bandCenterScore hK
  intro c
  have hsum :
      (B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c) B.bandCenterScore =
        ∑ j : Band, B.bandCenter j *
          (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c) (B.bandScore j) := by
    unfold bandCenterScore
    rw [show (fun m ↦ ∑ j : Band,
        B.bandCenter j * B.bandScore j m) =
      fun m ↦ ∑ j ∈ (Finset.univ : Finset Band),
        B.bandCenter j * B.bandScore j m by simp]
    rw [FiniteProbability.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro j hj
    rw [FiniteProbability.covariance_smul_right]
  rw [hsum]
  calc
    |∑ j : Band, B.bandCenter j *
        (B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c) (B.bandScore j)| ≤
      ∑ j : Band, |B.bandCenter j *
        (B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c) (B.bandScore j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Band,
        B.bandCenter j * (Cmarked * B.harmonicMass j) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_pos (B.bandCenter_pos j)]
      exact mul_le_mul_of_nonneg_left
        (B.abs_covariance_nuisance_bandScore_le_of_marked
          xi c j (fun p ↦ hmarked c p))
        (B.bandCenter_pos j).le
    _ = Cmarked * moment := by
      dsimp only [moment]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- The exact nuisance coefficient of the band-centre score, bounded only
from coercivity and the preceding reciprocal marked-prime summation. -/
theorem nuisanceCoefficient_bandCenterScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap B.bandCenterScore‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked *
          (∑ j : Band, B.harmonicMass j * B.bandCenter j))) / gamma := by
  calc
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap B.bandCenterScore‖ ≤
        ‖B.nuisanceCovarianceVector xi B.bandCenterScore‖ / gamma :=
      B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
    _ ≤ (Real.sqrt (Fintype.card
          (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked *
          (∑ j : Band, B.harmonicMass j * B.bandCenter j))) / gamma :=
      div_le_div_of_nonneg_right
        (B.nuisanceCovarianceVector_bandCenterScore_norm_le_of_marked
          xi hCmarked hmarked) hgamma.le

/-- Coordinatewise normalized nuisance-Schur correction for the band-centre
score.  There is no hidden least-centre divisor: the output band mass
cancels exactly. -/
theorem abs_normalizedBandCovarianceRow_bandCenter_nuisanceCorrection_le
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (i : Band) :
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.bandCenterScore)
          (B.nuisanceStatistic m)) i| ≤
      ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked *
            (∑ j : Band, B.harmonicMass j * B.bandCenter j))) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := by
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap B.bandCenterScore
  let droot : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let moment : ℝ :=
    ∑ j : Band, B.harmonicMass j * B.bandCenter j
  have hmoment : 0 ≤ moment := by
    dsimp only [moment]
    exact Finset.sum_nonneg fun j _ ↦
      mul_nonneg (B.harmonicMass_pos j).le (B.bandCenter_pos j).le
  have hdroot : 0 ≤ droot := Real.sqrt_nonneg _
  have hupperA : 0 ≤ (droot * (Cmarked * moment)) / gamma :=
    div_nonneg (mul_nonneg hdroot (mul_nonneg hCmarked hmoment)) hgamma.le
  have ha : ‖a‖ ≤ (droot * (Cmarked * moment)) / gamma := by
    simpa only [a, droot, moment] using
      B.nuisanceCoefficient_bandCenterScore_norm_le_of_marked
        xi hgamma hgap hCmarked hmarked
  have hrow :
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        (droot * Cmarked) * B.harmonicMass i := by
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [droot, mul_assoc] using h
  have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
  change |B.normalizedBandCovarianceRow xi
    (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) i| ≤ _
  unfold normalizedBandCovarianceRow
  rw [B.covariance_marked_nuisanceScore_eq_inner,
    abs_div, abs_of_pos hH]
  calc
    |inner ℝ a (B.nuisanceCovarianceVector xi (B.bandScore i))| /
          B.harmonicMass i ≤
        (‖a‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
          B.harmonicMass i :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hH.le
    _ ≤ (((droot * (Cmarked * moment)) / gamma) *
          ((droot * Cmarked) * B.harmonicMass i)) /
          B.harmonicMass i := by
      apply div_le_div_of_nonneg_right _ hH.le
      calc
        ‖a‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
            ((droot * (Cmarked * moment)) / gamma) *
              ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ :=
          mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ ((droot * (Cmarked * moment)) / gamma) *
              ((droot * Cmarked) * B.harmonicMass i) :=
          mul_le_mul_of_nonneg_left hrow hupperA
    _ = ((droot * (Cmarked * moment)) / gamma) *
        (droot * Cmarked) := by
      field_simp [hH.ne']

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
