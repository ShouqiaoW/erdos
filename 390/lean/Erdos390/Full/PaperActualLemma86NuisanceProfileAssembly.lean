import Erdos390.Full.PaperActualLemma86Assembly
import Erdos390.Full.PaperNuisancePrimeLogRows

/-!
# Exact nuisance-profile assembly for Lemma 8.6

This file joins the finite component-mixture cancellation to the two-stage
regression assembly.  The nuisance marked-row family is not an independent
hypothesis: it is derived from the physical marked row and pairwise agreement
of the guarded, fully tilted component valuation means.  Consequently the
finite-nuisance Schur loss is displayed at its actual `Lscale⁻²` scale.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerCovariance
open PaperPrimePowerRelativeQuadratic
open PaperPrimePowerLemma75

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Variance assembly with the nuisance-row hypothesis reduced to the two
literal analytic component estimates occurring in the paper.  The factor
`6 * Cscale / Lscale` is obtained by exact finite-mixture cancellation, so the
displayed Schur loss is genuinely quadratic in `1 / Lscale`. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree_and_pairwise_cells
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon lower upper Cscale Lscale : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
          upper * w ^ 2)
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ))) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((6 * Cscale / Lscale) * (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 := by
  have hmarked :=
    B.nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
      xi hCscale hLscale hphysical hpair
  have hCmarked : 0 ≤ 6 * Cscale / Lscale := by positivity
  exact
    B.actualCompensatedScore_variance_bounds_of_squarefree_and_marked_nuisance_rows
      xi q hC hK hw hCpow hepsilon hCmarked
      hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75
      hsfLower hsfUpper hmarked

/-- Marked-prime row assembly with the same componentwise hypotheses.  Both
finite-nuisance covariance vectors are derived from one marked family; after
regression their contribution is displayed at the stronger `Lscale⁻²`
scale. -/
theorem actualCompensatedScore_markedRow_bound_of_squarefree_and_pairwise_cells
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon Csf Cscale Lscale : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W)
    (hsquarefree :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
          Csf * w * (1 / (p : ℝ)))
    (hphysical : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |(B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m NuisanceCoord.physical)
          (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
        (Cscale / Lscale) * (1 / (r.1 : ℝ)))
    (hpair : ∀ (r : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation r.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation r.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (r.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      Csf * w * (1 / (p : ℝ)) +
        (1 + C) * w *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              ((6 * Cscale / Lscale) * (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (6 * Cscale / Lscale))) * w * (1 / (p : ℝ)) := by
  have hmarked :=
    B.nuisanceMarkedRows_le_of_pairwise_cell_valuation_and_physical
      xi hCscale hLscale hphysical hpair
  have hCmarked : 0 ≤ 6 * Cscale / Lscale := by positivity
  exact
    B.actualCompensatedScore_markedRow_bound_of_squarefree_and_marked_nuisance_rows
      xi q hC hK hw hCmarked
      hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75
      hp hsquarefree hmarked

/-- The variance assembly with the global physical-row contract removed as
well.  Its remaining nuisance inputs are precisely the two componentwise
estimates proved by the paper's local Stieltjes/omitted-score argument:
within-cell covariance with the physical logarithm, and pairwise agreement
of component valuation means. -/
theorem actualCompensatedScore_variance_bounds_of_squarefree_and_cell_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon lower upper Cscale Lscale Rmax : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hRmax : 0 ≤ Rmax)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hsfLower : lower * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) ≤
          upper * w ^ 2)
    (hphysicalBound : ∀ m : B.sampleData.Sample,
      |B.physicalScore m| ≤ Rmax)
    (hcellPhysical : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).covariance
          (fun x ↦ valuation p.1 (x : ℕ))
          (fun x ↦ B.physicalScore ⟨c, x⟩)| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ)))
    (hpair : ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation p.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation p.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (p.1 : ℝ))) :
    lower * w ^ 2 -
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 -
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          ((6 * ((1 + 2 * Rmax) * Cscale) / Lscale) *
            (7 + C * K))) ^ 2 / gamma) * w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ∧
    (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) ≤
      upper * w ^ 2 +
        (((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)) * w ^ 2 := by
  have hmarked :=
    B.nuisanceMarkedRows_le_of_cell_physical_covariance_and_pairwise_valuation
      xi hCscale hLscale hRmax hphysicalBound hcellPhysical hpair
  have hCmarked :
      0 ≤ 6 * ((1 + 2 * Rmax) * Cscale) / Lscale := by positivity
  exact
    B.actualCompensatedScore_variance_bounds_of_squarefree_and_marked_nuisance_rows
      xi q hC hK hw hCpow hepsilon hCmarked
      hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75
      hsfLower hsfUpper hmarked

/-- Marked-prime counterpart of the preceding theorem.  The complete
finite-nuisance regression correction is therefore derived from component
profiles and is displayed at the stronger `O(w/(p Lscale²))` scale. -/
theorem actualCompensatedScore_markedRow_bound_of_squarefree_and_cell_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon Csf Cscale Lscale Rmax : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCscale : 0 ≤ Cscale) (hLscale : 0 < Lscale)
    (hRmax : 0 ≤ Rmax)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W)
    (hsquarefree :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
          Csf * w * (1 / (p : ℝ)))
    (hphysicalBound : ∀ m : B.sampleData.Sample,
      |B.physicalScore m| ≤ Rmax)
    (hcellPhysical : ∀ (r : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).covariance
          (fun x ↦ valuation r.1 (x : ℕ))
          (fun x ↦ B.physicalScore ⟨c, x⟩)| ≤
        (Cscale / Lscale) * (1 / (r.1 : ℝ)))
    (hpair : ∀ (r : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head),
      |((B.guardedCellProbability c).exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c)).expect
          (fun x ↦ valuation r.1 (x : ℕ)) -
        ((B.guardedCellProbability c').exponentialTilt
          (FiniteProbability.sigmaCellScore
            (B.scaledBridgeScore xi) c')).expect
          (fun x ↦ valuation r.1 (x : ℕ))| ≤
        (Cscale / Lscale) * (1 / (r.1 : ℝ))) :
    |(B.tiltedLaw xi).covariance
      (fun m ↦ valuation p (B.sampleData.value m))
      (B.actualCompensatedScore xi hgamma hgap q)| ≤
      Csf * w * (1 / (p : ℝ)) +
        (1 + C) * w *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              ((6 * ((1 + 2 * Rmax) * Cscale) / Lscale) *
                (7 + C * K))) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (6 * ((1 + 2 * Rmax) * Cscale) / Lscale))) *
              w * (1 / (p : ℝ)) := by
  have hmarked :=
    B.nuisanceMarkedRows_le_of_cell_physical_covariance_and_pairwise_valuation
      xi hCscale hLscale hRmax hphysicalBound hcellPhysical hpair
  have hCmarked :
      0 ≤ 6 * ((1 + 2 * Rmax) * Cscale) / Lscale := by positivity
  exact
    B.actualCompensatedScore_markedRow_bound_of_squarefree_and_marked_nuisance_rows
      xi q hC hK hw hCmarked
      hsharp hbandT hdevSup hdevL1 hdevL2 hgamma hgap h75
      hp hsquarefree hmarked

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
