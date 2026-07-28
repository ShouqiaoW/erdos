import Erdos390.Full.PaperActualLemma86Assembly
import Erdos390.Full.PaperExactTwoStageTargetSolve

/-!
# Quantitative Lemma 8.6 output for the two-stage slow variance

This connector turns the literal squarefree lower bound, the full-valuation
prime-power transfer, and one reciprocal nuisance marked family into the
slow variance bound consumed by Proposition 8.7.  The final numerical margin
is stated explicitly, so no asymptotic choice or relative-error absorption is
hidden in the algebraic assembly.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimePowerCovariance
open PaperPrimePowerLemma75

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The exact slow-variance conclusion after all three displayed error
budgets are smaller than the preselected numerical margin. -/
theorem actualTwoStageCompensatedVariance_lower_of_squarefree_and_marked
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {C K Cpow epsilon lower upper Cmarked gammaSlow : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hCmarked : 0 ≤ Cmarked)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ C * B.w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * B.w)
    (hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2)
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hsfLower : lower * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore
          (B.actualBandRegression xi hgamma hgap e))
        (B.postBandSquarefreeScore
          (B.actualBandRegression xi hgamma hgap e)))
    (hsfUpper :
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore
          (B.actualBandRegression xi hgamma hgap e))
        (B.postBandSquarefreeScore
          (B.actualBandRegression xi hgamma hgap e)) ≤
        upper * B.w ^ 2)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (p.1 : ℝ)))
    (hmargin : gammaSlow ≤
      lower -
        ((1 + C) * (7 + C * K)) *
          (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) -
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (7 + C * K))) ^ 2 / gamma) :
    gammaSlow * B.w ^ 2 ≤
      B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
  let q := B.actualBandRegression xi hgamma hgap e
  let E := ((1 + C) * (7 + C * K)) *
    (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon)
  let N := (Real.sqrt
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * (7 + C * K))) ^ 2 / gamma
  have hbounds :=
    B.actualCompensatedScore_variance_bounds_of_squarefree_and_marked_nuisance_rows
      xi q hC hK B.w_pos.le hCpow hepsilon hCmarked
      (by simpa only [q] using hsharp) hbandT hdevSup hdevL1 hdevL2
      hgamma hgap h75 (by simpa only [q] using hsfLower)
      (by simpa only [q] using hsfUpper) hmarked
  have hscaled : gammaSlow * B.w ^ 2 ≤
      (lower - E - N) * B.w ^ 2 :=
    mul_le_mul_of_nonneg_right
      (by simpa only [E, N] using hmargin) (sq_nonneg B.w)
  calc
    gammaSlow * B.w ^ 2 ≤ (lower - E - N) * B.w ^ 2 := hscaled
    _ = lower * B.w ^ 2 - E * B.w ^ 2 - N * B.w ^ 2 := by ring
    _ ≤ (B.tiltedLaw xi).covariance
        (B.actualCompensatedScore xi hgamma hgap q)
        (B.actualCompensatedScore xi hgamma hgap q) := by
      simpa only [E, N] using hbounds.1
    _ = B.actualTwoStageCompensatedVariance xi hgamma hgap e := by
      rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
