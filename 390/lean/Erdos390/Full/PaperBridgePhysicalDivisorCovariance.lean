import Erdos390.Full.PaperBridgeNuisanceTiltFallback

/-!
# Arbitrary-divisor covariance through the physical residual tilt

The prime-power correction is a finite sum of covariances of divisibility
indicators.  To retain its extra reciprocal prime-power factor, the physical
second tilt must be compared before those sums are collapsed.  This module
proves the needed literal component estimate for arbitrary positive divisors.
The joint mark is kept at the exact `lcm` scale, so the theorem covers both
distinct-prime and diagonal prime-power terms.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open DivisibilityMomentBounds

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- An arbitrary pair of positive divisor indicators retains its reciprocal
`lcm`/product covariance scale under the residual physical tilt. -/
theorem abs_guardedCell_fullTilt_divIndCovariance_sub_medium_le
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A Aphys Kphys : ℝ} {D E : ℕ}
    (hD : 0 < D) (hE : 0 < E)
    (hA : 0 ≤ A) (hW : 1 < B.sampleData.W)
    (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ m : B.sampleData.SampleAt c,
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1) :
    let epsilon := Aphys * Kphys / B.L
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |((B.guardedCellProbability c).exponentialTilt
          (sigmaCellScore (B.scaledBridgeScore xi) c)).covariance
          (fun m ↦ divInd D m) (fun m ↦ divInd E m) -
        (B.cellMediumLaw xi c).covariance
          (fun m ↦ divInd D m) (fun m ↦ divInd E m)| ≤
      8 * epsilon *
        (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
  dsimp only
  let epsilon := Aphys * Kphys / B.L
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hepsilon0 : 0 ≤ epsilon := by
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hscore : ∀ m, |B.cellPhysicalTiltScore xi c m| ≤ epsilon := by
    simpa only [epsilon] using
      B.abs_cellPhysicalTiltScore_le xi c hAphys hKphys
  have hLcm : 0 < Nat.lcm D E := Nat.lcm_pos hD hE
  have hmediumD := B.cellMediumLaw_expect_divInd_le xi c
    hD hA hW hrho hcard heta
  have hmediumE := B.cellMediumLaw_expect_divInd_le xi c
    hE hA hW hrho hcard heta
  have hmediumLcm := B.cellMediumLaw_expect_divInd_le xi c
    hLcm hA hW hrho hcard heta
  have hDexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd D m) ≤ G * (1 / (D : ℝ)) := by
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (D : ℝ)) := hmediumD
      _ = _ := by ring
  have hEexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd E m) ≤ G * (1 / (E : ℝ)) := by
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (E : ℝ)) := hmediumE
      _ = _ := by ring
  have hproduct : (fun m : B.sampleData.SampleAt c ↦
      divInd D m * divInd E m) =
      fun m : B.sampleData.SampleAt c ↦ divInd (Nat.lcm D E) m := by
    funext m
    exact divInd_mul_eq_lcm D E m
  have hDEexpect : (B.cellMediumLaw xi c).expect
      (fun m ↦ divInd D m * divInd E m) ≤
        G * (1 / (Nat.lcm D E : ℝ)) := by
    rw [hproduct]
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (Nat.lcm D E : ℝ)) := hmediumLcm
      _ = _ := by ring
  rw [B.guardedCell_fullTilt_eq_medium_physicalTilt xi c]
  exact FiniteProbability.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
    (B.cellMediumLaw xi c)
    (fun m ↦ divInd D m) (fun m ↦ divInd E m)
    (B.cellPhysicalTiltScore xi c)
    (fun m ↦ divInd_nonneg D m) (fun m ↦ divInd_le_one D m)
    (fun m ↦ divInd_nonneg E m) (fun m ↦ divInd_le_one E m)
    hepsilon0 hsmall hscore hDexpect hEexpect hDEexpect

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
