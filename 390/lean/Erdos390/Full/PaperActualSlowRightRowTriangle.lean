import Erdos390.Full.PaperActualCenterNuisanceRow

/-!
# Exact finite triangle for the slow right column

This file joins four literal rows on the actual finite bridge:

1. the exact prime-log null relation;
2. full valuations versus squarefree valuations;
3. squarefree valuations versus the signed Dickman reference; and
4. the finite nuisance regression constructed from reciprocal marked rows.

The only two comparison hypotheses are pointwise sharp-row estimates, in the
precise form output by the already proved local profile and prime-power
theorems.  The reference row remains literal, so its non-step centered-prime
estimate can be attached without changing gauges.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open PrimePowerSharpBandTransfer SquarefreeSharpBandTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact finite slow-right-row triangle.  All scores and covariance rows in
the conclusion are the literal paper objects. -/
theorem abs_normalizedBandCovarianceRow_nuisanceResidual_slow_le_of_sharpRows
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked Efull Esquare Ereference : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hhead : ∀ h : Head, ∀ p : ℕ,
      p ∈ (B.sampleData.pattern h).primes ↔
        p.Prime ∧ p ≤ B.sampleData.W)
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (i : Band)
    (hfull :
      |fullSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) i -
        squarefreeSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) i| ≤ Efull)
    (hsquare :
      |squarefreeSharpRow (B.actualValuationLaw xi) B.partition
          (fun _ ↦ (1 : ℝ)) i -
        referenceSharpRow B.partition (fun _ ↦ (1 : ℝ)) i| ≤
          Esquare)
    (href :
      |referenceBandRow B.partition B.bandCenter i| ≤
        Ereference * B.bandCenter i) :
    |B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤
      (Efull + Esquare + Ereference) * B.bandCenter i +
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (Cmarked *
              (∑ j : Band, B.harmonicMass j * B.bandCenter j))) /
          gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked) := by
  let fullRaw : ℝ :=
    fullBandRow (B.actualValuationLaw xi) B.partition B.bandCenter i
  let squareRaw : ℝ :=
    squarefreeBandRow (B.actualValuationLaw xi) B.partition B.bandCenter i
  let referenceRaw : ℝ :=
    referenceBandRow B.partition B.bandCenter i
  let correction : ℝ :=
    B.normalizedBandCovarianceRow xi
      (fun m ↦ inner ℝ
        (B.nuisanceCoefficientOfScore xi hgamma hgap B.bandCenterScore)
        (B.nuisanceStatistic m)) i
  let nuisanceRate : ℝ :=
    ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked *
          (∑ j : Band, B.harmonicMass j * B.bandCenter j))) / gamma) *
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        Cmarked)
  have hcenter : 0 < B.bandCenter i := B.bandCenter_pos i
  have hcenter' : 0 < B.partition.center i := by
    simpa only [bandCenter] using hcenter
  have hfullDiv : |fullRaw - squareRaw| / B.bandCenter i ≤ Efull := by
    have h := hfull
    simp only [fullSharpRow, squarefreeSharpRow, mul_one] at h
    rw [← sub_div, abs_div, abs_of_pos hcenter'] at h
    simpa only [fullRaw, squareRaw, bandCenter] using h
  have hfullRaw : |fullRaw - squareRaw| ≤
      Efull * B.bandCenter i := (div_le_iff₀ hcenter).mp hfullDiv
  have hsquareDiv : |squareRaw - referenceRaw| / B.bandCenter i ≤
      Esquare := by
    have h := hsquare
    simp only [squarefreeSharpRow, referenceSharpRow, mul_one] at h
    rw [← sub_div, abs_div, abs_of_pos hcenter'] at h
    simpa only [squareRaw, referenceRaw, bandCenter] using h
  have hsquareRaw : |squareRaw - referenceRaw| ≤
      Esquare * B.bandCenter i :=
    (div_le_iff₀ hcenter).mp hsquareDiv
  have hreferenceRaw : |referenceRaw| ≤
      Ereference * B.bandCenter i := by
    simpa only [referenceRaw] using href
  have hfullAbs : |fullRaw| ≤
      (Efull + Esquare + Ereference) * B.bandCenter i := by
    calc
      |fullRaw| = |(fullRaw - squareRaw) +
          (squareRaw - referenceRaw) + referenceRaw| := by ring_nf
      _ ≤ |fullRaw - squareRaw| + |squareRaw - referenceRaw| +
          |referenceRaw| := by
        exact (abs_add_le _ _).trans
          (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ Efull * B.bandCenter i +
          Esquare * B.bandCenter i +
          Ereference * B.bandCenter i :=
        add_le_add (add_le_add hfullRaw hsquareRaw) hreferenceRaw
      _ = (Efull + Esquare + Ereference) * B.bandCenter i := by ring
  have hcorrection : |correction| ≤ nuisanceRate := by
    simpa only [correction, nuisanceRate] using
      B.abs_normalizedBandCovarianceRow_bandCenter_nuisanceCorrection_le
        xi hgamma hgap hCmarked hmarked i
  have hslowCenter :=
    B.normalizedBandCovarianceRow_nuisanceResidual_slow_eq_bandCenterScore
      xi hgamma hgap hhead
  have hslowCenterI :
      B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i =
        B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.bandCenterScore) i := by
    simpa only [bandCenterScore] using congrFun hslowCenter i
  have hcenterResidual :
      B.normalizedBandCovarianceRow xi
          (B.nuisanceResidualScore xi hgamma hgap B.bandCenterScore) i =
        fullRaw - correction := by
    unfold nuisanceResidualScore
    rw [B.normalizedBandCovarianceRow_sub]
    simp only [Pi.sub_apply]
    rw [← B.fullBandRow_bandCenter_eq_normalizedBandCovarianceRow xi i]
  rw [hslowCenterI]
  rw [hcenterResidual]
  calc
    |fullRaw - correction| ≤ |fullRaw| + |correction| := abs_sub _ _
    _ ≤ (Efull + Esquare + Ereference) * B.bandCenter i +
        nuisanceRate := add_le_add hfullAbs hcorrection
    _ = _ := rfl

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
