import Erdos390.Full.PaperCanonicalLemma86RelativePrimePowerEventually

/-!
# Common paper constants for Lemma 8.6

The arithmetic terminal naturally produces three explicit constants for the
pointwise, first-moment, and second-moment compensated-coefficient bounds.
This file replaces them by one positive constant `Ccmp`, exactly as in the
paper.  The choice depends only on the already fixed regression constant and
therefore precedes `W`, the mesh, the head data, and the effective tilt box.

We also record the exact algebra which turns the geometric lower estimate
`w^2 <= (456 / cMesh^2) V` into the positive-factor form
`(cMesh^2 / 456) w^2 <= V` used by the variance assembly.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport

namespace BridgeData

/-- The fixed reciprocal-prime-mass constant used in the Lemma 8.6
coefficient ledger. -/
def paperLemma86BandTConstant : ℝ := 2 * Real.log 4

/-- One paper coefficient constant dominating the pointwise, weighted
`L¹`, and weighted `L²` constants. -/
def paperLemma86CompensatedConstant (Creg : ℝ) : ℝ :=
  max (1 + Creg)
    (max (slowL1Constant Creg paperLemma86BandTConstant)
      (slowL2Constant Creg paperLemma86BandTConstant))

theorem paperLemma86BandTConstant_nonneg :
    0 ≤ paperLemma86BandTConstant := by
  dsimp only [paperLemma86BandTConstant]
  positivity

theorem paperLemma86CompensatedConstant_pos
    {Creg : ℝ} (hCreg : 0 ≤ Creg) :
    0 < paperLemma86CompensatedConstant Creg := by
  unfold paperLemma86CompensatedConstant
  exact (by linarith : 0 < 1 + Creg).trans_le (le_max_left _ _)

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Exact consolidation of the three coefficient estimates on one literal
regression `q^reg`, hence on one and the same Schur equivalence `e`. -/
theorem actualBandRegression_compensated_bounds_le_paperCcmp
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    {Creg : ℝ}
    (hsup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤
          (1 + Creg) * B.w)
    (hL1 : B.partition.compensatedL1
        (B.actualBandRegression xi hgamma hgap e) ≤
      slowL1Constant Creg paperLemma86BandTConstant * B.w)
    (hL2 : B.partition.compensatedL2Sq
        (B.actualBandRegression xi hgamma hgap e) ≤
      slowL2Constant Creg paperLemma86BandTConstant * B.w ^ 2) :
    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression xi hgamma hgap e) p| ≤
          paperLemma86CompensatedConstant Creg * B.w) ∧
    B.partition.compensatedL1
        (B.actualBandRegression xi hgamma hgap e) ≤
      paperLemma86CompensatedConstant Creg * B.w ∧
    B.partition.compensatedL2Sq
        (B.actualBandRegression xi hgamma hgap e) ≤
      paperLemma86CompensatedConstant Creg * B.w ^ 2 := by
  have hw : 0 ≤ B.w := B.w_pos.le
  have hw2 : 0 ≤ B.w ^ 2 := sq_nonneg B.w
  have hsupConst : 1 + Creg ≤
      paperLemma86CompensatedConstant Creg := by
    exact le_max_left _ _
  have hL1Const : slowL1Constant Creg paperLemma86BandTConstant ≤
      paperLemma86CompensatedConstant Creg := by
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hL2Const : slowL2Constant Creg paperLemma86BandTConstant ≤
      paperLemma86CompensatedConstant Creg := by
    exact (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨?_, hL1.trans (mul_le_mul_of_nonneg_right hL1Const hw),
    hL2.trans (mul_le_mul_of_nonneg_right hL2Const hw2)⟩
  intro p
  exact (hsup p).trans (mul_le_mul_of_nonneg_right hsupConst hw)

/-- Existential paper interface: `Ccmp` is selected before the bridge data
and hence, in particular, before its prime cutoff and tilt box. -/
theorem exists_paperLemma86CompensatedConstant
    (Creg : ℝ) (hCreg : 0 ≤ Creg) :
    ∃ Ccmp : ℝ, 0 < Ccmp ∧
      ∀ {Head Band : Type*} [Fintype Head] [DecidableEq Head]
        [Fintype Band] [DecidableEq Band]
        (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
        (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
        (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
          inner ℝ z (B.nuisanceCovarianceOperator xi z))
        (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
        (∀ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤
              (1 + Creg) * B.w) →
        B.partition.compensatedL1
            (B.actualBandRegression xi hgamma hgap e) ≤
          slowL1Constant Creg paperLemma86BandTConstant * B.w →
        B.partition.compensatedL2Sq
            (B.actualBandRegression xi hgamma hgap e) ≤
          slowL2Constant Creg paperLemma86BandTConstant * B.w ^ 2 →
        (∀ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccmp * B.w) ∧
        B.partition.compensatedL1
            (B.actualBandRegression xi hgamma hgap e) ≤ Ccmp * B.w ∧
        B.partition.compensatedL2Sq
            (B.actualBandRegression xi hgamma hgap e) ≤
          Ccmp * B.w ^ 2 := by
  refine ⟨paperLemma86CompensatedConstant Creg,
    paperLemma86CompensatedConstant_pos hCreg, ?_⟩
  intro Head Band _instHF _instHD _instBF _instBD B _instHN _instBN
    xi gamma hgamma hgap e hsup hL1 hL2
  exact actualBandRegression_compensated_bounds_le_paperCcmp
    B xi hgamma hgap e hsup hL1 hL2

/-- Positive geometric variance factor used by the paper. -/
def paperLemma86VarianceFactor (cMesh : ℝ) : ℝ := cMesh ^ 2 / 456

theorem paperLemma86VarianceFactor_pos
    {cMesh : ℝ} (hcMesh : 0 < cMesh) :
    0 < paperLemma86VarianceFactor cMesh := by
  dsimp only [paperLemma86VarianceFactor]
  positivity

/-- Exact `g/V` consolidation.  No asymptotic or operator input is used. -/
theorem lemma86_geometry_bounds_with_positive_varianceFactor
    {cMesh w gL1 V : ℝ} (hcMesh : 0 < cMesh)
    (hgL1 : gL1 ≤ 7 * w)
    (hVlower : w ^ 2 ≤ (456 / cMesh ^ 2) * V)
    (hVupper : V ≤ 4 * w ^ 2) :
    gL1 ≤ 7 * w ∧
      paperLemma86VarianceFactor cMesh * w ^ 2 ≤ V ∧
      V ≤ 4 * w ^ 2 := by
  refine ⟨hgL1, ?_, hVupper⟩
  have hfactor : 0 ≤ cMesh ^ 2 / 456 := by positivity
  calc
    paperLemma86VarianceFactor cMesh * w ^ 2 ≤
        (cMesh ^ 2 / 456) * ((456 / cMesh ^ 2) * V) := by
      dsimp only [paperLemma86VarianceFactor]
      exact mul_le_mul_of_nonneg_left hVlower hfactor
    _ = V := by
      field_simp [ne_of_gt hcMesh]

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
