import Erdos390.Full.CanonicalEndpointDiagonalEventually
import Erdos390.Full.CanonicalEndpointIntervalMesh
import Erdos390.Full.EndpointArithmeticGaugeIdentification
import Erdos390.Full.CompressedArithmeticOperator
import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# Canonical sharp-row aggregation of the double-kernel quadrature

This file closes the two-index application-layer item in the audit of paper
Lemma 8.4.  The normalized double-prime estimate is applied to the literal
canonical endpoints and then summed in the sharp arithmetic norm.  The low
output and low input are treated separately; in particular no factor
`1 / alpha_0` is hidden in a finite-dimensional constant.
-/

open scoped BigOperators
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator PositiveCellTransfer PrimeBandQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Literal absolute normalized double-kernel error at two canonical cells. -/
def endpointDoubleKernelError (n W : ℕ)
    (i j : Fin (M.cellCount + 1)) : ℝ :=
  |normalizedDoublePrimeKernelCell (y n)
      (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) -
    normalizedDoubleContinuumKernelCell (y n)
      (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))|

/-- The actual sharp weighted row sum.  The centre is the arithmetic centre
of the genuine prime partition, not a continuum surrogate. -/
def endpointDoubleKernelSharpRowError
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (i : Fin (M.cellCount + 1)) : ℝ :=
  let P := canonicalPartition M hdelta hn hW S
  ∑ j, endpointDoubleKernelError M n W i j *
    |P.center j / P.center i|

/-- The explicit right side of the uniform normalized cell theorem. -/
def normalizedDoubleKernelCellBound
    (CKernel DKernel CMass : ℝ) (z : ℝ)
    (A₁ Y₁ A₂ Y₂ : ℕ) : ℝ :=
  (((DKernel / Real.log (A₂ : ℝ) ^ 3) * actualCellMass A₁ Y₁ +
      (DKernel / Real.log (A₁ : ℝ) ^ 3) *
        continuumCellMass z A₂ Y₂) /
      actualCellMass A₁ Y₁) +
    ((CKernel *
        (realLogCoordinate z (Y₁ : ℝ) - realLogCoordinate z (A₁ : ℝ)) *
        (realLogCoordinate z (Y₂ : ℝ) - realLogCoordinate z (A₂ : ℝ))) *
      (5 * CMass / Real.log (A₁ : ℝ) ^ 3) /
      (actualCellMass A₁ Y₁ * |continuumCellMass z A₁ Y₁|))

/-- Algebraic form of the cell bound after naming the output mass, the two
continuum masses and the two coordinate lengths. -/
def abstractNormalizedCellBound
    (CKernel DKernel CMass rOut rIn actualOutMass
      continuumOutMass continuumInMass outLength inLength : ℝ) : ℝ :=
  (DKernel * rIn * actualOutMass +
      DKernel * rOut * continuumInMass) / actualOutMass +
    CKernel * outLength * inLength * (5 * CMass * rOut) /
      (actualOutMass * continuumOutMass)

/-- The exact cancellation behind the four low/positive orientations.
After sharp conjugation, the apparently dangerous output mass disappears;
the only non-vanishing fixed-cutoff terms are proportional to
`(log W)^{-3}`. -/
theorem abstractNormalizedCellBound_mul_ratio_le
    {CKernel DKernel CMass rOut rIn actualOutMass
      continuumOutMass continuumInMass outLength inLength ratio : ℝ}
    (hC : 0 ≤ CKernel) (hD : 0 ≤ DKernel) (hCMass : 0 ≤ CMass)
    (hrOut : 0 ≤ rOut) (hrIn : 0 ≤ rIn)
    (hActual : 0 < actualOutMass)
    (hOutMass : 0 < continuumOutMass)
    (hInMass : 0 < continuumInMass)
    (hOutLength : 0 < outLength) (hInLength : 0 < inLength)
    (hMassLower : continuumOutMass / 2 ≤ actualOutMass)
    (hRatio : 0 ≤ ratio)
    (hRatioUpper : ratio ≤
      3 * ((inLength / continuumInMass) /
        (outLength / continuumOutMass))) :
    abstractNormalizedCellBound CKernel DKernel CMass rOut rIn
        actualOutMass continuumOutMass continuumInMass outLength inLength *
        ratio ≤
      3 * DKernel * rIn *
          ((inLength / continuumInMass) /
            (outLength / continuumOutMass)) +
        6 * DKernel * rOut * (inLength / outLength) +
        30 * CKernel * CMass * rOut *
          (inLength ^ 2 / (continuumOutMass * continuumInMass)) := by
  have hInv : 1 / actualOutMass ≤ 2 / continuumOutMass := by
    rw [div_le_div_iff₀ hActual hOutMass]
    linarith
  have hRaw :
      abstractNormalizedCellBound CKernel DKernel CMass rOut rIn
          actualOutMass continuumOutMass continuumInMass outLength inLength ≤
        DKernel * rIn +
          2 * DKernel * rOut * continuumInMass / continuumOutMass +
          10 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass ^ 2 := by
    unfold abstractNormalizedCellBound
    have hFirst :
        (DKernel * rIn * actualOutMass +
            DKernel * rOut * continuumInMass) / actualOutMass =
          DKernel * rIn +
            (DKernel * rOut * continuumInMass) *
              (1 / actualOutMass) := by
      field_simp [ne_of_gt hActual]
    rw [hFirst]
    have hSecond :
        (DKernel * rOut * continuumInMass) * (1 / actualOutMass) ≤
          2 * DKernel * rOut * continuumInMass / continuumOutMass := by
      calc
        (DKernel * rOut * continuumInMass) * (1 / actualOutMass) ≤
            (DKernel * rOut * continuumInMass) *
              (2 / continuumOutMass) := by
          gcongr
        _ = 2 * DKernel * rOut * continuumInMass /
              continuumOutMass := by ring
    have hThird :
        CKernel * outLength * inLength * (5 * CMass * rOut) /
            (actualOutMass * continuumOutMass) ≤
          10 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass ^ 2 := by
      have hRewrite :
          CKernel * outLength * inLength * (5 * CMass * rOut) /
              (actualOutMass * continuumOutMass) =
            (5 * CKernel * CMass * rOut * outLength * inLength /
              continuumOutMass) * (1 / actualOutMass) := by
        field_simp [ne_of_gt hActual, ne_of_gt hOutMass]
      rw [hRewrite]
      calc
        (5 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass) * (1 / actualOutMass) ≤
          (5 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass) * (2 / continuumOutMass) := by
              gcongr
        _ = 10 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass ^ 2 := by ring
    linarith
  have hRawNonneg : 0 ≤
      abstractNormalizedCellBound CKernel DKernel CMass rOut rIn
        actualOutMass continuumOutMass continuumInMass outLength inLength := by
    unfold abstractNormalizedCellBound
    positivity
  calc
    abstractNormalizedCellBound CKernel DKernel CMass rOut rIn
        actualOutMass continuumOutMass continuumInMass outLength inLength *
        ratio ≤
      (DKernel * rIn +
          2 * DKernel * rOut * continuumInMass / continuumOutMass +
          10 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass ^ 2) * ratio :=
      mul_le_mul_of_nonneg_right hRaw hRatio
    _ ≤
      (DKernel * rIn +
          2 * DKernel * rOut * continuumInMass / continuumOutMass +
          10 * CKernel * CMass * rOut * outLength * inLength /
            continuumOutMass ^ 2) *
        (3 * ((inLength / continuumInMass) /
          (outLength / continuumOutMass))) := by
      gcongr
    _ =
      3 * DKernel * rIn *
          ((inLength / continuumInMass) /
            (outLength / continuumOutMass)) +
        6 * DKernel * rOut * (inLength / outLength) +
        30 * CKernel * CMass * rOut *
          (inLength ^ 2 / (continuumOutMass * continuumInMass)) := by
      field_simp [ne_of_gt hOutMass, ne_of_gt hInMass,
        ne_of_gt hOutLength, ne_of_gt hInLength]
      ring

/-- The moving low continuum harmonic mass grows much more slowly than the
cube of the ambient logarithm.  This is the rate needed when a positive
input column is divided by the moving low centre. -/
theorem tendsto_low_endpointContinuumMass_div_log_y_cube_zero
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (lowBand M) /
        Real.log (y n) ^ 3) atTop (nhds 0) := by
  have hUpperCoord : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W 1) atTop (nhds delta) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
      tendsto_floor_scalePoint_coordinate hdelta
  have hUpperLog : Tendsto (fun n : ℕ ↦
      Real.log (actualCutoffCoordinate M n W 1)) atTop
      (nhds (Real.log delta)) :=
    (Real.continuousAt_log (ne_of_gt hdelta)).tendsto.comp hUpperCoord
  have hLogY : Tendsto (fun n : ℕ ↦ Real.log (y n)) atTop atTop :=
    tendsto_log_y_atTop
  have hInvLogY : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLogY
  have hUpperPart : Tendsto (fun n : ℕ ↦
      Real.log (actualCutoffCoordinate M n W 1) /
        Real.log (y n) ^ 3) atTop (nhds 0) := by
    have h := hUpperLog.mul (hInvLogY.pow 3)
    simpa only [mul_zero, zero_pow (by norm_num : 3 ≠ 0),
      div_eq_mul_inv, inv_pow] using h
  have hWlog : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hConstPart : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (W : ℝ)) / Real.log (y n) ^ 3)
      atTop (nhds 0) := by
    have h := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ Real.log (Real.log (W : ℝ))) atTop
      (nhds (Real.log (Real.log (W : ℝ))))).mul (hInvLogY.pow 3)
    simpa only [mul_zero, zero_pow (by norm_num : 3 ≠ 0),
      div_eq_mul_inv, inv_pow] using h
  have hLogLogRatio : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (y n)) / Real.log (y n)) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLogY
  have hLogLogPart : Tendsto (fun n : ℕ ↦
      Real.log (Real.log (y n)) / Real.log (y n) ^ 3)
      atTop (nhds 0) := by
    have hInvSq := hInvLogY.pow 2
    have h := hLogLogRatio.mul hInvSq
    have h0 : Tendsto (fun n : ℕ ↦
        (Real.log (Real.log (y n)) / Real.log (y n)) *
          (Real.log (y n))⁻¹ ^ 2) atTop (nhds 0) := by
      simpa only [mul_zero, zero_mul, zero_pow (by norm_num : 2 ≠ 0)] using h
    apply h0.congr'
    have hne : ∀ᶠ n : ℕ in atTop, Real.log (y n) ≠ 0 :=
      hLogY.eventually (eventually_ne_atTop 0)
    filter_upwards [hne] with n hnlog
    field_simp [hnlog]
  have hSum := (hUpperPart.sub hConstPart).add hLogLogPart
  have hSum0 : Tendsto (fun n : ℕ ↦
      Real.log (actualCutoffCoordinate M n W 1) / Real.log (y n) ^ 3 -
        Real.log (Real.log (W : ℝ)) / Real.log (y n) ^ 3 +
        Real.log (Real.log (y n)) / Real.log (y n) ^ 3)
      atTop (nhds 0) := by simpa using hSum
  apply hSum0.congr'
  filter_upwards [eventually_gt_atTop 1,
    eventually_scaleSeparation M hdelta W] with n hn S
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hUpperPos : 0 < actualCutoffCoordinate M n W 1 := by
    unfold actualCutoffCoordinate realLogCoordinate
    apply div_pos
    · apply Real.log_pos
      exact_mod_cast (show 1 < fullCutoff M n W 1 by
        exact (show 1 < W by omega).trans_le (W_le_first_fullCutoff M S))
    · exact hylog
  have hLowerCoord :
      actualCutoffCoordinate M n W 0 =
        Real.log (W : ℝ) / Real.log (y n) := by rfl
  have hLowerPos : 0 < actualCutoffCoordinate M n W 0 := by
    rw [hLowerCoord]
    exact div_pos hWlog hylog
  unfold endpointContinuumMass lowBand
  simp only [Nat.zero_add, fullCutoff_zero]
  rw [show Real.log (fullCutoff M n W 1 : ℝ) =
      actualCutoffCoordinate M n W 1 * Real.log (y n) by
        unfold actualCutoffCoordinate realLogCoordinate
        field_simp [ne_of_gt hylog],
    show Real.log (W : ℝ) =
      actualCutoffCoordinate M n W 0 * Real.log (y n) by
        rw [hLowerCoord]
        field_simp [ne_of_gt hylog],
    Real.log_mul (ne_of_gt hUpperPos) (ne_of_gt hylog),
    Real.log_mul (ne_of_gt hLowerPos) (ne_of_gt hylog)]
  rw [hLowerCoord, Real.log_div (ne_of_gt hWlog) (ne_of_gt hylog)]
  ring

/-- Continuum centre of a literal canonical endpoint cell. -/
def endpointContinuumCenter (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  endpointContinuumMoment M n W j / endpointContinuumMass M n W j

/-- Cubic PNT cutoff factor attached to the lower endpoint of a cell. -/
def endpointInvLogCube (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  1 / Real.log (fullCutoff M n W j.1 : ℝ) ^ 3

@[simp] theorem endpointInvLogCube_low (n W : ℕ) :
    endpointInvLogCube M n W (lowBand M) =
      1 / Real.log (W : ℝ) ^ 3 := by
  rfl

theorem tendsto_positive_endpointInvLogCube_zero
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k))
      atTop (nhds 0) := by
  have hAReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
  have hLog := Real.tendsto_log_atTop.comp hAReal
  have hInv := tendsto_inv_atTop_zero.comp hLog
  have h := hInv.pow 3
  have h0 : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3)
      atTop (nhds 0) := by
    simpa only [Function.comp_apply,
      zero_pow (by norm_num : 3 ≠ 0)] using h
  apply h0.congr'
  filter_upwards with n
  unfold endpointInvLogCube positiveBand
  rw [one_div, inv_pow]

theorem tendsto_low_endpointContinuumCenter_zero
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumCenter M n W (lowBand M))
      atTop (nhds 0) := by
  have hMoment := tendsto_low_endpointContinuumMoment M hdelta W
  have hMass := tendsto_low_endpointContinuumMass_atTop M hdelta W
  simpa only [endpointContinuumCenter] using hMoment.div_atTop hMass

theorem tendsto_positive_endpointContinuumCenter
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumCenter M n W (positiveBand M k)) atTop
      (nhds (M.width k /
        (Real.log (M.upper k) - Real.log (M.lower k)))) := by
  have hMoment := tendsto_positive_endpointContinuumMoment M hdelta W k
  have hMass := tendsto_positive_endpointContinuumMass M hdelta W k
  have hMassPos : 0 < Real.log (M.upper k) - Real.log (M.lower k) :=
    sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
      ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
      (M.lower_lt_upper hdelta k))
  simpa only [endpointContinuumCenter] using
    hMoment.div hMass (ne_of_gt hMassPos)

/-- Coarse sharp entry obtained after the exact mass/centre cancellation.
It is deliberately separated into the three terms corresponding to the
two numerator errors and the mass-normalization error. -/
def endpointDoubleKernelCoarseEntry
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i j : Fin (M.cellCount + 1)) : ℝ :=
  3 * DKernel * endpointInvLogCube M n W j *
      (endpointContinuumCenter M n W j /
        endpointContinuumCenter M n W i) +
    6 * DKernel * endpointInvLogCube M n W i *
      (endpointContinuumMoment M n W j /
        endpointContinuumMoment M n W i) +
    30 * CKernel * CMass * endpointInvLogCube M n W i *
      (endpointContinuumMoment M n W j ^ 2 /
        (endpointContinuumMass M n W i *
          endpointContinuumMass M n W j))

def endpointDoubleKernelCoarseRow
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i : Fin (M.cellCount + 1)) : ℝ :=
  ∑ j, endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W i j

/-- Every positive output row of the coarse bound tends to zero, with the
low input included. -/
theorem tendsto_positive_endpointDoubleKernelCoarseRow_zero
    (hdelta : 0 < delta) (W : ℕ)
    (CKernel DKernel CMass : ℝ) (i : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointDoubleKernelCoarseRow M CKernel DKernel CMass n W
        (positiveBand M i)) atTop (nhds 0) := by
  unfold endpointDoubleKernelCoarseRow
  have hEach : ∀ j : Fin (M.cellCount + 1), Tendsto (fun n : ℕ ↦
      endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W
        (positiveBand M i) j) atTop (nhds 0) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · have hri := tendsto_positive_endpointInvLogCube_zero M hdelta W i
      have hci := tendsto_positive_endpointContinuumCenter M hdelta W i
      have hclow := tendsto_low_endpointContinuumCenter_zero M hdelta W
      have hli := tendsto_positive_endpointContinuumMoment M hdelta W i
      have hllow := tendsto_low_endpointContinuumMoment M hdelta W
      have hHi := tendsto_positive_endpointContinuumMass M hdelta W i
      have hHlow := tendsto_low_endpointContinuumMass_atTop M hdelta W
      have hHiPos : 0 < Real.log (M.upper i) - Real.log (M.lower i) :=
        sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta i)
          ((M.lower_pos hdelta i).trans (M.lower_lt_upper hdelta i))
          (M.lower_lt_upper hdelta i))
      have hciPos : 0 < M.width i /
          (Real.log (M.upper i) - Real.log (M.lower i)) :=
        div_pos (M.width_pos hdelta i) hHiPos
      have hfirst : Tendsto (fun n : ℕ ↦
          3 * DKernel * endpointInvLogCube M n W (lowBand M) *
            (endpointContinuumCenter M n W (lowBand M) /
            endpointContinuumCenter M n W (positiveBand M i)))
          atTop (nhds 0) := by
        have hconst : Tendsto (fun _n : ℕ ↦
            3 * DKernel * (1 / Real.log (W : ℝ) ^ 3)) atTop
            (nhds (3 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
          tendsto_const_nhds
        have hratio := hclow.div hci (ne_of_gt hciPos)
        simpa only [endpointInvLogCube_low, zero_div, mul_zero] using
          hconst.mul hratio
      have hsecond : Tendsto (fun n : ℕ ↦
          6 * DKernel * endpointInvLogCube M n W (positiveBand M i) *
            (endpointContinuumMoment M n W (lowBand M) /
              endpointContinuumMoment M n W (positiveBand M i)))
          atTop (nhds 0) := by
        have hratio := hllow.div hli (ne_of_gt (M.width_pos hdelta i))
        simpa only [mul_zero, zero_mul] using
          ((tendsto_const_nhds.mul tendsto_const_nhds).mul hri).mul hratio
      have hthirdRatio : Tendsto (fun n : ℕ ↦
          endpointContinuumMoment M n W (lowBand M) ^ 2 /
          (endpointContinuumMass M n W (positiveBand M i) *
            endpointContinuumMass M n W (lowBand M))) atTop (nhds 0) := by
        have hlowRatio := (hllow.pow 2).div_atTop hHlow
        have hratio := hlowRatio.div hHi (ne_of_gt hHiPos)
        have hratio0 : Tendsto
            ((fun n : ℕ ↦ endpointContinuumMoment M n W (lowBand M) ^ 2 /
                endpointContinuumMass M n W (lowBand M)) /
              fun n : ℕ ↦ endpointContinuumMass M n W (positiveBand M i))
            atTop (nhds 0) := by simpa using hratio
        apply hratio0.congr'
        have hHiNe := hHi.eventually (eventually_ne_nhds (ne_of_gt hHiPos))
        have hHlowPos := hHlow.eventually (eventually_gt_atTop 0)
        filter_upwards [hHiNe, hHlowPos] with n hne hpos
        change
          (endpointContinuumMoment M n W (lowBand M) ^ 2 /
              endpointContinuumMass M n W (lowBand M)) /
              endpointContinuumMass M n W (positiveBand M i) =
            endpointContinuumMoment M n W (lowBand M) ^ 2 /
              (endpointContinuumMass M n W (positiveBand M i) *
                endpointContinuumMass M n W (lowBand M))
        field_simp [hne, ne_of_gt hpos]
      have hthird : Tendsto (fun n : ℕ ↦
          30 * CKernel * CMass * endpointInvLogCube M n W (positiveBand M i) *
            (endpointContinuumMoment M n W (lowBand M) ^ 2 /
              (endpointContinuumMass M n W (positiveBand M i) *
                endpointContinuumMass M n W (lowBand M))))
          atTop (nhds 0) := by
        simpa only [mul_zero, zero_mul] using
          (((tendsto_const_nhds.mul tendsto_const_nhds).mul
            tendsto_const_nhds).mul hri).mul hthirdRatio
      simpa only [endpointDoubleKernelCoarseEntry, mul_zero, add_zero] using
        (hfirst.add hsecond).add hthird
    · have hri := tendsto_positive_endpointInvLogCube_zero M hdelta W i
      have hrk := tendsto_positive_endpointInvLogCube_zero M hdelta W k
      have hci := tendsto_positive_endpointContinuumCenter M hdelta W i
      have hck := tendsto_positive_endpointContinuumCenter M hdelta W k
      have hli := tendsto_positive_endpointContinuumMoment M hdelta W i
      have hlk := tendsto_positive_endpointContinuumMoment M hdelta W k
      have hHi := tendsto_positive_endpointContinuumMass M hdelta W i
      have hHk := tendsto_positive_endpointContinuumMass M hdelta W k
      have hHiPos : 0 < Real.log (M.upper i) - Real.log (M.lower i) :=
        sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta i)
          ((M.lower_pos hdelta i).trans (M.lower_lt_upper hdelta i))
          (M.lower_lt_upper hdelta i))
      have hHkPos : 0 < Real.log (M.upper k) - Real.log (M.lower k) :=
        sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
          ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
          (M.lower_lt_upper hdelta k))
      have hciPos : 0 < M.width i /
          (Real.log (M.upper i) - Real.log (M.lower i)) :=
        div_pos (M.width_pos hdelta i) hHiPos
      have hfirstRatio := hck.div hci (ne_of_gt hciPos)
      have hsecondRatio := hlk.div hli (ne_of_gt (M.width_pos hdelta i))
      have hthirdRatio := (hlk.pow 2).div (hHi.mul hHk)
        (mul_ne_zero (ne_of_gt hHiPos) (ne_of_gt hHkPos))
      have hfirst : Tendsto (fun n : ℕ ↦
          3 * DKernel * endpointInvLogCube M n W (positiveBand M k) *
            (endpointContinuumCenter M n W (positiveBand M k) /
              endpointContinuumCenter M n W (positiveBand M i)))
          atTop (nhds 0) := by
        simpa only [mul_zero, zero_mul] using
          ((tendsto_const_nhds.mul tendsto_const_nhds).mul hrk).mul hfirstRatio
      have hsecond : Tendsto (fun n : ℕ ↦
          6 * DKernel * endpointInvLogCube M n W (positiveBand M i) *
            (endpointContinuumMoment M n W (positiveBand M k) /
              endpointContinuumMoment M n W (positiveBand M i)))
          atTop (nhds 0) := by
        simpa only [mul_zero, zero_mul] using
          ((tendsto_const_nhds.mul tendsto_const_nhds).mul hri).mul hsecondRatio
      have hthird : Tendsto (fun n : ℕ ↦
          30 * CKernel * CMass * endpointInvLogCube M n W (positiveBand M i) *
            (endpointContinuumMoment M n W (positiveBand M k) ^ 2 /
              (endpointContinuumMass M n W (positiveBand M i) *
                endpointContinuumMass M n W (positiveBand M k))))
          atTop (nhds 0) := by
        simpa only [mul_zero, zero_mul] using
          (((tendsto_const_nhds.mul tendsto_const_nhds).mul
            tendsto_const_nhds).mul hri).mul hthirdRatio
      simpa only [endpointDoubleKernelCoarseEntry, mul_zero, add_zero] using
        (hfirst.add hsecond).add hthird
  have hSum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
  simpa only [Finset.sum_const_zero] using hSum

/-- The positive-cell cubic cutoff beats the reciprocal moving-low centre.
This is the quantitative low-output/positive-input orientation. -/
theorem tendsto_positive_invLogCube_mul_lowMass_zero
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
        endpointContinuumMass M n W (lowBand M))
      atTop (nhds 0) := by
  have hRate :=
    tendsto_low_endpointContinuumMass_div_log_y_cube_zero M hdelta hWTwo
  have hCoord : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 1)) atTop
      (nhds (M.lower k)) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using
        tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)
  have hCoordCube := hCoord.pow 3
  have hLowerCube : M.lower k ^ 3 ≠ 0 :=
    pow_ne_zero 3 (ne_of_gt (M.lower_pos hdelta k))
  have hQuot := hRate.div hCoordCube hLowerCube
  have hQuot0 : Tendsto (fun n : ℕ ↦
      (endpointContinuumMass M n W (lowBand M) /
          Real.log (y n) ^ 3) /
        actualCutoffCoordinate M n W (k.1 + 1) ^ 3)
      atTop (nhds 0) := by simpa using hQuot
  apply hQuot0.congr'
  have hCoordNe := hCoord.eventually
    (eventually_ne_nhds (ne_of_gt (M.lower_pos hdelta k)))
  have hLogNe := tendsto_log_y_atTop.eventually (eventually_ne_atTop 0)
  filter_upwards [hCoordNe, hLogNe] with n hcn hln
  have hLogCutoff :
      Real.log (fullCutoff M n W (k.1 + 1) : ℝ) =
        actualCutoffCoordinate M n W (k.1 + 1) * Real.log (y n) := by
    unfold actualCutoffCoordinate realLogCoordinate
    field_simp [hln]
  unfold endpointInvLogCube positiveBand
  rw [hLogCutoff]
  field_simp [hcn, hln]

/-- The low output row has an explicit fixed-cutoff limit.  All positive
input first-numerator terms vanish by the preceding rate theorem. -/
theorem tendsto_low_endpointDoubleKernelCoarseRow
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (CKernel DKernel CMass : ℝ) :
    Tendsto (fun n : ℕ ↦
      endpointDoubleKernelCoarseRow M CKernel DKernel CMass n W
        (lowBand M)) atTop
      (nhds ((3 * DKernel + 6 * DKernel / delta) /
        Real.log (W : ℝ) ^ 3)) := by
  unfold endpointDoubleKernelCoarseRow
  have hEach : ∀ j : Fin (M.cellCount + 1),
      Tendsto (fun n : ℕ ↦
        endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W
          (lowBand M) j) atTop
        (nhds (Fin.cases
          (9 * DKernel / Real.log (W : ℝ) ^ 3)
          (fun k : Fin M.cellCount ↦
            (6 * DKernel / Real.log (W : ℝ) ^ 3) *
              (M.width k / delta)) j)) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · have hMoment := tendsto_low_endpointContinuumMoment M hdelta W
      have hMass := tendsto_low_endpointContinuumMass_atTop M hdelta W
      have hMomentPos := hMoment.eventually (eventually_gt_nhds hdelta)
      have hMassPos := hMass.eventually (eventually_gt_atTop 0)
      have hCenterPos : ∀ᶠ n : ℕ in atTop,
          0 < endpointContinuumCenter M n W (lowBand M) := by
        filter_upwards [hMomentPos, hMassPos] with n hm hH
        exact div_pos hm hH
      have hFirst : Tendsto (fun n : ℕ ↦
          3 * DKernel * endpointInvLogCube M n W (lowBand M) *
            (endpointContinuumCenter M n W (lowBand M) /
              endpointContinuumCenter M n W (lowBand M))) atTop
          (nhds (3 * DKernel / Real.log (W : ℝ) ^ 3)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hCenterPos] with n hc
        rw [div_self (ne_of_gt hc), mul_one, endpointInvLogCube_low]
        ring
      have hSecond : Tendsto (fun n : ℕ ↦
          6 * DKernel * endpointInvLogCube M n W (lowBand M) *
            (endpointContinuumMoment M n W (lowBand M) /
              endpointContinuumMoment M n W (lowBand M))) atTop
          (nhds (6 * DKernel / Real.log (W : ℝ) ^ 3)) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [hMomentPos] with n hm
        rw [div_self (ne_of_gt hm), mul_one, endpointInvLogCube_low]
        ring
      have hThirdRatio : Tendsto (fun n : ℕ ↦
          endpointContinuumMoment M n W (lowBand M) ^ 2 /
            (endpointContinuumMass M n W (lowBand M) *
              endpointContinuumMass M n W (lowBand M))) atTop (nhds 0) := by
        have hratio := hMoment.div_atTop hMass
        have hsq := hratio.pow 2
        have hsq0 : Tendsto (fun n : ℕ ↦
            (endpointContinuumMoment M n W (lowBand M) /
              endpointContinuumMass M n W (lowBand M)) ^ 2)
            atTop (nhds 0) := by
          simpa only [zero_pow (by norm_num : 2 ≠ 0)] using hsq
        apply hsq0.congr'
        have hMassPos' := hMass.eventually (eventually_gt_atTop 0)
        filter_upwards [hMassPos'] with n hH
        field_simp [ne_of_gt hH]
      have hThird : Tendsto (fun n : ℕ ↦
          30 * CKernel * CMass * endpointInvLogCube M n W (lowBand M) *
            (endpointContinuumMoment M n W (lowBand M) ^ 2 /
              (endpointContinuumMass M n W (lowBand M) *
                endpointContinuumMass M n W (lowBand M)))) atTop
          (nhds 0) := by
        have hconst : Tendsto (fun _n : ℕ ↦
            30 * CKernel * CMass * (1 / Real.log (W : ℝ) ^ 3)) atTop
            (nhds (30 * CKernel * CMass *
              (1 / Real.log (W : ℝ) ^ 3))) := tendsto_const_nhds
        simpa only [endpointInvLogCube_low, mul_zero] using
          hconst.mul hThirdRatio
      have hsum := (hFirst.add hSecond).add hThird
      have hsum' : Tendsto (fun n : ℕ ↦
          endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W
            (lowBand M) (lowBand M)) atTop
          (nhds (3 * DKernel / Real.log (W : ℝ) ^ 3 +
            6 * DKernel / Real.log (W : ℝ) ^ 3)) := by
        simpa only [endpointDoubleKernelCoarseEntry, add_zero] using hsum
      convert hsum' using 1
      simp only [Fin.cases_zero]
      ring
    · have hMomentLow := tendsto_low_endpointContinuumMoment M hdelta W
      have hMassLow := tendsto_low_endpointContinuumMass_atTop M hdelta W
      have hMomentK := tendsto_positive_endpointContinuumMoment M hdelta W k
      have hMassK := tendsto_positive_endpointContinuumMass M hdelta W k
      have hMassKPos : 0 < Real.log (M.upper k) - Real.log (M.lower k) :=
        sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
          ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
          (M.lower_lt_upper hdelta k))
      have hFirstCore :=
        tendsto_positive_invLogCube_mul_lowMass_zero M hdelta hWTwo k
      have hFirstRatio : Tendsto (fun n : ℕ ↦
          endpointInvLogCube M n W (positiveBand M k) *
            (endpointContinuumCenter M n W (positiveBand M k) /
              endpointContinuumCenter M n W (lowBand M))) atTop
          (nhds 0) := by
        have haux : Tendsto (fun n : ℕ ↦
            endpointContinuumMoment M n W (positiveBand M k) /
              (endpointContinuumMass M n W (positiveBand M k) *
                endpointContinuumMoment M n W (lowBand M))) atTop
            (nhds (M.width k /
              ((Real.log (M.upper k) - Real.log (M.lower k)) * delta))) := by
          exact hMomentK.div (hMassK.mul hMomentLow)
            (mul_ne_zero (ne_of_gt hMassKPos) (ne_of_gt hdelta))
        have hmul := hFirstCore.mul haux
        have hPosLow := hMomentLow.eventually (eventually_gt_nhds hdelta)
        have hMassLowPos := hMassLow.eventually (eventually_gt_atTop 0)
        have hMassKNe := hMassK.eventually
          (eventually_ne_nhds (ne_of_gt hMassKPos))
        have hmul0 : Tendsto (fun n : ℕ ↦
            (endpointInvLogCube M n W (positiveBand M k) *
                endpointContinuumMass M n W (lowBand M)) *
              (endpointContinuumMoment M n W (positiveBand M k) /
                (endpointContinuumMass M n W (positiveBand M k) *
                  endpointContinuumMoment M n W (lowBand M))))
            atTop (nhds 0) := by simpa only [zero_mul] using hmul
        apply hmul0.congr'
        filter_upwards [hPosLow, hMassLowPos, hMassKNe] with n hl hHl hHk
        unfold endpointContinuumCenter
        field_simp [ne_of_gt hl, ne_of_gt hHl, hHk]
      have hFirst : Tendsto (fun n : ℕ ↦
          3 * DKernel * endpointInvLogCube M n W (positiveBand M k) *
            (endpointContinuumCenter M n W (positiveBand M k) /
              endpointContinuumCenter M n W (lowBand M))) atTop
          (nhds 0) := by
        have hconst : Tendsto (fun _n : ℕ ↦ 3 * DKernel) atTop
            (nhds (3 * DKernel)) := tendsto_const_nhds
        have hmul := hconst.mul hFirstRatio
        simpa only [mul_zero, mul_assoc] using hmul
      have hSecondRatio := hMomentK.div hMomentLow (ne_of_gt hdelta)
      have hSecond : Tendsto (fun n : ℕ ↦
          6 * DKernel * endpointInvLogCube M n W (lowBand M) *
            (endpointContinuumMoment M n W (positiveBand M k) /
              endpointContinuumMoment M n W (lowBand M))) atTop
          (nhds ((6 * DKernel / Real.log (W : ℝ) ^ 3) *
            (M.width k / delta))) := by
        have hconst : Tendsto (fun _n : ℕ ↦
            6 * DKernel * (1 / Real.log (W : ℝ) ^ 3)) atTop
            (nhds (6 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
          tendsto_const_nhds
        have hmul := hconst.mul hSecondRatio
        simpa only [endpointInvLogCube_low, div_eq_mul_inv, one_mul,
          mul_assoc] using hmul
      have hThirdRatio : Tendsto (fun n : ℕ ↦
          endpointContinuumMoment M n W (positiveBand M k) ^ 2 /
            (endpointContinuumMass M n W (lowBand M) *
              endpointContinuumMass M n W (positiveBand M k))) atTop
          (nhds 0) := by
        have hnum := hMomentK.pow 2
        have hquot := hnum.div hMassK (ne_of_gt hMassKPos)
        have hzero := hquot.div_atTop hMassLow
        have hzero0 : Tendsto (fun n : ℕ ↦
            (endpointContinuumMoment M n W (positiveBand M k) ^ 2 /
                endpointContinuumMass M n W (positiveBand M k)) /
              endpointContinuumMass M n W (lowBand M))
            atTop (nhds 0) := by simpa using hzero
        apply hzero0.congr'
        have hMassKNe := hMassK.eventually
          (eventually_ne_nhds (ne_of_gt hMassKPos))
        have hMassLowPos := hMassLow.eventually (eventually_gt_atTop 0)
        filter_upwards [hMassKNe, hMassLowPos] with n hk hl
        field_simp [hk, ne_of_gt hl]
      have hThird : Tendsto (fun n : ℕ ↦
          30 * CKernel * CMass * endpointInvLogCube M n W (lowBand M) *
            (endpointContinuumMoment M n W (positiveBand M k) ^ 2 /
              (endpointContinuumMass M n W (lowBand M) *
                endpointContinuumMass M n W (positiveBand M k)))) atTop
          (nhds 0) := by
        have hconst : Tendsto (fun _n : ℕ ↦
            30 * CKernel * CMass * (1 / Real.log (W : ℝ) ^ 3)) atTop
            (nhds (30 * CKernel * CMass *
              (1 / Real.log (W : ℝ) ^ 3))) := tendsto_const_nhds
        simpa only [endpointInvLogCube_low, mul_zero] using
          hconst.mul hThirdRatio
      change Tendsto (fun n : ℕ ↦
          endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W
            (lowBand M) (positiveBand M k)) atTop
        (nhds ((6 * DKernel / Real.log (W : ℝ) ^ 3) *
          (M.width k / delta)))
      simpa only [endpointDoubleKernelCoarseEntry, zero_add, add_zero] using
        (hFirst.add hSecond).add hThird
  have hSum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
  have hWidthSum :
      (∑ j : Fin (M.cellCount + 1), Fin.cases
        (9 * DKernel / Real.log (W : ℝ) ^ 3)
        (fun k : Fin M.cellCount ↦
          (6 * DKernel / Real.log (W : ℝ) ^ 3) *
            (M.width k / delta)) j) =
        (3 * DKernel + 6 * DKernel / delta) /
          Real.log (W : ℝ) ^ 3 := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [show (∑ i : Fin M.cellCount,
        (6 * DKernel / Real.log (W : ℝ) ^ 3) * (M.width i / delta)) =
        (6 * DKernel / Real.log (W : ℝ) ^ 3) *
          ((∑ i : Fin M.cellCount, M.width i) / delta) by
      rw [Finset.sum_div, Finset.mul_sum]]
    rw [M.sum_width_eq_one_sub_delta]
    field_simp [ne_of_gt hdelta]
    ring
  simpa only [hWidthSum] using hSum

/-- Relative centre errors of at most one half cost at most the fixed factor
three in every sharp centre ratio. -/
theorem abs_centerRatio_le_three_of_relative
    {aᵢ aⱼ cᵢ cⱼ : ℝ}
    (haᵢ : 0 < aᵢ) (haⱼ : 0 < aⱼ) (hcᵢ : 0 < cᵢ) (hcⱼ : 0 < cⱼ)
    (hrelᵢ : |aᵢ / cᵢ - 1| ≤ 1 / 2)
    (hrelⱼ : |aⱼ / cⱼ - 1| ≤ 1 / 2) :
    |aⱼ / aᵢ| ≤ 3 * ((cⱼ : ℝ) / cᵢ) := by
  let rᵢ := aᵢ / cᵢ
  let rⱼ := aⱼ / cⱼ
  have hrᵢBounds := abs_le.mp hrelᵢ
  have hrⱼBounds := abs_le.mp hrelⱼ
  have hrᵢPos : 0 < rᵢ := by
    dsimp only [rᵢ] at *
    nlinarith
  have hrⱼNonneg : 0 ≤ rⱼ := by
    dsimp only [rⱼ] at *
    nlinarith
  have hrRatio : rⱼ / rᵢ ≤ 3 := by
    apply (div_le_iff₀ hrᵢPos).2
    dsimp only [rᵢ, rⱼ] at *
    nlinarith
  have hid : aⱼ / aᵢ = (rⱼ / rᵢ) * (cⱼ / cᵢ) := by
    dsimp only [rᵢ, rⱼ]
    field_simp [ne_of_gt haᵢ, ne_of_gt haⱼ, ne_of_gt hcᵢ, ne_of_gt hcⱼ]
  rw [hid, abs_mul, abs_of_nonneg (div_nonneg hrⱼNonneg hrᵢPos.le),
    abs_of_pos (div_pos hcⱼ hcᵢ)]
  exact mul_le_mul_of_nonneg_right hrRatio (div_pos hcⱼ hcᵢ).le

/-- Endpoint notation is literally the abstract cell-bound notation. -/
theorem normalizedDoubleKernelCellBound_eq_endpointAbstract
    {n W : ℕ} (hn : 1 < n)
    (hmono : Monotone (fullCutoff M n W))
    (hLowerTwo : ∀ j : Fin (M.cellCount + 1),
      2 ≤ fullCutoff M n W j.1)
    (hMassPos : ∀ j : Fin (M.cellCount + 1),
      0 < endpointContinuumMass M n W j)
    (CKernel DKernel CMass : ℝ)
    (i j : Fin (M.cellCount + 1)) :
    normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
        (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
        (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) =
      abstractNormalizedCellBound CKernel DKernel CMass
        (endpointInvLogCube M n W i) (endpointInvLogCube M n W j)
        (endpointActualMass M n W i)
        (endpointContinuumMass M n W i)
        (endpointContinuumMass M n W j)
        (endpointContinuumMoment M n W i)
        (endpointContinuumMoment M n W j) := by
  have hMassI := endpointContinuumMass_eq_doubleKernelMass M hn i
    (hLowerTwo i) (hmono (Nat.le_succ i.1))
  have hMassJ := endpointContinuumMass_eq_doubleKernelMass M hn j
    (hLowerTwo j) (hmono (Nat.le_succ j.1))
  have hLengthI := endpointContinuumMoment_eq_coordinateLength
    M (W := W) hn i
  have hLengthJ := endpointContinuumMoment_eq_coordinateLength
    M (W := W) hn j
  unfold normalizedDoubleKernelCellBound abstractNormalizedCellBound
    endpointInvLogCube endpointActualMass
  rw [← hMassI, ← hMassJ, abs_of_pos (hMassPos i)]
  rw [hLengthI, hLengthJ]
  unfold actualCutoffCoordinate
  ring

/-- A literal normalized cell estimate implies the sharp coarse entry after
the arithmetic/continuum centre comparison. -/
theorem endpointDoubleKernelError_mul_centerRatio_le_coarse
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
    (CKernel DKernel CMass : ℝ)
    (hC : 0 ≤ CKernel) (hD : 0 ≤ DKernel) (hCMass : 0 ≤ CMass)
    (hMassPos : ∀ r : Fin (M.cellCount + 1),
      0 < endpointContinuumMass M n W r)
    (hMomentPos : ∀ r : Fin (M.cellCount + 1),
      0 < endpointContinuumMoment M n W r)
    (hMassLower : ∀ r : Fin (M.cellCount + 1),
      endpointContinuumMass M n W r / 2 ≤ endpointActualMass M n W r)
    (hCenterRel : ∀ r : Fin (M.cellCount + 1),
      let P := canonicalPartition M hdelta hn hW S
      |P.center r / endpointContinuumCenter M n W r - 1| ≤ 1 / 2)
    (i j : Fin (M.cellCount + 1))
    (hError : endpointDoubleKernelError M n W i j ≤
      normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
        (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
        (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))) :
    let P := canonicalPartition M hdelta hn hW S
    endpointDoubleKernelError M n W i j * |P.center j / P.center i| ≤
      endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W i j := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hLowerTwo (r : Fin (M.cellCount + 1)) :
      2 ≤ fullCutoff M n W r.1 := by
    exact hWTwo.trans (hmono (Nat.zero_le r.1))
  have hActualEq (r : Fin (M.cellCount + 1)) :
      endpointActualMass M n W r = P.mass r := by
    rw [E.mass_eq_fullReciprocalSum_sub]
    rfl
  have hActualPos (r : Fin (M.cellCount + 1)) :
      0 < endpointActualMass M n W r := by
    rw [hActualEq]
    exact P.data.mass_pos r
  have hCenterPos (r : Fin (M.cellCount + 1)) : 0 < P.center r :=
    P.center_pos hn r
  have hContinuumCenterPos (r : Fin (M.cellCount + 1)) :
      0 < endpointContinuumCenter M n W r :=
    div_pos (hMomentPos r) (hMassPos r)
  have hRatio := abs_centerRatio_le_three_of_relative
    (hCenterPos i) (hCenterPos j)
    (hContinuumCenterPos i) (hContinuumCenterPos j)
    (hCenterRel i) (hCenterRel j)
  have hAbstract := abstractNormalizedCellBound_mul_ratio_le
    (CKernel := CKernel) (DKernel := DKernel) (CMass := CMass)
    (rOut := endpointInvLogCube M n W i)
    (rIn := endpointInvLogCube M n W j)
    (actualOutMass := endpointActualMass M n W i)
    (continuumOutMass := endpointContinuumMass M n W i)
    (continuumInMass := endpointContinuumMass M n W j)
    (outLength := endpointContinuumMoment M n W i)
    (inLength := endpointContinuumMoment M n W j)
    (ratio := |P.center j / P.center i|)
    hC hD hCMass
    (by unfold endpointInvLogCube; positivity)
    (by unfold endpointInvLogCube; positivity)
    (hActualPos i) (hMassPos i) (hMassPos j)
    (hMomentPos i) (hMomentPos j) (hMassLower i)
    (abs_nonneg (P.center j / P.center i)) hRatio
  have hIdentification := normalizedDoubleKernelCellBound_eq_endpointAbstract
    M hn hmono hLowerTwo hMassPos CKernel DKernel CMass i j
  dsimp only [P]
  calc
    endpointDoubleKernelError M n W i j *
        |(canonicalPartition M hdelta hn hW S).center j /
          (canonicalPartition M hdelta hn hW S).center i| ≤
      normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
          (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
          (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) *
        |(canonicalPartition M hdelta hn hW S).center j /
          (canonicalPartition M hdelta hn hW S).center i| :=
      mul_le_mul_of_nonneg_right hError (abs_nonneg _)
    _ = abstractNormalizedCellBound CKernel DKernel CMass
          (endpointInvLogCube M n W i) (endpointInvLogCube M n W j)
          (endpointActualMass M n W i)
          (endpointContinuumMass M n W i)
          (endpointContinuumMass M n W j)
          (endpointContinuumMoment M n W i)
          (endpointContinuumMoment M n W j) *
        |(canonicalPartition M hdelta hn hW S).center j /
          (canonicalPartition M hdelta hn hW S).center i| := by
      rw [hIdentification]
    _ ≤ endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W i j := by
      simpa only [endpointDoubleKernelCoarseEntry] using hAbstract

/-- Unconditional canonical sharp-row quadrature.  The PNT constants are
chosen first.  The cutoff `W` is then chosen, and only afterwards are the
accuracy and the ambient integer `n` chosen.  The fixed term is explicitly
`O((log W)^{-3})`; every remaining term tends to zero with `n`, uniformly
over the finite canonical band set. -/
theorem exists_cutoff_eventually_canonical_doubleKernelSharpRowError
    (hdelta : 0 < delta) :
    ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
        ∀ᶠ n : ℕ in atTop,
          ∃ hW : W ≠ 0, ∃ hn : 1 < n,
            ∃ S : ScaleSeparation M n W,
              ∀ i : Fin (M.cellCount + 1),
                endpointDoubleKernelSharpRowError M hdelta hn hW S i ≤
                  CRow / Real.log (W : ℝ) ^ 3 + e := by
  obtain ⟨CKernel, hCKernel, DKernel, hDKernel, CMass, hCMass,
    XKernel, hKernel⟩ := exists_uniform_normalizedDoubleKernelCell_error_bound
  obtain ⟨Cmass, hCmass, Xmass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  obtain ⟨Wcenter, hCenter⟩ :=
    exists_cutoff_eventually_canonical_relativeCenters M hdelta
  let CRow : ℝ := 3 * DKernel + 6 * DKernel / delta + 1
  let W₀ : ℕ := max 2 (max XKernel (max Xmass Wcenter))
  have hCRow : 0 < CRow := by
    dsimp only [CRow]
    have hdiv := div_pos hDKernel hdelta
    positivity
  refine ⟨CRow, hCRow, W₀, ?_⟩
  intro W hW e he
  have hWTwo : 2 ≤ W := (le_max_left 2 (max XKernel (max Xmass Wcenter))).trans hW
  have hXKernel : XKernel ≤ W :=
    ((le_max_left XKernel (max Xmass Wcenter)).trans
      (le_max_right 2 (max XKernel (max Xmass Wcenter)))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass Wcenter).trans
      (le_max_right XKernel (max Xmass Wcenter))).trans
      ((le_max_right 2 (max XKernel (max Xmass Wcenter))).trans hW)
  have hWcenter : Wcenter ≤ W :=
    ((le_max_right Xmass Wcenter).trans
      (le_max_right XKernel (max Xmass Wcenter))).trans
      ((le_max_right 2 (max XKernel (max Xmass Wcenter))).trans hW)
  have hCenterEvent := hCenter W hWcenter (1 / 2) (by norm_num)
  have hReady := eventually_endpointRelativeCenterBound_le M hdelta
    (W := W) Cmass 0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hLowCoarse :=
    (tendsto_low_endpointDoubleKernelCoarseRow M hdelta hWTwo
      CKernel DKernel CMass).eventually
        (eventually_le_nhds (show
          (3 * DKernel + 6 * DKernel / delta) /
              Real.log (W : ℝ) ^ 3 <
            (3 * DKernel + 6 * DKernel / delta) /
              Real.log (W : ℝ) ^ 3 + e / 2 by
          linarith))
  have hPositiveCoarse : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        endpointDoubleKernelCoarseRow M CKernel DKernel CMass n W
          (positiveBand M k) ≤ e / 2 := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_endpointDoubleKernelCoarseRow_zero
      M hdelta W CKernel DKernel CMass k).eventually
        (eventually_le_nhds (half_pos he))
  filter_upwards [hCenterEvent, hReady, hLowCoarse, hPositiveCoarse] with
    n hCenterN hReadyN hLowN hPositiveN
  obtain ⟨hWne, hn, S, hCenterN⟩ := hCenterN
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hMassPos (r : Fin (M.cellCount + 1)) :
      0 < endpointContinuumMass M n W r := (hReadyN r).1
  have hMomentPos (r : Fin (M.cellCount + 1)) :
      0 < endpointContinuumMoment M n W r := (hReadyN r).2.1
  have hMassError (r : Fin (M.cellCount + 1)) :
      |endpointActualMass M n W r - endpointContinuumMass M n W r| ≤
        endpointMassError M Cmass n W r := by
    have hq := hMass (fullCutoff M n W r.1)
      (fullCutoff M n W (r.1 + 1))
      (hXmass.trans (hmono (Nat.zero_le r.1)))
      (hmono (Nat.le_succ r.1))
    simpa only [endpointActualMass, endpointContinuumMass,
      endpointMassError] using hq
  have hMassLower (r : Fin (M.cellCount + 1)) :
      endpointContinuumMass M n W r / 2 ≤ endpointActualMass M n W r := by
    have hleft := (abs_le.mp (hMassError r)).1
    have hsmall := (hReadyN r).2.2.1
    linarith
  have hCenterRel (r : Fin (M.cellCount + 1)) :
      |P.center r / endpointContinuumCenter M n W r - 1| ≤ 1 / 2 := by
    simpa only [P, E, endpointContinuumCenter,
      IntervalCertificate.continuumCenter] using hCenterN r
  have hActualMassPos (r : Fin (M.cellCount + 1)) :
      0 < endpointActualMass M n W r := by
    have hEq : endpointActualMass M n W r = P.mass r := by
      rw [E.mass_eq_fullReciprocalSum_sub]
      rfl
    rw [hEq]
    exact P.data.mass_pos r
  have hY (r : Fin (M.cellCount + 1)) :
      (fullCutoff M n W (r.1 + 1) : ℝ) ≤ y n := by
    have hNat : fullCutoff M n W (r.1 + 1) ≤ yNat n := by
      rw [← fullCutoff_last M (Nat.zero_lt_of_lt hn)]
      exact hmono (by omega)
    exact (by exact_mod_cast hNat :
      (fullCutoff M n W (r.1 + 1) : ℝ) ≤ (yNat n : ℝ)) |>.trans
        (Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le)
  have hCellError (i j : Fin (M.cellCount + 1)) :
      endpointDoubleKernelError M n W i j ≤
        normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
          (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
          (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) := by
    have hq := hKernel (y n) hy
      (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
      (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))
      (hXKernel.trans (hmono (Nat.zero_le i.1)))
      (hmono (Nat.le_succ i.1)) (hY i)
      (hXKernel.trans (hmono (Nat.zero_le j.1)))
      (hmono (Nat.le_succ j.1)) (hY j)
      (hActualMassPos i)
      (by
        have hEq := endpointContinuumMass_eq_doubleKernelMass M hn i
          (hWTwo.trans (hmono (Nat.zero_le i.1)))
          (hmono (Nat.le_succ i.1))
        rw [← hEq]
        exact ne_of_gt (hMassPos i))
    simpa only [endpointDoubleKernelError,
      normalizedDoubleKernelCellBound] using hq
  have hPoint (i j : Fin (M.cellCount + 1)) :
      endpointDoubleKernelError M n W i j * |P.center j / P.center i| ≤
        endpointDoubleKernelCoarseEntry M CKernel DKernel CMass n W i j := by
    exact endpointDoubleKernelError_mul_centerRatio_le_coarse
      M hdelta hn hWne hWTwo S CKernel DKernel CMass
      hCKernel.le hDKernel.le hCMass.le hMassPos hMomentPos hMassLower
      (by simpa only [P] using hCenterRel) i j (hCellError i j)
  have hRow (i : Fin (M.cellCount + 1)) :
      endpointDoubleKernelSharpRowError M hdelta hn hWne S i ≤
        endpointDoubleKernelCoarseRow M CKernel DKernel CMass n W i := by
    unfold endpointDoubleKernelSharpRowError endpointDoubleKernelCoarseRow
    exact Finset.sum_le_sum (fun j _hj ↦ hPoint i j)
  refine ⟨hWne, hn, S, ?_⟩
  intro i
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hInvNonneg : 0 ≤ 1 / Real.log (W : ℝ) ^ 3 := by positivity
  have hMainNonneg : 0 ≤
      (3 * DKernel + 6 * DKernel / delta) /
        Real.log (W : ℝ) ^ 3 := by positivity
  have hCRowIdentity :
      CRow / Real.log (W : ℝ) ^ 3 =
        (3 * DKernel + 6 * DKernel / delta) /
          Real.log (W : ℝ) ^ 3 +
        1 / Real.log (W : ℝ) ^ 3 := by
    dsimp only [CRow]
    ring
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · calc
      endpointDoubleKernelSharpRowError M hdelta hn hWne S (lowBand M) ≤
          endpointDoubleKernelCoarseRow M CKernel DKernel CMass n W
            (lowBand M) := hRow (lowBand M)
      _ ≤ (3 * DKernel + 6 * DKernel / delta) /
          Real.log (W : ℝ) ^ 3 + e / 2 := hLowN
      _ ≤ CRow / Real.log (W : ℝ) ^ 3 + e := by
        rw [hCRowIdentity]
        nlinarith
  · calc
      endpointDoubleKernelSharpRowError M hdelta hn hWne S
          (positiveBand M k) ≤
        endpointDoubleKernelCoarseRow M CKernel DKernel CMass n W
          (positiveBand M k) := hRow (positiveBand M k)
      _ ≤ e / 2 := hPositiveN k
      _ ≤ CRow / Real.log (W : ℝ) ^ 3 + e := by
        rw [hCRowIdentity]
        nlinarith

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
