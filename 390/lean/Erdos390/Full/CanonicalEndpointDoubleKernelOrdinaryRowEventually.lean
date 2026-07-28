import Erdos390.Full.CanonicalEndpointDoubleKernelRowEventually

/-!
# Canonical endpoint double-kernel quadrature in ordinary raw norm

The sharp row estimate weights an input cell by a ratio of arithmetic
centres.  That is the correct estimate after sharp conjugation, but its
fixed-cutoff constant contains the reciprocal of the moving low centre.
For the ordinary raw norm no centre ratio occurs.  This file repeats only
the final finite summation in that norm and obtains a fixed-cutoff constant
which is independent of the later regular mesh.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open PrimeBandQuadrature KernelPrimeQuadrature DoubleKernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- A centre-free majorant for one normalized double-kernel cell. -/
def endpointDoubleKernelOrdinaryCoarseEntry
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i j : Fin (M.cellCount + 1)) : ℝ :=
  DKernel * endpointInvLogCube M n W j +
    2 * DKernel * endpointInvLogCube M n W i *
      (endpointContinuumMass M n W j /
        endpointContinuumMass M n W i) +
    10 * CKernel * CMass * endpointInvLogCube M n W i *
      (endpointContinuumMoment M n W i *
        endpointContinuumMoment M n W j /
          endpointContinuumMass M n W i ^ 2)

def endpointDoubleKernelOrdinaryCoarseRow
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i : Fin (M.cellCount + 1)) : ℝ :=
  ∑ j, endpointDoubleKernelOrdinaryCoarseEntry
    M CKernel DKernel CMass n W i j

/-- Removing the sharp centre ratio from the abstract cell estimate removes
the dangerous reciprocal low-centre factor as well. -/
theorem abstractNormalizedCellBound_le_ordinaryCoarse
    {CKernel DKernel CMass rOut rIn actualOutMass
      continuumOutMass continuumInMass outLength inLength : ℝ}
    (hC : 0 ≤ CKernel) (hD : 0 ≤ DKernel) (hCMass : 0 ≤ CMass)
    (hrOut : 0 ≤ rOut)
    (hActual : 0 < actualOutMass)
    (hOutMass : 0 < continuumOutMass)
    (hInMass : 0 < continuumInMass)
    (hOutLength : 0 ≤ outLength) (hInLength : 0 ≤ inLength)
    (hMassLower : continuumOutMass / 2 ≤ actualOutMass) :
    abstractNormalizedCellBound CKernel DKernel CMass rOut rIn
        actualOutMass continuumOutMass continuumInMass outLength inLength ≤
      DKernel * rIn +
        2 * DKernel * rOut * (continuumInMass / continuumOutMass) +
        10 * CKernel * CMass * rOut *
          (outLength * inLength / continuumOutMass ^ 2) := by
  have hInv : 1 / actualOutMass ≤ 2 / continuumOutMass := by
    rw [div_le_div_iff₀ hActual hOutMass]
    linarith
  have hFirst :
      (DKernel * rIn * actualOutMass +
          DKernel * rOut * continuumInMass) / actualOutMass =
        DKernel * rIn +
          (DKernel * rOut * continuumInMass) * (1 / actualOutMass) := by
    field_simp [ne_of_gt hActual]
  have hSecond :
      (DKernel * rOut * continuumInMass) * (1 / actualOutMass) ≤
        2 * DKernel * rOut * (continuumInMass / continuumOutMass) := by
    calc
      (DKernel * rOut * continuumInMass) * (1 / actualOutMass) ≤
          (DKernel * rOut * continuumInMass) *
            (2 / continuumOutMass) := by gcongr
      _ = 2 * DKernel * rOut *
          (continuumInMass / continuumOutMass) := by ring
  have hThird :
      CKernel * outLength * inLength * (5 * CMass * rOut) /
          (actualOutMass * continuumOutMass) ≤
        10 * CKernel * CMass * rOut *
          (outLength * inLength / continuumOutMass ^ 2) := by
    have hDenInv : 1 / (actualOutMass * continuumOutMass) ≤
        2 / continuumOutMass ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_right hInv
        (one_div_nonneg.mpr hOutMass.le)
      have hrewriteLeft :
          (1 / actualOutMass) * (1 / continuumOutMass) =
            1 / (actualOutMass * continuumOutMass) := by ring
      have hrewriteRight :
          (2 / continuumOutMass) * (1 / continuumOutMass) =
            2 / continuumOutMass ^ 2 := by ring
      simpa only [hrewriteLeft, hrewriteRight] using hmul
    calc
      CKernel * outLength * inLength * (5 * CMass * rOut) /
          (actualOutMass * continuumOutMass) =
        (5 * CKernel * CMass * rOut * outLength * inLength) *
          (1 / (actualOutMass * continuumOutMass)) := by ring
      _ ≤ (5 * CKernel * CMass * rOut * outLength * inLength) *
          (2 / continuumOutMass ^ 2) := by gcongr
      _ = 10 * CKernel * CMass * rOut *
          (outLength * inLength / continuumOutMass ^ 2) := by ring
  unfold abstractNormalizedCellBound
  rw [hFirst]
  exact add_le_add (add_le_add le_rfl hSecond) hThird

theorem endpointDoubleKernelOrdinaryCoarseRow_eq
    (CKernel DKernel CMass : ℝ) (n W : ℕ)
    (i : Fin (M.cellCount + 1)) :
    endpointDoubleKernelOrdinaryCoarseRow
        M CKernel DKernel CMass n W i =
      DKernel * (∑ j, endpointInvLogCube M n W j) +
        2 * DKernel * endpointInvLogCube M n W i *
          ((∑ j, endpointContinuumMass M n W j) /
            endpointContinuumMass M n W i) +
        10 * CKernel * CMass * endpointInvLogCube M n W i *
          (endpointContinuumMoment M n W i *
            (∑ j, endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W i ^ 2) := by
  unfold endpointDoubleKernelOrdinaryCoarseRow
    endpointDoubleKernelOrdinaryCoarseEntry
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum]
  rw [show (∑ x : Fin (M.cellCount + 1),
      2 * DKernel * endpointInvLogCube M n W i *
        (endpointContinuumMass M n W x /
          endpointContinuumMass M n W i)) =
      2 * DKernel * endpointInvLogCube M n W i *
        ((∑ x, endpointContinuumMass M n W x) /
          endpointContinuumMass M n W i) by
    rw [Finset.sum_div, Finset.mul_sum]]
  rw [show (∑ x : Fin (M.cellCount + 1),
      10 * CKernel * CMass * endpointInvLogCube M n W i *
        (endpointContinuumMoment M n W i *
          endpointContinuumMoment M n W x /
            endpointContinuumMass M n W i ^ 2)) =
      10 * CKernel * CMass * endpointInvLogCube M n W i *
        (endpointContinuumMoment M n W i *
          (∑ x, endpointContinuumMoment M n W x) /
            endpointContinuumMass M n W i ^ 2) by
    calc
      _ = ∑ x : Fin (M.cellCount + 1),
          (10 * CKernel * CMass * endpointInvLogCube M n W i *
            endpointContinuumMoment M n W i /
              endpointContinuumMass M n W i ^ 2) *
                endpointContinuumMoment M n W x := by
          apply Finset.sum_congr rfl
          intro x hx
          ring
      _ = (10 * CKernel * CMass * endpointInvLogCube M n W i *
            endpointContinuumMoment M n W i /
              endpointContinuumMass M n W i ^ 2) *
            (∑ x, endpointContinuumMoment M n W x) := by
          rw [Finset.mul_sum]
      _ = _ := by ring]

theorem tendsto_sum_endpointInvLogCube
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      ∑ j : Fin (M.cellCount + 1), endpointInvLogCube M n W j)
      atTop (nhds (1 / Real.log (W : ℝ) ^ 3)) := by
  have hEach : ∀ j : Fin (M.cellCount + 1), Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W j) atTop
      (nhds (Fin.cases (1 / Real.log (W : ℝ) ^ 3)
        (fun _ : Fin M.cellCount ↦ 0) j)) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa only [Fin.cases_zero, lowBand, endpointInvLogCube_low] using
        (tendsto_const_nhds : Tendsto
          (fun _n : ℕ ↦ 1 / Real.log (W : ℝ) ^ 3) atTop
            (nhds (1 / Real.log (W : ℝ) ^ 3)))
    · simpa only [Fin.cases_succ] using
        tendsto_positive_endpointInvLogCube_zero M hdelta W k
  have hSum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
  have hLimit : (∑ j : Fin (M.cellCount + 1),
      Fin.cases (1 / Real.log (W : ℝ) ^ 3)
        (fun _ : Fin M.cellCount ↦ 0) j) =
      1 / Real.log (W : ℝ) ^ 3 := by
    rw [Fin.sum_univ_succ]
    simp
  simpa only [hLimit] using hSum

theorem tendsto_sum_endpointContinuumMoment_one
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      ∑ j : Fin (M.cellCount + 1), endpointContinuumMoment M n W j)
      atTop (nhds 1) := by
  have hEach : ∀ j : Fin (M.cellCount + 1), Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W j) atTop
      (nhds (Fin.cases (motive := fun _ ↦ ℝ) delta
        (fun k : Fin M.cellCount ↦ M.width k) j)) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa only [Fin.cases_zero] using
        tendsto_low_endpointContinuumMoment M hdelta W
    · simpa only [Fin.cases_succ] using
        tendsto_positive_endpointContinuumMoment M hdelta W k
  have hSum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
  have hLimit : (∑ j : Fin (M.cellCount + 1),
      Fin.cases (motive := fun _ ↦ ℝ) delta
        (fun k : Fin M.cellCount ↦ M.width k) j) = (1 : ℝ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cases_zero, Fin.cases_succ]
    rw [M.sum_width_eq_one_sub_delta]
    ring
  simpa only [hLimit] using hSum

theorem tendsto_positive_endpointContinuumMass_sum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      ∑ k : Fin M.cellCount,
        endpointContinuumMass M n W (positiveBand M k)) atTop
      (nhds (∑ k : Fin M.cellCount,
        (Real.log (M.upper k) - Real.log (M.lower k)))) := by
  exact tendsto_finset_sum Finset.univ (fun k _hk ↦
    tendsto_positive_endpointContinuumMass M hdelta W k)

/-- In the moving low row the total continuum harmonic mass is asymptotic
to the low-cell harmonic mass. -/
theorem tendsto_sum_endpointContinuumMass_div_low_one
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j) /
        endpointContinuumMass M n W (lowBand M)) atTop (nhds 1) := by
  have hLow := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hPos := tendsto_positive_endpointContinuumMass_sum M hdelta W
  have hPosDiv := hPos.div_atTop hLow
  have hLowNe : ∀ᶠ n : ℕ in atTop,
      endpointContinuumMass M n W (lowBand M) ≠ 0 :=
    hLow.eventually (eventually_ne_atTop 0)
  have hRewrite : ∀ᶠ n : ℕ in atTop,
      (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j) /
          endpointContinuumMass M n W (lowBand M) =
        1 +
          (∑ k : Fin M.cellCount,
            endpointContinuumMass M n W (positiveBand M k)) /
              endpointContinuumMass M n W (lowBand M) := by
    filter_upwards [hLowNe] with n hzero
    rw [Fin.sum_univ_succ]
    change (endpointContinuumMass M n W (lowBand M) +
        ∑ k : Fin M.cellCount,
          endpointContinuumMass M n W (positiveBand M k)) /
          endpointContinuumMass M n W (lowBand M) = _
    field_simp [hzero]
  have hAdd : Tendsto (fun n : ℕ ↦
      (1 : ℝ) +
        (∑ k : Fin M.cellCount,
          endpointContinuumMass M n W (positiveBand M k)) /
            endpointContinuumMass M n W (lowBand M)) atTop (nhds 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add hPosDiv : Tendsto (fun n : ℕ ↦
        (1 : ℝ) +
          (∑ k : Fin M.cellCount,
            endpointContinuumMass M n W (positiveBand M k)) /
              endpointContinuumMass M n W (lowBand M)) atTop
        (nhds ((1 : ℝ) + 0)))
  exact hAdd.congr' (hRewrite.mono fun n hn ↦ hn.symm)

theorem tendsto_positive_invLogCube_mul_sumContinuumMass_zero
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
        (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j))
      atTop (nhds 0) := by
  have hLow := tendsto_positive_invLogCube_mul_lowMass_zero
    M hdelta hWTwo k
  have hInv := tendsto_positive_endpointInvLogCube_zero M hdelta W k
  have hPos := tendsto_positive_endpointContinuumMass_sum M hdelta W
  have hPosPart := hInv.mul hPos
  have hSplit : ∀ n : ℕ,
      endpointInvLogCube M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1), endpointContinuumMass M n W j) =
        endpointInvLogCube M n W (positiveBand M k) *
            endpointContinuumMass M n W (lowBand M) +
          endpointInvLogCube M n W (positiveBand M k) *
            (∑ j : Fin M.cellCount,
              endpointContinuumMass M n W (positiveBand M j)) := by
    intro n
    rw [Fin.sum_univ_succ]
    change _ * (endpointContinuumMass M n W (lowBand M) +
      ∑ j : Fin M.cellCount,
        endpointContinuumMass M n W (positiveBand M j)) = _
    ring
  have hSum : Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
          endpointContinuumMass M n W (lowBand M) +
        endpointInvLogCube M n W (positiveBand M k) *
          (∑ j : Fin M.cellCount,
            endpointContinuumMass M n W (positiveBand M j)))
      atTop (nhds 0) := by
    have hAdd := hLow.add hPosPart
    simpa only [zero_add, zero_mul, add_zero] using hAdd
  exact hSum.congr' (Filter.Eventually.of_forall fun n ↦ (hSplit n).symm)

theorem tendsto_low_endpointDoubleKernelOrdinaryCoarseRow
    (hdelta : 0 < delta) (W : ℕ)
    (CKernel DKernel CMass : ℝ) :
    Tendsto (fun n : ℕ ↦
      endpointDoubleKernelOrdinaryCoarseRow
        M CKernel DKernel CMass n W (lowBand M)) atTop
      (nhds (3 * DKernel / Real.log (W : ℝ) ^ 3)) := by
  have hInv := tendsto_sum_endpointInvLogCube M hdelta W
  have hMassRatio :=
    tendsto_sum_endpointContinuumMass_div_low_one M hdelta W
  have hLowMoment := tendsto_low_endpointContinuumMoment M hdelta W
  have hMomentSum := tendsto_sum_endpointContinuumMoment_one M hdelta W
  have hLowMass := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hMomentDiv := hLowMoment.div_atTop hLowMass
  have hSumDiv := hMomentSum.div_atTop hLowMass
  have hThirdCore : Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W (lowBand M) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
        endpointContinuumMass M n W (lowBand M) ^ 2) atTop (nhds 0) := by
    have hprod := hMomentDiv.mul hSumDiv
    have hprodZero : Tendsto (fun n : ℕ ↦
        (endpointContinuumMoment M n W (lowBand M) /
            endpointContinuumMass M n W (lowBand M)) *
          ((∑ j : Fin (M.cellCount + 1),
              endpointContinuumMoment M n W j) /
            endpointContinuumMass M n W (lowBand M))) atTop (nhds 0) := by
      simpa only [zero_mul] using hprod
    apply hprodZero.congr'
    have hMassPos := hLowMass.eventually (eventually_gt_atTop 0)
    filter_upwards [hMassPos] with n hn
    field_simp [ne_of_gt hn]
  have hFirst : Tendsto (fun n : ℕ ↦
      DKernel * (∑ j : Fin (M.cellCount + 1),
        endpointInvLogCube M n W j)) atTop
      (nhds (DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
    tendsto_const_nhds.mul hInv
  have hSecond : Tendsto (fun n : ℕ ↦
      2 * DKernel * endpointInvLogCube M n W (lowBand M) *
        ((∑ j : Fin (M.cellCount + 1),
          endpointContinuumMass M n W j) /
            endpointContinuumMass M n W (lowBand M))) atTop
      (nhds (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) := by
    have hconst : Tendsto (fun _n : ℕ ↦
        2 * DKernel * (1 / Real.log (W : ℝ) ^ 3)) atTop
        (nhds (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
      tendsto_const_nhds
    have hmul := hconst.mul hMassRatio
    have hmulLimit : Tendsto (fun n : ℕ ↦
        (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3)) *
          ((∑ j : Fin (M.cellCount + 1),
            endpointContinuumMass M n W j) /
              endpointContinuumMass M n W (lowBand M))) atTop
        (nhds (2 * DKernel * (1 / Real.log (W : ℝ) ^ 3))) := by
      simpa only [mul_one] using hmul
    apply hmulLimit.congr'
    filter_upwards with n
    rw [endpointInvLogCube_low]
  have hThird : Tendsto (fun n : ℕ ↦
      10 * CKernel * CMass * endpointInvLogCube M n W (lowBand M) *
        (endpointContinuumMoment M n W (lowBand M) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (lowBand M) ^ 2))
      atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦
        10 * CKernel * CMass *
          (1 / Real.log (W : ℝ) ^ 3)) atTop
        (nhds (10 * CKernel * CMass *
          (1 / Real.log (W : ℝ) ^ 3))) := tendsto_const_nhds
    have hmul := hconst.mul hThirdCore
    have hmulZero : Tendsto (fun n : ℕ ↦
        (10 * CKernel * CMass * (1 / Real.log (W : ℝ) ^ 3)) *
          (endpointContinuumMoment M n W (lowBand M) *
            (∑ j : Fin (M.cellCount + 1),
              endpointContinuumMoment M n W j) /
                endpointContinuumMass M n W (lowBand M) ^ 2))
        atTop (nhds 0) := by
      simpa only [mul_zero] using hmul
    apply hmulZero.congr'
    filter_upwards with n
    rw [endpointInvLogCube_low]
  rw [show 3 * DKernel / Real.log (W : ℝ) ^ 3 =
      DKernel * (1 / Real.log (W : ℝ) ^ 3) +
        2 * DKernel * (1 / Real.log (W : ℝ) ^ 3) + 0 by ring]
  apply ((hFirst.add hSecond).add hThird).congr'
  filter_upwards with n
  rw [endpointDoubleKernelOrdinaryCoarseRow_eq]

theorem tendsto_positive_endpointDoubleKernelOrdinaryCoarseRow
    (hdelta : 0 < delta) {W : ℕ} (hWTwo : 2 ≤ W)
    (CKernel DKernel CMass : ℝ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointDoubleKernelOrdinaryCoarseRow M CKernel DKernel CMass n W
        (positiveBand M k)) atTop
      (nhds (DKernel / Real.log (W : ℝ) ^ 3)) := by
  have hInvSum := tendsto_sum_endpointInvLogCube M hdelta W
  have hInv := tendsto_positive_endpointInvLogCube_zero M hdelta W k
  have hMassSum := tendsto_positive_invLogCube_mul_sumContinuumMass_zero M
    hdelta hWTwo k
  have hMass := tendsto_positive_endpointContinuumMass M hdelta W k
  have hMoment := tendsto_positive_endpointContinuumMoment M hdelta W k
  have hMomentSum := tendsto_sum_endpointContinuumMoment_one M hdelta W
  let Hk : ℝ := Real.log (M.upper k) - Real.log (M.lower k)
  have hHk : 0 < Hk := by
    dsimp only [Hk]
    exact sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
      ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
      (M.lower_lt_upper hdelta k))
  have hSecondCore := hMassSum.div hMass (ne_of_gt hHk)
  have hThirdCore : Tendsto (fun n : ℕ ↦
      endpointInvLogCube M n W (positiveBand M k) *
        (endpointContinuumMoment M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (positiveBand M k) ^ 2))
      atTop (nhds 0) := by
    have hnum := (hInv.mul hMoment).mul hMomentSum
    have hden := hMass.pow 2
    have hquot := hnum.div hden (pow_ne_zero 2 (ne_of_gt hHk))
    have hquotZero : Tendsto (fun n : ℕ ↦
        (endpointInvLogCube M n W (positiveBand M k) *
            endpointContinuumMoment M n W (positiveBand M k) *
              (∑ j : Fin (M.cellCount + 1),
                endpointContinuumMoment M n W j)) /
          endpointContinuumMass M n W (positiveBand M k) ^ 2)
        atTop (nhds 0) := by
      simpa only [zero_mul, mul_zero, zero_div] using hquot
    apply hquotZero.congr'
    filter_upwards with n
    ring
  have hFirst : Tendsto (fun n : ℕ ↦
      DKernel * (∑ j : Fin (M.cellCount + 1),
        endpointInvLogCube M n W j)) atTop
      (nhds (DKernel / Real.log (W : ℝ) ^ 3)) := by
    have hmul : Tendsto (fun n : ℕ ↦
        DKernel * (∑ j : Fin (M.cellCount + 1),
          endpointInvLogCube M n W j)) atTop
        (nhds (DKernel * (1 / Real.log (W : ℝ) ^ 3))) :=
      tendsto_const_nhds.mul hInvSum
    simpa [div_eq_mul_inv] using hmul
  have hSecond : Tendsto (fun n : ℕ ↦
      2 * DKernel * endpointInvLogCube M n W (positiveBand M k) *
        ((∑ j : Fin (M.cellCount + 1),
          endpointContinuumMass M n W j) /
            endpointContinuumMass M n W (positiveBand M k)))
      atTop (nhds 0) := by
    have hSecondCoreZero : Tendsto (fun n : ℕ ↦
        (endpointInvLogCube M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMass M n W j)) /
              endpointContinuumMass M n W (positiveBand M k))
        atTop (nhds 0) := by
      simpa only [zero_div] using hSecondCore
    have hmul : Tendsto (fun n : ℕ ↦
        (2 * DKernel) *
          (endpointInvLogCube M n W (positiveBand M k) *
            (∑ j : Fin (M.cellCount + 1),
              endpointContinuumMass M n W j) /
                endpointContinuumMass M n W (positiveBand M k)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hSecondCoreZero
    apply hmul.congr'
    filter_upwards with n
    ring
  have hThird : Tendsto (fun n : ℕ ↦
      10 * CKernel * CMass * endpointInvLogCube M n W (positiveBand M k) *
        (endpointContinuumMoment M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (positiveBand M k) ^ 2))
      atTop (nhds 0) := by
    have hmul : Tendsto (fun n : ℕ ↦
        (10 * CKernel * CMass) *
          (endpointInvLogCube M n W (positiveBand M k) *
            (endpointContinuumMoment M n W (positiveBand M k) *
              (∑ j : Fin (M.cellCount + 1),
                endpointContinuumMoment M n W j) /
                  endpointContinuumMass M n W (positiveBand M k) ^ 2)))
        atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hThirdCore
    apply hmul.congr'
    filter_upwards with n
    ring
  have hTotal : Tendsto (fun n : ℕ ↦
      DKernel * (∑ j : Fin (M.cellCount + 1),
        endpointInvLogCube M n W j) +
      2 * DKernel * endpointInvLogCube M n W (positiveBand M k) *
        ((∑ j : Fin (M.cellCount + 1),
          endpointContinuumMass M n W j) /
            endpointContinuumMass M n W (positiveBand M k)) +
      10 * CKernel * CMass * endpointInvLogCube M n W (positiveBand M k) *
        (endpointContinuumMoment M n W (positiveBand M k) *
          (∑ j : Fin (M.cellCount + 1),
            endpointContinuumMoment M n W j) /
              endpointContinuumMass M n W (positiveBand M k) ^ 2))
      atTop (nhds (DKernel / Real.log (W : ℝ) ^ 3)) := by
    simpa only [add_zero] using (hFirst.add hSecond).add hThird
  apply hTotal.congr'
  filter_upwards with n
  rw [endpointDoubleKernelOrdinaryCoarseRow_eq]

/-- A literal normalized double-kernel cell estimate implies the
centre-free coarse entry used by the ordinary raw norm.  No comparison of
arithmetic centres is needed here. -/
theorem endpointDoubleKernelError_le_ordinaryCoarse
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
    (i j : Fin (M.cellCount + 1))
    (hError : endpointDoubleKernelError M n W i j ≤
      normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
        (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
        (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1))) :
    endpointDoubleKernelError M n W i j ≤
      endpointDoubleKernelOrdinaryCoarseEntry
        M CKernel DKernel CMass n W i j := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hLowerTwo (r : Fin (M.cellCount + 1)) :
      2 ≤ fullCutoff M n W r.1 :=
    hWTwo.trans (hmono (Nat.zero_le r.1))
  have hActualEq (r : Fin (M.cellCount + 1)) :
      endpointActualMass M n W r = P.mass r := by
    rw [E.mass_eq_fullReciprocalSum_sub]
    rfl
  have hActualPos (r : Fin (M.cellCount + 1)) :
      0 < endpointActualMass M n W r := by
    rw [hActualEq]
    exact P.data.mass_pos r
  have hAbstract := abstractNormalizedCellBound_le_ordinaryCoarse
    (CKernel := CKernel) (DKernel := DKernel) (CMass := CMass)
    (rOut := endpointInvLogCube M n W i)
    (rIn := endpointInvLogCube M n W j)
    (actualOutMass := endpointActualMass M n W i)
    (continuumOutMass := endpointContinuumMass M n W i)
    (continuumInMass := endpointContinuumMass M n W j)
    (outLength := endpointContinuumMoment M n W i)
    (inLength := endpointContinuumMoment M n W j)
    hC hD hCMass
    (by unfold endpointInvLogCube; positivity)
    (hActualPos i) (hMassPos i) (hMassPos j)
    (hMomentPos i).le (hMomentPos j).le (hMassLower i)
  have hIdentification := normalizedDoubleKernelCellBound_eq_endpointAbstract
    M hn hmono hLowerTwo hMassPos CKernel DKernel CMass i j
  calc
    endpointDoubleKernelError M n W i j ≤
        normalizedDoubleKernelCellBound CKernel DKernel CMass (y n)
          (fullCutoff M n W i.1) (fullCutoff M n W (i.1 + 1))
          (fullCutoff M n W j.1) (fullCutoff M n W (j.1 + 1)) := hError
    _ = abstractNormalizedCellBound CKernel DKernel CMass
          (endpointInvLogCube M n W i) (endpointInvLogCube M n W j)
          (endpointActualMass M n W i)
          (endpointContinuumMass M n W i)
          (endpointContinuumMass M n W j)
          (endpointContinuumMoment M n W i)
          (endpointContinuumMoment M n W j) := hIdentification
    _ ≤ endpointDoubleKernelOrdinaryCoarseEntry
          M CKernel DKernel CMass n W i j := by
      simpa only [endpointDoubleKernelOrdinaryCoarseEntry] using hAbstract

/-- Canonical double-kernel quadrature in ordinary raw row norm.  The
constant and cutoff are selected before `delta`, `eta`, and the mesh.  For
each fixed permitted mesh, only the eventual threshold in `n` may depend on
that mesh. -/
theorem exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError :
    ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
      ∀ {δ ε : ℝ} (N : Mesh δ ε), 0 < δ →
        ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
          ∀ᶠ n : ℕ in atTop,
            ∃ _hW : W ≠ 0, ∃ _hn : 1 < n,
              ∃ _S : ScaleSeparation N n W,
                ∀ i : Fin (N.cellCount + 1),
                  (∑ j : Fin (N.cellCount + 1),
                      endpointDoubleKernelError N n W i j) ≤
                    CRow / Real.log (W : ℝ) ^ 3 + e := by
  obtain ⟨CKernel, hCKernel, DKernel, hDKernel, CMass, hCMass,
    XKernel, hKernel⟩ := exists_uniform_normalizedDoubleKernelCell_error_bound
  obtain ⟨Cmass, hCmass, Xmass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  let CRow : ℝ := 3 * DKernel + 1
  let W₀ : ℕ := max 2 (max XKernel Xmass)
  have hCRow : 0 < CRow := by
    dsimp only [CRow]
    positivity
  refine ⟨CRow, hCRow, W₀, ?_⟩
  intro δ ε N hδ
  let M := N
  have hdelta : 0 < δ := hδ
  intro W hW e he
  have hWTwo : 2 ≤ W :=
    (le_max_left 2 (max XKernel Xmass)).trans hW
  have hWne : W ≠ 0 := by omega
  have hXKernel : XKernel ≤ W :=
    ((le_max_left XKernel Xmass).trans
      (le_max_right 2 (max XKernel Xmass))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_right XKernel Xmass).trans
      (le_max_right 2 (max XKernel Xmass))).trans hW
  have hReady := eventually_endpointRelativeCenterBound_le M
    hdelta (W := W) Cmass 0
      (by norm_num : (0 : ℝ) < 1 / 2)
  have hLowCoarse :=
    (tendsto_low_endpointDoubleKernelOrdinaryCoarseRow M
      hdelta W CKernel DKernel CMass).eventually
        (eventually_le_nhds (show
          3 * DKernel / Real.log (W : ℝ) ^ 3 <
            3 * DKernel / Real.log (W : ℝ) ^ 3 + e / 2 by
          linarith))
  have hPositiveCoarse : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        endpointDoubleKernelOrdinaryCoarseRow
            M CKernel DKernel CMass n W (positiveBand M k) ≤
          DKernel / Real.log (W : ℝ) ^ 3 + e / 2 := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_endpointDoubleKernelOrdinaryCoarseRow
      M hdelta hWTwo CKernel DKernel CMass k).eventually
        (eventually_le_nhds (show
          DKernel / Real.log (W : ℝ) ^ 3 <
            DKernel / Real.log (W : ℝ) ^ 3 + e / 2 by
          linarith))
  have hNgt : ∀ᶠ n : ℕ in atTop, 1 < n := eventually_gt_atTop 1
  have hSep := eventually_scaleSeparation M hdelta W
  filter_upwards [hReady, hLowCoarse, hPositiveCoarse, hNgt, hSep] with
    n hReadyN hLowN hPositiveN hn S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn
      (W_le_first_fullCutoff M S)
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
      endpointDoubleKernelError M n W i j ≤
        endpointDoubleKernelOrdinaryCoarseEntry
          M CKernel DKernel CMass n W i j :=
    endpointDoubleKernelError_le_ordinaryCoarse
      M hdelta hn hWne hWTwo S
      CKernel DKernel CMass hCKernel.le hDKernel.le hCMass.le
      hMassPos hMomentPos hMassLower i j (hCellError i j)
  have hRow (i : Fin (M.cellCount + 1)) :
      (∑ j : Fin (M.cellCount + 1),
          endpointDoubleKernelError M n W i j) ≤
        endpointDoubleKernelOrdinaryCoarseRow
          M CKernel DKernel CMass n W i := by
    unfold endpointDoubleKernelOrdinaryCoarseRow
    exact Finset.sum_le_sum (fun j _hj ↦ hPoint i j)
  refine ⟨hWne, hn, S, ?_⟩
  intro i
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hInvNonneg : 0 ≤ 1 / Real.log (W : ℝ) ^ 3 := by positivity
  have hCRowIdentity :
      CRow / Real.log (W : ℝ) ^ 3 =
        3 * DKernel / Real.log (W : ℝ) ^ 3 +
          1 / Real.log (W : ℝ) ^ 3 := by
    dsimp only [CRow]
    ring
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · calc
      (∑ j : Fin (M.cellCount + 1),
          endpointDoubleKernelError M n W (lowBand M) j) ≤
        endpointDoubleKernelOrdinaryCoarseRow
          M CKernel DKernel CMass n W (lowBand M) := hRow (lowBand M)
      _ ≤ 3 * DKernel / Real.log (W : ℝ) ^ 3 + e / 2 := hLowN
      _ ≤ CRow / Real.log (W : ℝ) ^ 3 + e := by
        rw [hCRowIdentity]
        nlinarith
  · calc
      (∑ j : Fin (M.cellCount + 1),
          endpointDoubleKernelError M n W (positiveBand M k) j) ≤
        endpointDoubleKernelOrdinaryCoarseRow
          M CKernel DKernel CMass n W (positiveBand M k) :=
            hRow (positiveBand M k)
      _ ≤ DKernel / Real.log (W : ℝ) ^ 3 + e / 2 := hPositiveN k
      _ ≤ CRow / Real.log (W : ℝ) ^ 3 + e := by
        rw [hCRowIdentity]
        have hDNonneg : 0 ≤ DKernel := hDKernel.le
        have hScale :
            DKernel / Real.log (W : ℝ) ^ 3 ≤
              3 * DKernel / Real.log (W : ℝ) ^ 3 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          nlinarith [mul_nonneg hDNonneg
            (inv_nonneg.mpr (pow_nonneg hlogW.le 3))]
        linarith


end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
