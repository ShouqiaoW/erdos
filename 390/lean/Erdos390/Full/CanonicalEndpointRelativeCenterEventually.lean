import Erdos390.Full.CanonicalEndpointMeshGeometryEventually
import Erdos390.Full.MovingLowGaugeTransfer

/-!
# Relative centre convergence for the canonical endpoint family

This is the endpoint-level convergence needed by the moving-low sharp
projection.  In particular the conclusion is relative even on the low band,
whose centre tends to zero.  Constants in the two PNT estimates are selected
before the cutoff and before `n`.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- The cutoff is chosen solely from the two global prime-sum estimates.  In
particular it is definitionally independent of every later regular mesh. -/
noncomputable def canonicalRelativeCenterCutoff : ℕ :=
  max 2 (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Endpoint continuum mass, before mentioning a partition proof. -/
def endpointContinuumMass (n W : ℕ) (j : Fin (M.cellCount + 1)) : ℝ :=
  Real.log (Real.log (fullCutoff M n W (j.1 + 1) : ℝ)) -
    Real.log (Real.log (fullCutoff M n W j.1 : ℝ))

/-- Endpoint continuum first moment on the `log y` scale. -/
def endpointContinuumMoment (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  (Real.log (fullCutoff M n W (j.1 + 1) : ℝ) -
    Real.log (fullCutoff M n W j.1 : ℝ)) / Real.log (y n)

def endpointMassError (C : ℝ) (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  5 * C / Real.log (fullCutoff M n W j.1 : ℝ) ^ 3

def endpointMomentError (C : ℝ) (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  (2 * C / Real.log (fullCutoff M n W j.1 : ℝ) ^ 3 +
    C / (2 * Real.log (fullCutoff M n W j.1 : ℝ) ^ 2)) /
      Real.log (y n)

def endpointRelativeCenterBound (Cmass Cmoment : ℝ) (n W : ℕ)
    (j : Fin (M.cellCount + 1)) : ℝ :=
  2 * endpointMomentError M Cmoment n W j /
      endpointContinuumMoment M n W j +
    2 * endpointMassError M Cmass n W j /
      endpointContinuumMass M n W j

theorem endpointContinuumMoment_eq_coordinateLength
    {n W : ℕ} (hn : 1 < n) (j : Fin (M.cellCount + 1)) :
    endpointContinuumMoment M n W j =
      actualCutoffCoordinate M n W (j.1 + 1) -
        actualCutoffCoordinate M n W j.1 := by
  have hlog : Real.log (y n) ≠ 0 := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_ne_zero (by norm_num) (ne_of_gt
      (Real.log_pos (by exact_mod_cast hn)))
  unfold endpointContinuumMoment actualCutoffCoordinate realLogCoordinate
  field_simp [hlog]

theorem tendsto_low_endpointContinuumMoment
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W (lowBand M))
      atTop (nhds delta) := by
  have hcoord := tendsto_low_actualCoordinateLength M hdelta W
  apply hcoord.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [endpointContinuumMoment_eq_coordinateLength M hn]
  rfl

theorem tendsto_positive_endpointContinuumMoment
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMoment M n W (positiveBand M k))
      atTop (nhds (M.width k)) := by
  have hcoord := tendsto_positive_actualCoordinateLength M hdelta W k
  apply hcoord.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [endpointContinuumMoment_eq_coordinateLength M hn]
  rfl

theorem tendsto_positive_endpointContinuumMass
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (positiveBand M k))
      atTop (nhds (Real.log (M.upper k) - Real.log (M.lower k))) := by
  have hLower : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using
        tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)
  have hUpper : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
    have hup : 0 < M.upper k :=
      (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
    simpa only [actualCutoffCoordinate,
      show k.1 + 2 = (k.1 + 1) + 1 by omega,
      fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
        tendsto_floor_scalePoint_coordinate hup
  have hLogLower :=
    (Real.continuousAt_log (ne_of_gt (M.lower_pos hdelta k))).tendsto.comp
      hLower
  have hup : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  have hLogUpper :=
    (Real.continuousAt_log (ne_of_gt hup)).tendsto.comp hUpper
  have hCoordMass := hLogUpper.sub hLogLower
  apply hCoordMass.congr'
  have hTwo := eventually_threshold_le_nonlow_fullCutoff M hdelta W 2
    (positiveBand M k) (by
      intro h
      have := congrArg Fin.val h
      simp only [positiveBand, lowBand, Fin.val_mk] at this
      omega)
  filter_upwards [eventually_gt_atTop 1,
    eventually_scaleSeparation M hdelta W, hTwo] with n hn S hLowerTwo
  have hAY : fullCutoff M n W (k.1 + 1) ≤
      fullCutoff M n W (k.1 + 2) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S) (by omega)
  have hmass := log_logCoordinate_sub
    (show 1 < y n by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog)
    hLowerTwo hAY
  simpa only [endpointContinuumMass, positiveBand,
    actualCutoffCoordinate, realLogCoordinate,
    PrimeBandQuadrature.logCoordinate] using hmass

theorem tendsto_low_endpointContinuumMass_atTop
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointContinuumMass M n W (lowBand M)) atTop atTop := by
  have hCutNat : Tendsto (fun n : ℕ ↦ fullCutoff M n W 1)
      atTop atTop := by
    simpa only [fullCutoff_succ, M.endpoint_zero] using
      tendsto_nat_floor_atTop.comp (tendsto_scalePoint_atTop hdelta)
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hCutNat
  have hLogLog := Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp hCutReal)
  rw [tendsto_atTop]
  intro b
  have hEvent := hLogLog.eventually
    (eventually_ge_atTop (b + Real.log (Real.log (W : ℝ))))
  filter_upwards [hEvent] with n hn
  change b + Real.log (Real.log (W : ℝ)) ≤
    Real.log (Real.log (fullCutoff M n W 1 : ℝ)) at hn
  unfold endpointContinuumMass lowBand
  simp only [Nat.zero_add, fullCutoff_zero]
  linarith

theorem tendsto_general_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))

theorem tendsto_positive_endpointMassError_zero
    (hdelta : 0 < delta) (C : ℝ) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointMassError M C n W (positiveBand M k))
      atTop (nhds 0) := by
  have hReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
  have hLog := Real.tendsto_log_atTop.comp hReal
  have hInv := tendsto_inv_atTop_zero.comp hLog
  have hMain := (tendsto_const_nhds : Tendsto
    (fun _n : ℕ ↦ 5 * C) atTop (nhds (5 * C))).mul (hInv.pow 3)
  have hMainZero : Tendsto (fun n : ℕ ↦
      5 * C * (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3)
      atTop (nhds 0) := by simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  unfold endpointMassError positiveBand
  rw [div_eq_mul_inv, inv_pow]

theorem tendsto_positive_endpointMomentError_zero
    (hdelta : 0 < delta) (C : ℝ) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      endpointMomentError M C n W (positiveBand M k))
      atTop (nhds 0) := by
  have hReal : Tendsto (fun n : ℕ ↦
      (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
  have hLog := Real.tendsto_log_atTop.comp hReal
  have hInvA := tendsto_inv_atTop_zero.comp hLog
  have hInvY := tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hNumerator : Tendsto (fun n : ℕ ↦
      2 * C * (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3 +
        (C / 2) *
          (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 2)
      atTop (nhds 0) := by
    convert ((tendsto_const_nhds.mul (hInvA.pow 3)).add
      (tendsto_const_nhds.mul (hInvA.pow 2))) using 1
    all_goals ring
  have hMain := hNumerator.mul hInvY
  have hMainZero : Tendsto (fun n : ℕ ↦
      (2 * C * (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 3 +
        (C / 2) *
          (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹ ^ 2) *
        (Real.log (y n))⁻¹) atTop (nhds 0) := by
    simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  unfold endpointMomentError positiveBand
  ring

theorem tendsto_low_endpointMomentError_zero
    (C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      endpointMomentError M C n W (lowBand M))
      atTop (nhds 0) := by
  have hInvY := tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hMain := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦
      2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)) atTop
      (nhds (2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)))).mul hInvY
  simpa only [endpointMomentError, lowBand, Fin.val_mk,
    fullCutoff_zero, div_eq_mul_inv, mul_zero] using hMain

/-- For every fixed admissible cutoff, the full relative centre bound tends
to zero simultaneously in all canonical bands. -/
theorem eventually_endpointRelativeCenterBound_le
    (hdelta : 0 < delta) {W : ℕ}
    (Cmass Cmoment : ℝ) {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (M.cellCount + 1),
      0 < endpointContinuumMass M n W j ∧
      0 < endpointContinuumMoment M n W j ∧
      endpointMassError M Cmass n W j ≤
        endpointContinuumMass M n W j / 2 ∧
      endpointRelativeCenterBound M Cmass Cmoment n W j ≤ e := by
  have hLowMass := tendsto_low_endpointContinuumMass_atTop M hdelta W
  have hLowMoment := tendsto_low_endpointContinuumMoment M hdelta W
  have hLowMomentErr := tendsto_low_endpointMomentError_zero M Cmoment W
  let lowMassErr := 5 * Cmass / Real.log (W : ℝ) ^ 3
  have hLowMassErrEq : ∀ n,
      endpointMassError M Cmass n W (lowBand M) = lowMassErr := by
    intro n
    rfl
  have hLowReady : ∀ᶠ n : ℕ in atTop,
      0 < endpointContinuumMass M n W (lowBand M) ∧
      0 < endpointContinuumMoment M n W (lowBand M) ∧
      endpointMassError M Cmass n W (lowBand M) ≤
        endpointContinuumMass M n W (lowBand M) / 2 ∧
      endpointRelativeCenterBound M Cmass Cmoment n W (lowBand M) ≤ e := by
    have hMassPos := hLowMass.eventually (eventually_gt_atTop 0)
    have hMomentPos := hLowMoment.eventually
      (eventually_gt_nhds hdelta)
    have hMassSmall := hLowMass.eventually
      (eventually_ge_atTop (2 * lowMassErr))
    have hRel : Tendsto (fun n : ℕ ↦
        endpointRelativeCenterBound M Cmass Cmoment n W (lowBand M))
        atTop (nhds 0) := by
      unfold endpointRelativeCenterBound
      have hTwo : Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
        tendsto_const_nhds
      have hFirst := (hTwo.mul hLowMomentErr).div hLowMoment
        (ne_of_gt hdelta)
      have hMassErrT : Tendsto (fun n : ℕ ↦
          endpointMassError M Cmass n W (lowBand M))
          atTop (nhds lowMassErr) := by
        apply tendsto_const_nhds.congr'
        exact Filter.Eventually.of_forall hLowMassErrEq
      have hSecond := (hTwo.mul hMassErrT).div_atTop hLowMass
      simpa only [Pi.div_apply, mul_zero, zero_div, add_zero] using
        hFirst.add hSecond
    have hRelSmall := hRel.eventually (eventually_le_nhds he)
    filter_upwards [hMassPos, hMomentPos, hMassSmall, hRelSmall] with
      n hm hmo hsmall hrel
    refine ⟨hm, hmo, ?_, hrel⟩
    rw [hLowMassErrEq]
    linarith
  have hPositiveReady : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
      0 < endpointContinuumMass M n W (positiveBand M k) ∧
      0 < endpointContinuumMoment M n W (positiveBand M k) ∧
      endpointMassError M Cmass n W (positiveBand M k) ≤
        endpointContinuumMass M n W (positiveBand M k) / 2 ∧
      endpointRelativeCenterBound M Cmass Cmoment n W
        (positiveBand M k) ≤ e := by
    rw [Filter.eventually_all]
    intro k
    have hMass := tendsto_positive_endpointContinuumMass M hdelta W k
    have hMoment := tendsto_positive_endpointContinuumMoment M hdelta W k
    have hMassErr := tendsto_positive_endpointMassError_zero M hdelta Cmass W k
    have hMomentErr :=
      tendsto_positive_endpointMomentError_zero M hdelta Cmoment W k
    have hMassLimit : 0 < Real.log (M.upper k) - Real.log (M.lower k) :=
      sub_pos.mpr (Real.strictMonoOn_log (M.lower_pos hdelta k)
        ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
        (M.lower_lt_upper hdelta k))
    have hMomentLimit : 0 < M.width k := M.width_pos hdelta k
    have hMassPos := hMass.eventually (eventually_gt_nhds hMassLimit)
    have hMomentPos := hMoment.eventually
      (eventually_gt_nhds hMomentLimit)
    have hMassSmall : Tendsto (fun n : ℕ ↦
        endpointContinuumMass M n W (positiveBand M k) / 2 -
          endpointMassError M Cmass n W (positiveBand M k))
        atTop (nhds ((Real.log (M.upper k) - Real.log (M.lower k)) / 2)) := by
      simpa only [sub_zero] using hMass.div_const 2 |>.sub hMassErr
    have hMassSmallEvent := hMassSmall.eventually
      (eventually_ge_nhds (div_pos hMassLimit (by norm_num)))
    have hRel : Tendsto (fun n : ℕ ↦
        endpointRelativeCenterBound M Cmass Cmoment n W
          (positiveBand M k)) atTop (nhds 0) := by
      unfold endpointRelativeCenterBound
      have hTwo : Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
        tendsto_const_nhds
      have hFirst := (hTwo.mul hMomentErr).div hMoment
        (ne_of_gt hMomentLimit)
      have hSecond := (hTwo.mul hMassErr).div hMass
        (ne_of_gt hMassLimit)
      simpa only [Pi.div_apply, mul_zero, zero_div, add_zero] using
        hFirst.add hSecond
    have hRelEvent := hRel.eventually (eventually_le_nhds he)
    filter_upwards [hMassPos, hMomentPos, hMassSmallEvent, hRelEvent] with
      n hm hmo hsmall hrel
    exact ⟨hm, hmo, by linarith, hrel⟩
  filter_upwards [hLowReady, hPositiveReady] with n hlow hpos
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa only [lowBand] using hlow
  · simpa only [positiveBand] using hpos k

/-- Relative-centre convergence with the *global* arithmetic cutoff exposed.
The cutoff is selected before, and is independent of, `M`; only the eventual
ambient threshold may depend on the mesh. -/
theorem canonicalRelativeCenterCutoff_eventually
    (hdelta : 0 < delta) (W : ℕ)
    (hW : canonicalRelativeCenterCutoff ≤ W) (e : ℝ) (he : 0 < e) :
      ∀ᶠ n : ℕ in atTop, ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        ∃ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let E := canonicalCertificate M hdelta hn hWne S
          ∀ j : Fin (M.cellCount + 1),
            |P.center j / E.continuumCenter j - 1| ≤ e := by
  let Cmass := PrimeBandQuadrature.fullReciprocalSumUniformConstant
  let Cmoment := MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  have hW2 : 2 ≤ W := (le_max_left 2
    (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)).trans hW
  have hXmass : PrimeBandQuadrature.fullReciprocalSumUniformCutoff ≤ W :=
    ((le_max_left PrimeBandQuadrature.fullReciprocalSumUniformCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2
        (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
          MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hW
  have hXmoment : MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ W :=
    ((le_max_right PrimeBandQuadrature.fullReciprocalSumUniformCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2
        (max PrimeBandQuadrature.fullReciprocalSumUniformCutoff
          MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hW
  have hReady := eventually_endpointRelativeCenterBound_le M hdelta
    (W := W) Cmass Cmoment he
  have hSep := eventually_scaleSeparation M hdelta W
  filter_upwards [eventually_gt_atTop 1, hSep, hReady] with n hn S hR
  have hWne : W ≠ 0 := by omega
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  refine ⟨hWne, hn, S, ?_⟩
  dsimp only
  intro j
  have hLowerThresholdMass :
      PrimeBandQuadrature.fullReciprocalSumUniformCutoff ≤ E.lower j :=
    hXmass.trans (E.cutoff_le_lower j)
  have hLowerThresholdMoment :
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ E.lower j :=
    hXmoment.trans (E.cutoff_le_lower j)
  have hMassQ : |P.mass j - E.continuumMass j| ≤
      endpointMassError M Cmass n W j := by
    have h := PrimeBandQuadrature.fullReciprocalSumUniform_bound
      (E.lower j) (E.upper j)
      hLowerThresholdMass (E.lower_le_upper j)
    rw [E.mass_eq_fullReciprocalSum_sub]
    simpa only [P, E, canonicalCertificate_lower,
      canonicalCertificate_upper, endpointMassError] using h
  have hMomentQ : |P.mass j * P.center j - E.continuumMoment j| ≤
      endpointMomentError M Cmoment n W j := by
    have h := MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound
      (E.lower j) (E.upper j)
      hLowerThresholdMoment (E.lower_le_upper j)
    rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    have hNorm :
        |(PrimeSums.fullLogReciprocalSum (E.upper j) -
              PrimeSums.fullLogReciprocalSum (E.lower j)) /
              Real.log (y n) - E.continuumMoment j| ≤
          (2 * Cmoment / Real.log (E.lower j : ℝ) ^ 3 +
            Cmoment / (2 * Real.log (E.lower j : ℝ) ^ 2)) /
              Real.log (y n) := by
      unfold IntervalCertificate.continuumMoment
      rw [show
        (PrimeSums.fullLogReciprocalSum (E.upper j) -
              PrimeSums.fullLogReciprocalSum (E.lower j)) /
              Real.log (y n) -
            (Real.log (E.upper j : ℝ) - Real.log (E.lower j : ℝ)) /
              Real.log (y n) =
          ((PrimeSums.fullLogReciprocalSum (E.upper j) -
              PrimeSums.fullLogReciprocalSum (E.lower j)) -
            (Real.log (E.upper j : ℝ) - Real.log (E.lower j : ℝ))) /
              Real.log (y n) by ring]
      rw [abs_div, abs_of_pos hlog]
      exact div_le_div_of_nonneg_right h hlog.le
    simpa only [P, E, canonicalCertificate_lower,
      endpointMomentError] using hNorm
  have hMassId : E.continuumMass j = endpointContinuumMass M n W j := by
    rfl
  have hMomentId : E.continuumMoment j =
      endpointContinuumMoment M n W j := by rfl
  have hBound := center_ratio_error_le_two_errors E j hMassQ hMomentQ
    (by rw [hMassId]; exact (hR j).1)
    (by rw [hMomentId]; exact (hR j).2.1)
    (by rw [hMassId]; exact (hR j).2.2.1)
  exact hBound.trans (by
    simpa only [hMassId, hMomentId, endpointRelativeCenterBound] using
      (hR j).2.2.2)

/-- Existential compatibility form.  Its witness is the named global cutoff
above, so callers that need the paper's `W`-before-mesh parameter order should
prefer `canonicalRelativeCenterCutoff_eventually`. -/
theorem exists_cutoff_eventually_canonical_relativeCenters
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
      ∀ᶠ n : ℕ in atTop, ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        ∃ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let E := canonicalCertificate M hdelta hn hWne S
          ∀ j : Fin (M.cellCount + 1),
            |P.center j / E.continuumCenter j - 1| ≤ e :=
  ⟨canonicalRelativeCenterCutoff,
    fun W hW e he ↦ canonicalRelativeCenterCutoff_eventually M hdelta W hW e he⟩

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
