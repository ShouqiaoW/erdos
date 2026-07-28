import Erdos390.Full.RegularMeshActualMomentBounds
import Erdos390.Full.CanonicalEndpointAnchorCoverage

/-!
# Eventual actual-prime moment bounds on the canonical regular mesh

This file discharges the `MomentReady` inputs of
`RegularMeshActualMomentBounds` from the unconditional prime number theorem
quadratures.  The endpoint family is the canonical family of floored powers
of `y`; no continuum mesh, prime-population, or moment estimate is assumed.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature
open PrimeIntervalPartitionConstructor PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The logarithmic coordinate of one explicit natural cutoff. -/
def cutoffCoordinate (n W r : ℕ) : ℝ :=
  realLogCoordinate (y n) (fullCutoff M n W r : ℝ)

theorem tendsto_log_y_atTop :
    Tendsto (fun n : ℕ ↦ Real.log (y n)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_y_atTop

theorem tendsto_fixed_cutoffCoordinate_zero (W : ℕ) :
    Tendsto (fun n : ℕ ↦ realLogCoordinate (y n) (W : ℝ))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto (fun _n : ℕ ↦ Real.log (W : ℝ)) atTop
      (nhds (Real.log (W : ℝ))) := tendsto_const_nhds
  simpa only [realLogCoordinate, div_eq_mul_inv, mul_zero] using
    hConst.mul hInv

theorem tendsto_floor_scalePoint_coordinate
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ))
      atTop (nhds t) := by
  have hLoss : Tendsto (fun n : ℕ ↦ Real.log 2 / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_y_atTop
  have hLowerT : Tendsto
      (fun n : ℕ ↦ t - Real.log 2 / Real.log (y n))
      atTop (nhds t) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hLoss
  have hUpperT : Tendsto (fun _n : ℕ ↦ t) atTop (nhds t) :=
    tendsto_const_nhds
  have hTwo := (tendsto_scalePoint_atTop ht).eventually
    (eventually_ge_atTop (2 : ℝ))
  have hLower : ∀ᶠ n : ℕ in atTop,
      t - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) := by
    filter_upwards [eventually_gt_atTop 1, hTwo] with n hn hnTwo
    exact (floor_scalePoint_coordinate_bounds hn hnTwo).1
  have hUpper : ∀ᶠ n : ℕ in atTop,
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ≤ t := by
    filter_upwards [eventually_gt_atTop 1, hTwo] with n hn hnTwo
    exact (floor_scalePoint_coordinate_bounds hn hnTwo).2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hLowerT hUpperT hLower hUpper

theorem tendsto_positive_lowerCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
  simpa only [cutoffCoordinate, fullCutoff_succ,
    RegularRelativeMesh.Mesh.lower] using
      tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)

theorem tendsto_positive_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  simpa only [cutoffCoordinate, show k.1 + 2 = (k.1 + 1) + 1 by omega,
    fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
      tendsto_floor_scalePoint_coordinate hUpperPos

theorem tendsto_low_upperCoordinate
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ cutoffCoordinate M n W 1)
      atTop (nhds delta) := by
  simpa only [cutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
    tendsto_floor_scalePoint_coordinate hdelta

/-- Harmonic continuum main term expressed in the actual floored endpoint
coordinates of a positive cell. -/
def positiveContinuumMass (n W : ℕ) (k : Fin M.cellCount) : ℝ :=
  Real.log (cutoffCoordinate M n W (k.1 + 2)) -
    Real.log (cutoffCoordinate M n W (k.1 + 1))

/-- First-coordinate continuum main term for the moving low cell. -/
def lowFirstContinuum (n W : ℕ) : ℝ :=
  cutoffCoordinate M n W 1 - realLogCoordinate (y n) (W : ℝ)

/-- Second-coordinate continuum main term for the moving low cell. -/
def lowSecondContinuum (n W : ℕ) : ℝ :=
  (cutoffCoordinate M n W 1 ^ 2 -
    realLogCoordinate (y n) (W : ℝ) ^ 2) / 2

theorem tendsto_positiveContinuumMass
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ positiveContinuumMass M n W k) atTop
      (nhds (M.cellHarmonicMass k)) := by
  have hLower := tendsto_positive_lowerCoordinate M hdelta W k
  have hUpper := tendsto_positive_upperCoordinate M hdelta W k
  have hLogLower : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 1)))
      atTop (nhds (Real.log (M.lower k))) :=
    (Real.continuousAt_log (ne_of_gt (M.lower_pos hdelta k))).tendsto.comp
      hLower
  have hUpperPos : 0 < M.upper k :=
    (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
  have hLogUpper : Tendsto
      (fun n : ℕ ↦ Real.log (cutoffCoordinate M n W (k.1 + 2)))
      atTop (nhds (Real.log (M.upper k))) :=
    (Real.continuousAt_log (ne_of_gt hUpperPos)).tendsto.comp hUpper
  have hDiff := hLogUpper.sub hLogLower
  simpa only [positiveContinuumMass,
    RegularRelativeMesh.Mesh.cellHarmonicMass,
    Real.log_div (ne_of_gt hUpperPos)
      (ne_of_gt (M.lower_pos hdelta k))] using hDiff

theorem tendsto_lowFirstContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowFirstContinuum M n W)
      atTop (nhds delta) := by
  simpa only [lowFirstContinuum, sub_zero] using
    (tendsto_low_upperCoordinate M hdelta W).sub
      (tendsto_fixed_cutoffCoordinate_zero W)

theorem tendsto_lowSecondContinuum
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ lowSecondContinuum M n W)
      atTop (nhds (delta ^ 2 / 2)) := by
  have hUpper := (tendsto_low_upperCoordinate M hdelta W).pow 2
  have hLower := (tendsto_fixed_cutoffCoordinate_zero W).pow 2
  have hDiff := hUpper.sub hLower
  have hDiv := hDiff.div_const (2 : ℝ)
  simpa only [lowSecondContinuum, zero_pow (by omega : 2 ≠ 0), sub_zero]
    using hDiv

theorem tendsto_positive_lowerCutoff_atTop
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦ fullCutoff M n W (k.1 + 1))
      atTop atTop := by
  simpa only [fullCutoff_succ, RegularRelativeMesh.Mesh.lower] using
    tendsto_nat_floor_atTop.comp
      (tendsto_scalePoint_atTop (M.lower_pos hdelta k))

theorem tendsto_positive_massError_zero
    (hdelta : 0 < delta) (W : ℕ) (C : ℝ)
    (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      5 * C / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3)
      atTop (nhds 0) := by
  have hCutReal : Tendsto
      (fun n : ℕ ↦ (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_positive_lowerCutoff_atTop M hdelta W k)
  have hLog : Tendsto
      (fun n : ℕ ↦ Real.log (fullCutoff M n W (k.1 + 1) : ℝ))
      atTop atTop := Real.tendsto_log_atTop.comp hCutReal
  have hInv : Tendsto (fun n : ℕ ↦
      (Real.log (fullCutoff M n W (k.1 + 1) : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLog
  have hConst : Tendsto (fun _n : ℕ ↦ 5 * C) atTop (nhds (5 * C)) :=
    tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 3)
  simpa only [div_eq_mul_inv, inv_pow, mul_zero, zero_pow (by omega : 3 ≠ 0)]
    using hMain

theorem tendsto_lowFirstError_zero (C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      (2 * C / Real.log (W : ℝ) ^ 3 +
        C / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n))
      atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop tendsto_log_y_atTop

theorem tendsto_lowSecondError_zero
    (C : ℝ) {W : ℕ} (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      3 * C / (Real.log (y n) ^ 2 * Real.log (W : ℝ)))
      atTop (nhds 0) := by
  have hInv : Tendsto (fun n : ℕ ↦ (Real.log (y n))⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_log_y_atTop
  have hConst : Tendsto
      (fun _n : ℕ ↦ 3 * C / Real.log (W : ℝ)) atTop
      (nhds (3 * C / Real.log (W : ℝ))) := tendsto_const_nhds
  have hMain := hConst.mul (hInv.pow 2)
  have hMainZero : Tendsto (fun n : ℕ ↦
      (3 * C / Real.log (W : ℝ)) * (Real.log (y n))⁻¹ ^ 2)
      atTop (nhds 0) := by simpa using hMain
  apply hMainZero.congr'
  filter_upwards with n
  have hLogW : Real.log (W : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hW))
  field_simp [hLogW]

theorem tendsto_lowHarmonicMain_atTop
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
        Real.log (Real.log (W : ℝ))) atTop atTop := by
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
  linarith

/-- Endpoint-only inequalities needed to turn the three uniform PNT
quadratures into `MomentReady`.  All displayed endpoints are the actual
floored natural endpoints. -/
structure EndpointMomentBounds (n W : ℕ)
    (Cmass Cfirst Csecond : ℝ) : Prop where
  n_gt_one : 1 < n
  positiveMain : ∀ k : Fin M.cellCount,
    positiveContinuumMass M n W k ≤ 2 * M.ratio
  positiveMassError : ∀ k : Fin M.cellCount,
    5 * Cmass / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 ≤
      M.ratio
  lowFirstMain : lowFirstContinuum M n W ≤ 3 * delta / 2
  lowFirstError :
    (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
      Cfirst / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n) ≤
        delta / 2
  lowSecondMainLower : 5 * delta ^ 2 / 12 ≤
    lowSecondContinuum M n W
  lowSecondMainUpper : lowSecondContinuum M n W ≤
    11 * delta ^ 2 / 12
  lowSecondError :
    3 * Csecond / (Real.log (y n) ^ 2 * Real.log (W : ℝ)) ≤
      delta ^ 2 / 12
  lowMassMain :
    48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
      Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
        Real.log (Real.log (W : ℝ))

theorem eventually_endpointMomentBounds
    (hdelta : 0 < delta) (W : ℕ) (Cmass Cfirst Csecond : ℝ)
    (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      EndpointMomentBounds M n W Cmass Cfirst Csecond := by
  have hPositiveMain : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        positiveContinuumMass M n W k ≤ 2 * M.ratio := by
    rw [Filter.eventually_all]
    intro k
    have hT := tendsto_positiveContinuumMass M hdelta W k
    have hLimit : M.cellHarmonicMass k < 2 * M.ratio :=
      (M.cellHarmonicMass_le_ratio hdelta k).trans_lt (by
        linarith [M.ratio_pos])
    exact hT.eventually (eventually_le_nhds hLimit)
  have hPositiveError : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        5 * Cmass / Real.log (fullCutoff M n W (k.1 + 1) : ℝ) ^ 3 ≤
          M.ratio := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_massError_zero M hdelta W Cmass k).eventually
      (eventually_le_nhds M.ratio_pos)
  have hFirstMain : ∀ᶠ n : ℕ in atTop,
      lowFirstContinuum M n W ≤ 3 * delta / 2 := by
    have hLimit : delta < 3 * delta / 2 := by linarith
    exact (tendsto_lowFirstContinuum M hdelta W).eventually
      (eventually_le_nhds hLimit)
  have hFirstError : ∀ᶠ n : ℕ in atTop,
      (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
        Cfirst / (2 * Real.log (W : ℝ) ^ 2)) / Real.log (y n) ≤
          delta / 2 := by
    exact (tendsto_lowFirstError_zero Cfirst W).eventually
      (eventually_le_nhds (by linarith : (0 : ℝ) < delta / 2))
  have hSecondLower : ∀ᶠ n : ℕ in atTop,
      5 * delta ^ 2 / 12 ≤ lowSecondContinuum M n W := by
    have hStrict : 5 * delta ^ 2 / 12 < delta ^ 2 / 2 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_ge_nhds hStrict)
  have hSecondUpper : ∀ᶠ n : ℕ in atTop,
      lowSecondContinuum M n W ≤ 11 * delta ^ 2 / 12 := by
    have hStrict : delta ^ 2 / 2 < 11 * delta ^ 2 / 12 := by
      nlinarith [sq_pos_of_pos hdelta]
    exact (tendsto_lowSecondContinuum M hdelta W).eventually
      (eventually_le_nhds hStrict)
  have hSecondError : ∀ᶠ n : ℕ in atTop,
      3 * Csecond / (Real.log (y n) ^ 2 * Real.log (W : ℝ)) ≤
        delta ^ 2 / 12 := by
    have hStrict : (0 : ℝ) < delta ^ 2 / 12 := by positivity
    exact (tendsto_lowSecondError_zero Csecond hW).eventually
      (eventually_le_nhds hStrict)
  have hLowMass : ∀ᶠ n : ℕ in atTop,
      48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
        Real.log (Real.log (fullCutoff M n W 1 : ℝ)) -
          Real.log (Real.log (W : ℝ)) :=
    (tendsto_lowHarmonicMain_atTop M hdelta W).eventually
      (eventually_ge_atTop
        (48 + 5 * Cmass / Real.log (W : ℝ) ^ 3))
  filter_upwards [eventually_gt_atTop 1, hPositiveMain, hPositiveError,
    hFirstMain, hFirstError, hSecondLower, hSecondUpper, hSecondError,
    hLowMass] with n hn hPM hPE hFM hFE hSL hSU hSE hLM
  exact ⟨hn, hPM, hPE, hFM, hFE, hSL, hSU, hSE, hLM⟩

variable {n W : ℕ}
  (P : Partition n W (Fin (M.cellCount + 1)))
  (E : IntervalCertificate P)
  (hLower : ∀ j, E.lower j = fullCutoff M n W j.1)
  (hUpper : ∀ j, E.upper j = fullCutoff M n W (j.1 + 1))

include E hLower hUpper

/-- Deterministic PNT assembly.  The three quadrature estimates are stated
with constants and thresholds selected before `n`, the partition, and its
endpoints. -/
theorem momentReady_of_endpointMomentBounds
    {Cmass Cfirst Csecond : ℝ} {Xmass Xfirst Xsecond : ℕ}
    (hW8 : 8 ≤ W)
    (hXmass : Xmass ≤ W) (hXfirst : Xfirst ≤ W)
    (hXsecond : Xsecond ≤ W)
    (hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3)
    (hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
        PrimeSums.fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2))
    (hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)))
    (B : EndpointMomentBounds M n W Cmass Cfirst Csecond) :
    MomentReady M P := by
  have hW2 : 2 ≤ W := hW8.trans' (by omega)
  have hy : 1 < y n := y_gt_one B.n_gt_one
  have hlogy : 0 < Real.log (y n) := Real.log_pos hy
  have hPositiveMass (k : Fin M.cellCount) :
      P.mass k.succ ≤ 3 * M.ratio := by
    have hAThreshold : Xmass ≤ E.lower k.succ :=
      hXmass.trans (E.cutoff_le_lower k.succ)
    have hQuad := hMass (E.lower k.succ) (E.upper k.succ)
      hAThreshold (E.lower_le_upper k.succ)
    have hA2 : 2 ≤ E.lower k.succ :=
      hW2.trans (E.cutoff_le_lower k.succ)
    have hMainEq :
        Real.log (Real.log (E.upper k.succ : ℝ)) -
            Real.log (Real.log (E.lower k.succ : ℝ)) =
          positiveContinuumMass M n W k := by
      rw [hLower k.succ, hUpper k.succ]
      have hCoord := log_logCoordinate_sub hy hA2
        (E.lower_le_upper k.succ)
      rw [hLower k.succ, hUpper k.succ] at hCoord
      symm
      exact hCoord
    have hMassError :
        |P.mass k.succ - positiveContinuumMass M n W k| ≤ M.ratio := by
      rw [E.mass_eq_fullReciprocalSum_sub, ← hMainEq]
      exact hQuad.trans (by
        rw [hLower k.succ]
        exact B.positiveMassError k)
    have hOneSide :
        P.mass k.succ - positiveContinuumMass M n W k ≤ M.ratio :=
      (le_abs_self _).trans hMassError
    linarith [B.positiveMain k]
  have hLowFirst : P.mass 0 * P.center 0 ≤ 2 * delta := by
    have hLowerZero : E.lower 0 = W := by
      simpa only [Fin.val_zero, fullCutoff_zero] using hLower 0
    have hAThreshold : Xfirst ≤ E.lower 0 := by
      rw [hLowerZero]
      exact hXfirst
    have hRaw := hFirst (E.lower 0) (E.upper 0) hAThreshold
      (E.lower_le_upper 0)
    have hRawW :
        |PrimeSums.fullLogReciprocalSum (E.upper 0) -
          PrimeSums.fullLogReciprocalSum (E.lower 0) -
          (Real.log (E.upper 0 : ℝ) -
            Real.log (E.lower 0 : ℝ))| ≤
          2 * Cfirst / Real.log (W : ℝ) ^ 3 +
            Cfirst / (2 * Real.log (W : ℝ) ^ 2) := by
      calc
        _ ≤ 2 * Cfirst / Real.log (E.lower 0 : ℝ) ^ 3 +
              Cfirst / (2 * Real.log (E.lower 0 : ℝ) ^ 2) := hRaw
        _ = _ := by rw [hLowerZero]
    have hNorm :
        |(PrimeSums.fullLogReciprocalSum (E.upper 0) -
              PrimeSums.fullLogReciprocalSum (E.lower 0)) /
              Real.log (y n) -
            (Real.log (E.upper 0 : ℝ) -
              Real.log (E.lower 0 : ℝ)) / Real.log (y n)| ≤
          (2 * Cfirst / Real.log (W : ℝ) ^ 3 +
            Cfirst / (2 * Real.log (W : ℝ) ^ 2)) /
              Real.log (y n) := by
      rw [← sub_div, abs_div, abs_of_pos hlogy]
      exact div_le_div_of_nonneg_right hRawW hlogy.le
    have hMainEq :
        (Real.log (E.upper 0 : ℝ) -
            Real.log (E.lower 0 : ℝ)) / Real.log (y n) =
          lowFirstContinuum M n W := by
      rw [← logCoordinate_sub hy, hLower 0, hUpper 0]
      rfl
    have hActualError :
        |P.mass 0 * P.center 0 - lowFirstContinuum M n W| ≤
          delta / 2 := by
      rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub, ← hMainEq]
      exact hNorm.trans B.lowFirstError
    have hOneSide := (le_abs_self
      (P.mass 0 * P.center 0 - lowFirstContinuum M n W)).trans
        hActualError
    linarith [B.lowFirstMain]
  have hLowSecondError :
      |P.bandSecondMoment 0 - lowSecondContinuum M n W| ≤
        delta ^ 2 / 12 := by
    have hLowerZero : E.lower 0 = W := by
      simpa only [Fin.val_zero, fullCutoff_zero] using hLower 0
    have hAThreshold : Xsecond ≤ E.lower 0 := by
      rw [hLowerZero]
      exact hXsecond
    have hRaw := hSecond (y n) hy (E.lower 0) (E.upper 0)
      hAThreshold (E.lower_le_upper 0)
    rw [P.bandSecondMoment_eq_fullWeightedReciprocalSum_sub E]
    have hMainEq :
        (realLogCoordinate (y n) (E.upper 0 : ℝ) ^ 2 -
            realLogCoordinate (y n) (E.lower 0 : ℝ) ^ 2) / 2 =
          lowSecondContinuum M n W := by
      rw [hLower 0, hUpper 0]
      rfl
    rw [← hMainEq]
    exact hRaw.trans (by
      rw [hLowerZero]
      exact B.lowSecondError)
  have hLowSecondLower : delta ^ 2 / 3 ≤ P.bandSecondMoment 0 := by
    have hLowerSide := (neg_le_neg hLowSecondError).trans (neg_abs_le
      (P.bandSecondMoment 0 - lowSecondContinuum M n W))
    nlinarith [B.lowSecondMainLower]
  have hLowSecondUpper : P.bandSecondMoment 0 ≤ delta ^ 2 := by
    have hUpperSide := (le_abs_self
      (P.bandSecondMoment 0 - lowSecondContinuum M n W)).trans
        hLowSecondError
    nlinarith [B.lowSecondMainUpper]
  have hLowMass : 48 ≤ P.mass 0 := by
    have hLowerZero : E.lower 0 = W := by
      simpa only [Fin.val_zero, fullCutoff_zero] using hLower 0
    have hAThreshold : Xmass ≤ E.lower 0 := by
      rw [hLowerZero]
      exact hXmass
    have hRaw := hMass (E.lower 0) (E.upper 0) hAThreshold
      (E.lower_le_upper 0)
    have hMassError :
        |P.mass 0 -
          (Real.log (Real.log (E.upper 0 : ℝ)) -
            Real.log (Real.log (E.lower 0 : ℝ)))| ≤
          5 * Cmass / Real.log (W : ℝ) ^ 3 := by
      rw [E.mass_eq_fullReciprocalSum_sub]
      exact hRaw.trans_eq (by rw [hLowerZero])
    have hLowerSide := (neg_le_neg hMassError).trans (neg_abs_le
      (P.mass 0 - (Real.log (Real.log (E.upper 0 : ℝ)) -
        Real.log (Real.log (E.lower 0 : ℝ)))))
    have hUpperZero : E.upper 0 = fullCutoff M n W 1 := by
      simpa only [Fin.val_zero, Nat.zero_add] using hUpper 0
    have hMainBound :
        48 + 5 * Cmass / Real.log (W : ℝ) ^ 3 ≤
          Real.log (Real.log (E.upper 0 : ℝ)) -
            Real.log (Real.log (E.lower 0 : ℝ)) := by
      rw [hLowerZero, hUpperZero]
      exact B.lowMassMain
    linarith
  exact ⟨hPositiveMass, hLowFirst, hLowSecondLower,
    hLowSecondUpper, hLowMass⟩

/-- The actual prime-deviation coefficient is uniformly of size at most
`w = delta + ratio`; this is the pointwise input to the compensated-score
regression ledger. -/
theorem actual_deviation_sup_le_scale
    (hdelta : 0 < delta) (hn : 1 < n)
    (p : BandPrime n W) :
    |P.deviation p| ≤ delta + M.ratio := by
  let motive := fun j : Fin (M.cellCount + 1) ↦
    P.band p = j → |P.deviation p| ≤ delta + M.ratio
  apply (Fin.cases (motive := motive) ?_ ?_
    (P.band p)) rfl
  · intro hpBand
    have hpFiber : p ∈ P.data.fiber (0 : Fin (M.cellCount + 1)) :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mpr hpBand
    have hdev := P.abs_deviation_le_width_of_coord_bounds 0
      (low_coord_bounds M P E hUpper hn) p hpFiber
    nlinarith [M.ratio_pos]
  · intro k hpBand
    have hpFiber : p ∈ P.data.fiber k.succ :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mpr hpBand
    have hdev := P.abs_deviation_le_width_of_coord_bounds k.succ
      (positive_coord_bounds M P E hLower hUpper hn k) p hpFiber
    rw [show M.upper k - M.lower k = M.width k by rfl] at hdev
    have hw := M.width_le_ratio hdelta k
    nlinarith

omit E hLower hUpper in
/-- The scale-normalized form consumed by the relative-row and regression
estimates in Lemma 8.6. -/
theorem relative_row_inputs_of_actual_moment_bounds
    (hdelta : 0 < delta)
    (hL1 : P.totalL1 ≤ 7 * (delta + M.ratio))
    (hVarLower : (delta + M.ratio) ^ 2 / 16 ≤ P.variance)
    (hVarUpper : P.variance ≤ 4 * (delta + M.ratio) ^ 2) :
    P.totalL1 / (delta + M.ratio) ≤ 7 ∧
      (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
      P.variance / (delta + M.ratio) ^ 2 ≤ 4 := by
  have hw : 0 < delta + M.ratio := add_pos hdelta M.ratio_pos
  have hwSq : 0 < (delta + M.ratio) ^ 2 := sq_pos_of_pos hw
  have hVar : 0 < P.variance :=
    (div_pos hwSq (by norm_num : (0 : ℝ) < 16)).trans_le hVarLower
  constructor
  · rw [div_le_iff₀ hw]
    linarith
  constructor
  · rw [div_le_iff₀ hVar]
    nlinarith
  · rw [div_le_iff₀ hwSq]
    exact hVarUpper

omit E hLower hUpper in
/-- Unconditional actual-prime mesh theorem.  The PNT constants and their
thresholds are selected first.  Every larger fixed cutoff then works for all
sufficiently large `n`, and the conclusion includes both the raw and the
scale-normalized bounds used in Lemma 8.6. -/
theorem exists_cutoff_eventually_actual_moment_bounds
    (hdelta : 0 < delta) (hratioDelta : M.ratio ≤ delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ P : Partition n W (Fin (M.cellCount + 1)),
          ∃ E : IntervalCertificate P,
            (∀ j, E.lower j = fullCutoff M n W j.1) ∧
            (∀ j, E.upper j = fullCutoff M n W (j.1 + 1)) ∧
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            (delta + M.ratio) ^ 2 / 16 ≤ P.variance ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 ∧
            P.totalL1 / (delta + M.ratio) ≤ 7 ∧
            (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
            P.variance / (delta + M.ratio) ^ 2 ≤ 4 := by
  obtain ⟨Cmass, hCmass, Xmass, hMass⟩ :=
    PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound
  obtain ⟨Cfirst, hCfirst, Xfirst, hFirst⟩ :=
    MovingLowMomentQuadrature.exists_fullLogReciprocalSum_interval_uniform_error_bound
  obtain ⟨Csecond, hCsecond, Xsecond, hSecond⟩ :=
    PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound
  let W₀ := max 8 (max Xmass (max Xfirst Xsecond))
  refine ⟨W₀, ?_⟩
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint := eventually_endpointMomentBounds M hdelta W
    Cmass Cfirst Csecond (by omega : 1 < W)
  have hPartition := eventually_exists_partition_and_certificate M
    hdelta hWne
  filter_upwards [hEndpoint, hPartition] with n B hExist
  obtain ⟨P, E, hLower, hUpper⟩ := hExist
  have hReady := momentReady_of_endpointMomentBounds M P E hLower hUpper
    hW8 hXmass hXfirst hXsecond hMass hFirst hSecond B
  obtain ⟨hL1, hVarLower, hVarUpper⟩ :=
    actual_moment_bounds_of_ready M P E hLower hUpper hdelta
      hratioDelta B.n_gt_one hReady
  obtain ⟨hRelL1, hRelInv, hRelVar⟩ :=
    relative_row_inputs_of_actual_moment_bounds M P hdelta hL1
      hVarLower hVarUpper
  have hSup := actual_deviation_sup_le_scale M P E hLower hUpper
    hdelta B.n_gt_one
  exact ⟨P, E, hLower, hUpper, hSup, hL1, hVarLower, hVarUpper,
    hRelL1, hRelInv, hRelVar⟩

omit E hLower hUpper in
/-- Fully bundled existence statement, including construction of the
regular relative mesh itself. -/
theorem exists_regular_mesh_and_eventually_actual_moment_bounds
    (hdelta : 0 < delta) (hdeltaOne : delta < 1) :
    ∃ M : Mesh delta delta, ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ P : Partition n W (Fin (M.cellCount + 1)),
          ∃ E : IntervalCertificate P,
            (∀ j, E.lower j = fullCutoff M n W j.1) ∧
            (∀ j, E.upper j = fullCutoff M n W (j.1 + 1)) ∧
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            (delta + M.ratio) ^ 2 / 16 ≤ P.variance ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 ∧
            P.totalL1 / (delta + M.ratio) ≤ 7 ∧
            (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
            P.variance / (delta + M.ratio) ^ 2 ≤ 4 := by
  obtain ⟨M⟩ := RegularRelativeMesh.exists_mesh hdelta hdeltaOne hdelta
  obtain ⟨W₀, hW₀⟩ := exists_cutoff_eventually_actual_moment_bounds M hdelta
    M.ratio_le_eta
  exact ⟨M, W₀, hW₀⟩

end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs
