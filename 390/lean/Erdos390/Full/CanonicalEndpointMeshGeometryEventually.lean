import Erdos390.Full.RegularMeshActualMomentBoundsEventually
import Erdos390.Full.CanonicalEndpointTwoTailCertificate

/-!
# Eventual geometry of the literal canonical endpoint mesh

The first endpoint is the fixed cutoff `W` and the last is `floor y`.
This file proves, rather than assumes, that the two omitted tails vanish and
that every actual floored cell inherits any strict upper bound satisfied by
its ideal regular-mesh length.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Logarithmic coordinate of one literal natural cutoff, for a general
regular mesh whose two parameters need not coincide. -/
def actualCutoffCoordinate (n W r : ℕ) : ℝ :=
  realLogCoordinate (y n) (fullCutoff M n W r : ℝ)

theorem tendsto_low_actualCoordinateLength
    (hdelta : 0 < delta) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W 1 - actualCutoffCoordinate M n W 0)
      atTop (nhds delta) := by
  have hUpper : Tendsto (fun n : ℕ ↦ actualCutoffCoordinate M n W 1)
      atTop (nhds delta) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ, M.endpoint_zero] using
      tendsto_floor_scalePoint_coordinate hdelta
  have hLower := tendsto_fixed_cutoffCoordinate_zero W
  have hLower' : Tendsto
      (fun n : ℕ ↦ actualCutoffCoordinate M n W 0)
      atTop (nhds 0) := by
    simpa only [actualCutoffCoordinate, fullCutoff_zero] using hLower
  simpa only [sub_zero] using hUpper.sub hLower'

theorem tendsto_positive_actualCoordinateLength
    (hdelta : 0 < delta) (W : ℕ) (k : Fin M.cellCount) :
    Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 2) -
      actualCutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.width k)) := by
  have hUpper : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 2))
      atTop (nhds (M.upper k)) := by
    have hpos : 0 < M.upper k :=
      (M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k)
    simpa only [actualCutoffCoordinate,
      show k.1 + 2 = (k.1 + 1) + 1 by omega,
      fullCutoff_succ, RegularRelativeMesh.Mesh.upper] using
        tendsto_floor_scalePoint_coordinate hpos
  have hLower : Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (k.1 + 1))
      atTop (nhds (M.lower k)) := by
    simpa only [actualCutoffCoordinate, fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using
        tendsto_floor_scalePoint_coordinate (M.lower_pos hdelta k)
  simpa only [RegularRelativeMesh.Mesh.width] using hUpper.sub hLower

/-- If the ideal low cell and every ideal positive cell have length
strictly below `rho`, then all literal floored cells eventually do too,
simultaneously. -/
theorem eventually_all_actualCoordinateLengths_lt
    (hdelta : 0 < delta) {rho : ℝ}
    (hLow : delta < rho)
    (hPositive : ∀ k : Fin M.cellCount, M.width k < rho)
    (W : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : Fin (M.cellCount + 1),
      actualCutoffCoordinate M n W (j.1 + 1) -
        actualCutoffCoordinate M n W j.1 < rho := by
  have hLowEvent : ∀ᶠ n : ℕ in atTop,
      actualCutoffCoordinate M n W 1 - actualCutoffCoordinate M n W 0 < rho :=
    (tendsto_low_actualCoordinateLength M hdelta W).eventually
      (eventually_lt_nhds hLow)
  have hPositiveEvent : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        actualCutoffCoordinate M n W (k.1 + 2) -
          actualCutoffCoordinate M n W (k.1 + 1) < rho := by
    rw [Filter.eventually_all]
    intro k
    exact (tendsto_positive_actualCoordinateLength M hdelta W k).eventually
      (eventually_lt_nhds (hPositive k))
  filter_upwards [hLowEvent, hPositiveEvent] with n hnLow hnPositive
  intro j
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simpa using hnLow
  · simpa using hnPositive k

theorem tendsto_canonical_upperEnd_one (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      actualCutoffCoordinate M n W (M.cellCount + 1))
      atTop (nhds 1) := by
  have hT := tendsto_floor_scalePoint_coordinate (t := (1 : ℝ)) (by norm_num)
  apply hT.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simp only [actualCutoffCoordinate, fullCutoff_last M hn, yNat, scalePoint,
    one_mul, Real.exp_log (Scale.y_pos hn)]

/-- Both literal endpoint omissions tend to zero. -/
theorem eventually_canonical_twoTails_lt
    (W : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    ∀ᶠ n : ℕ in atTop,
      actualCutoffCoordinate M n W 0 < beta ∧
        1 - actualCutoffCoordinate M n W (M.cellCount + 1) < beta := by
  have hBase : Tendsto (fun n : ℕ ↦ actualCutoffCoordinate M n W 0)
      atTop (nhds 0) := by
    have h := tendsto_fixed_cutoffCoordinate_zero W
    simpa only [actualCutoffCoordinate, fullCutoff_zero] using h
  have hTop := tendsto_canonical_upperEnd_one M W
  have hTopTail : Tendsto (fun n : ℕ ↦
      1 - actualCutoffCoordinate M n W (M.cellCount + 1))
      atTop (nhds 0) := by
    have hOne : Tendsto (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [sub_self] using hOne.sub hTop
  exact (hBase.eventually (eventually_lt_nhds hbeta)).and
    (hTopTail.eventually (eventually_lt_nhds hbeta))

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
