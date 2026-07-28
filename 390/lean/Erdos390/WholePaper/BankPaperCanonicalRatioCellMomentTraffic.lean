import Erdos390.WholePaper.BankPaperCanonicalRatioCellTraffic
import Erdos390.Full.RegularMeshActualMomentBoundsEventually

/-!
# Moment collapse of the canonical ratio-cell traffic

The endpoint-by-endpoint Mertens envelope is useful for pointwise ports,
but it is deliberately too wasteful for the sum over all cell cuts: its
uniform error is repeated once at every cut.  For total traffic one first
interchanges the two finite sums.  A vertex in cell `i` occurs in exactly
`i` strict tails, so the complete tail census is the first moment of the
literal cell index.

For the canonical multiplicative cells that index is at most

`(log y / log rho) * (t_p - t_lower)`.

The arithmetic moment bounds already proved for the canonical regular
mesh then give the paper-sized factor `delta + ratio`.  The only loss from
the natural floors is the explicit quantity `log 2 / log y`.

No new asymptotic or distribution hypothesis occurs in this file.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## The finite cut/tail interchange -/

/-- Summing all strict pointwise tails counts the upper bound at a vertex
exactly once for every cut strictly to the left of its cell. -/
theorem tangentRatioCell_sum_tailPointwiseUpper_eq_indexMoment
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v)) :
    (∑ band : Band,
      ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut) =
      ∑ v : V, (cellIndex v : Real) * pointwiseUpper v := by
  classical
  calc
    (∑ band : Band,
        ∑ cut ∈ Finset.range (lastCell band),
          tangentRatioCellTailPointwiseUpper
            pointwiseUpper bandOf cellIndex band cut) =
        ∑ band : Band, ∑ v : V,
          if bandOf v = band then
            (cellIndex v : Real) * pointwiseUpper v
          else 0 := by
      apply Finset.sum_congr rfl
      intro band _hband
      unfold tangentRatioCellTailPointwiseUpper
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hvBand : bandOf v = band
      · simp only [hvBand, true_and]
        have hfilter :
            (Finset.range (lastCell band)).filter
                (fun cut => cut < cellIndex v) =
              Finset.range (cellIndex v) := by
          ext cut
          simp only [Finset.mem_filter, Finset.mem_range]
          constructor
          · exact fun h => h.2
          · intro hcut
            exact ⟨hcut.trans_le (by simpa only [hvBand] using hindex v),
              hcut⟩
        rw [← Finset.sum_filter, hfilter]
        simp
      · simp [hvBand]
    _ = ∑ v : V, (cellIndex v : Real) * pointwiseUpper v := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Fintype.sum_eq_single (bandOf v)]
      · simp
      · intro band hband
        have hne : bandOf v ≠ band := Ne.symm hband
        simp [hne]

/-! ## Logarithmic control of the concrete cell index -/

/-- The merged canonical cell index is bounded by the logarithmic distance
from the actual natural lower endpoint of its exponent band. -/
theorem bankPaperCanonical_ratioCellIndex_le_logGap_div_logRho
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
      (Real.log (bankPaperCanonicalTangentPrimeLabel p : Real) -
          Real.log (bankPaperCanonicalExponentBandLower M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) :
              Real)) /
        Real.log rho := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
  have hrawReal : (lower : Real) * rho ^ raw < (p.1 : Real) := by
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, band] using
      tangentMultiplicativeRawCell_real_lower_lt
        hlower hrho hpLower
  have hlowerReal : (0 : Real) < lower := by exact_mod_cast hlower
  have hpReal : (0 : Real) < p.1 := by
    exact_mod_cast (bankPaperCanonicalTangentPrimeLabel_prime p).pos
  have hrhoPos : 0 < rho := by linarith
  have hproductPos : 0 < (lower : Real) * rho ^ raw :=
    mul_pos hlowerReal (pow_pos hrhoPos raw)
  have hlogRaw := Real.strictMonoOn_log
    (show (lower : Real) * rho ^ raw ∈ Set.Ioi 0 from hproductPos)
    (show (p.1 : Real) ∈ Set.Ioi 0 from hpReal) hrawReal
  have hlogIdentity :
      Real.log ((lower : Real) * rho ^ raw) =
        Real.log (lower : Real) + (raw : Real) * Real.log rho := by
    rw [Real.log_mul hlowerReal.ne' (pow_ne_zero raw hrhoPos.ne'),
      Real.log_pow]
  rw [hlogIdentity] at hlogRaw
  have hmerged :
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <= raw := by
    unfold bankPaperCanonicalRatioCellIndex
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hlogRho : 0 < Real.log rho := Real.log_pos hrho
  apply (le_div_iff₀ hlogRho).2
  have hmergedReal :
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
        (raw : Real) := by exact_mod_cast hmerged
  change
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
        Real.log rho <=
      Real.log (p.1 : Real) - Real.log (lower : Real)
  calc
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
          Real.log rho <=
        (raw : Real) * Real.log rho :=
      mul_le_mul_of_nonneg_right hmergedReal hlogRho.le
    _ <= Real.log (p.1 : Real) - Real.log (lower : Real) := by
      linarith

/-- Coordinate form of the preceding bound.  This is the exact bridge
from the ratio-cell census to the canonical arithmetic moments. -/
theorem bankPaperCanonical_ratioCellIndex_le_coordinateGap
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
      (Real.log (y n) / Real.log rho) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p).1) := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hraw := bankPaperCanonical_ratioCellIndex_le_logGap_div_logRho
    M hdelta hn hW S hrho p
  calc
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) <=
        (Real.log (bankPaperCanonicalTangentPrimeLabel p : Real) -
            Real.log (bankPaperCanonicalExponentBandLower M n W
              (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) :
                Real)) /
          Real.log rho := hraw
    _ = (Real.log (y n) / Real.log rho) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p).1) := by
      unfold tPrime RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
        KernelPrimeQuadrature.realLogCoordinate
        bankPaperCanonicalExponentBandLower
        bankPaperCanonicalTangentPrimeLabel
      field_simp [hlogy.ne', hlogrho.ne']

/-! ## The exact shifted-coordinate moment -/

/-- The canonical arithmetic first moment measured from the actual natural
lower endpoint in each exponent band. -/
def bankPaperCanonicalRatioCellCoordinateMoment
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) : Real :=
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  ∑ band : BankPaperCanonicalExponentBand M,
    P.mass band *
      (P.center band -
        RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1)

/-- On one arithmetic fiber, the shifted-coordinate sum is exactly mass
times the shifted arithmetic center. -/
theorem bankPaperCanonical_fiber_shiftedCoordinate_eq
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
    (∑ p ∈ P.data.fiber band,
      (1 / (p.1 : Real)) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1)) =
      P.mass band *
        (P.center band -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1) := by
  dsimp only
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let lowerCoord :=
    RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1
  have hfirst :
      (∑ p ∈ P.data.fiber band,
        (1 / (p.1 : Real)) * tPrime n p.1) =
        P.mass band * P.center band := by
    change (∑ p ∈ P.data.fiber band,
        (1 / (p.1 : Real)) * tPrime n p.1) =
      P.data.mass band *
        ((∑ p ∈ P.data.fiber band,
          (1 / (p.1 : Real)) * tPrime n p.1) / P.data.mass band)
    field_simp [ne_of_gt (P.data.mass_pos band)]
  have hmass :
      (∑ p ∈ P.data.fiber band, 1 / (p.1 : Real)) =
        P.mass band := rfl
  calc
    (∑ p ∈ P.data.fiber band,
        (1 / (p.1 : Real)) * (tPrime n p.1 - lowerCoord)) =
        (∑ p ∈ P.data.fiber band,
          (1 / (p.1 : Real)) * tPrime n p.1) -
        lowerCoord *
          (∑ p ∈ P.data.fiber band, 1 / (p.1 : Real)) := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ = P.mass band * (P.center band - lowerCoord) := by
      rw [hfirst, hmass]
      ring

/-- Reindexing the preceding fiber identities gives the complete shifted
coordinate moment over the literal canonical prime band. -/
theorem bankPaperCanonical_sum_shiftedCoordinate_eq_coordinateMoment
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      (1 / (p.1 : Real)) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S p).1)) =
      bankPaperCanonicalRatioCellCoordinateMoment
        M hdelta hn hW S := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  rw [← Finset.sum_fiberwise Finset.univ P.band
    (fun p : BankPaperCanonicalTangentPrime n W =>
      (1 / (p.1 : Real)) *
        (tPrime n p.1 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
            (bankPaperCanonicalExponentBandOf
              M hdelta hn hW S p).1))]
  unfold bankPaperCanonicalRatioCellCoordinateMoment
  dsimp only
  apply Finset.sum_congr rfl
  intro band _hband
  calc
    (∑ p ∈ Finset.univ with P.band p = band,
        (1 / (p.1 : Real)) *
          (tPrime n p.1 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
              (P.band p).1)) =
        ∑ p ∈ P.data.fiber band,
          (1 / (p.1 : Real)) *
            (tPrime n p.1 -
              RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpBand : P.band p = band := (Finset.mem_filter.mp hp).2
      rw [hpBand]
    _ = P.mass band *
        (P.center band -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W band.1) := by
      simpa only [P] using
        bankPaperCanonical_fiber_shiftedCoordinate_eq
          M hdelta hn hW S band

/-! ## Canonical-mesh bound for the shifted moment -/

/-- The only coordinate loss caused by flooring a positive mesh endpoint. -/
def bankPaperCanonicalRatioCellFloorLoss (n : Nat) : Real :=
  Real.log 2 / Real.log (y n)

/-- The positive-cell contribution is controlled by its actual width and
one copy of the explicit floor loss. -/
theorem bankPaperCanonical_positive_shiftedCoordinate_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (k : Fin M.cellCount)
    (hTwo : 2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn hW S)) :
    let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
    P.mass k.succ *
        (P.center k.succ -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W (k.1 + 1)) <=
      3 * M.ratio *
        (M.width k + bankPaperCanonicalRatioCellFloorLoss n) := by
  dsimp only
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  let loss := bankPaperCanonicalRatioCellFloorLoss n
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hloss : 0 <= loss := by
    unfold loss bankPaperCanonicalRatioCellFloorLoss
    exact div_nonneg (Real.log_nonneg (by norm_num)) hlogy.le
  have hlowerCoord :
      M.lower k - loss <=
        RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W (k.1 + 1) := by
    have hfloor := (floor_scalePoint_coordinate_bounds hn hTwo).1
    simpa only [loss, bankPaperCanonicalRatioCellFloorLoss,
      RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate,
      RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
      RegularRelativeMesh.Mesh.lower] using hfloor
  have hcoord :=
    RegularMeshPrimeCutoffs.Mesh.positive_coord_bounds
      M P E (fun _j => rfl) (fun _j => rfl) hn k
  have hwidthLoss : 0 <= M.width k + loss :=
    add_nonneg (M.width_pos hdelta k).le hloss
  change P.mass k.succ *
      (P.center k.succ -
        RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W k.succ.1) <=
    3 * M.ratio * (M.width k + bankPaperCanonicalRatioCellFloorLoss n)
  rw [← bankPaperCanonical_fiber_shiftedCoordinate_eq
    M hdelta hn hW S k.succ]
  calc
    (∑ p ∈ P.data.fiber k.succ,
        (1 / (p.1 : Real)) *
          (tPrime n p.1 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
              M n W (k.1 + 1))) <=
        ∑ p ∈ P.data.fiber k.succ,
          (1 / (p.1 : Real)) * (M.width k + loss) := by
      apply Finset.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hpUpper := (hcoord p hp).2
      unfold RegularRelativeMesh.Mesh.width
      linarith
    _ = P.mass k.succ * (M.width k + loss) := by
      change (∑ p ∈ P.data.fiber k.succ,
          (1 / (p.1 : Real)) * (M.width k + loss)) =
        (∑ p ∈ P.data.fiber k.succ, 1 / (p.1 : Real)) *
          (M.width k + loss)
      rw [Finset.sum_mul]
    _ <= 3 * M.ratio * (M.width k + loss) :=
      mul_le_mul_of_nonneg_right (R.positiveMass k) hwidthLoss

/-- The moving low cell is controlled by the already-proved first-moment
part of `MomentReady`; subtracting its nonnegative fixed-cutoff coordinate
can only decrease it. -/
theorem bankPaperCanonical_low_shiftedCoordinate_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S)) :
    let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn (by omega) S
    P.mass 0 *
        (P.center 0 -
          RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0) <=
      2 * delta := by
  dsimp only
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn (by omega : W ≠ 0) S
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hWlog : 0 <= Real.log (W : Real) :=
    Real.log_nonneg (by exact_mod_cast (show 1 <= W by omega))
  have hlowerCoord :
      0 <= RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0 := by
    unfold RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
      KernelPrimeQuadrature.realLogCoordinate
    rw [RegularMeshPrimeCutoffs.Mesh.fullCutoff_zero]
    exact div_nonneg hWlog hlogy.le
  have hmass : 0 <= P.mass (0 : BankPaperCanonicalExponentBand M) :=
    (P.data.mass_pos 0).le
  calc
    P.mass 0 *
          (P.center 0 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0) <=
        P.mass 0 * P.center 0 := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ hlowerCoord) hmass
    _ <= 2 * delta := R.lowFirst

/-- Complete canonical shifted-coordinate budget.  The low cell contributes
`2*delta`; the positive mesh contributes `3*ratio`, plus the displayed
finite floor loss. -/
theorem bankPaperCanonical_ratioCellCoordinateMoment_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S)) :
    bankPaperCanonicalRatioCellCoordinateMoment
        M hdelta hn (by omega) S <=
      2 * delta + 3 * M.ratio *
        (1 + (M.cellCount : Real) *
          bankPaperCanonicalRatioCellFloorLoss n) := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn (by omega : W ≠ 0) S
  let loss := bankPaperCanonicalRatioCellFloorLoss n
  have hloss : 0 <= loss := by
    unfold loss bankPaperCanonicalRatioCellFloorLoss
    have hlogy : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn))
    exact div_nonneg (Real.log_nonneg (by norm_num)) hlogy.le
  unfold bankPaperCanonicalRatioCellCoordinateMoment
  dsimp only
  rw [Fin.sum_univ_succ]
  calc
    P.mass 0 *
          (P.center 0 -
            RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W 0) +
        ∑ k : Fin M.cellCount,
          P.mass k.succ *
            (P.center k.succ -
              RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate
                M n W (k.1 + 1)) <=
        2 * delta +
          ∑ k : Fin M.cellCount,
            3 * M.ratio * (M.width k + loss) := by
      exact add_le_add
        (bankPaperCanonical_low_shiftedCoordinate_le
          M hdelta hn hWtwo S R)
        (Finset.sum_le_sum fun k _hk =>
          bankPaperCanonical_positive_shiftedCoordinate_le
            M hdelta hn (by omega) S k (hTwo k) R)
    _ = 2 * delta + 3 * M.ratio *
        (1 - delta + (M.cellCount : Real) * loss) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        M.sum_width_eq_one_sub_delta]
      simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    _ <= 2 * delta + 3 * M.ratio *
        (1 + (M.cellCount : Real) * loss) := by
      have hrho : 0 <= 3 * M.ratio :=
        mul_nonneg (by norm_num) M.ratio_pos.le
      gcongr
      linarith

/-! ## Moment majorants for the complete traffic ledger -/

/-- Exact arithmetic-moment majorant for the sum of the canonical cut
loads. -/
def bankPaperCanonicalRatioCellMomentCutMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n : Nat) (rho scale : Real) : Real :=
  scale * Real.log (y n) / Real.log rho *
    (2 * delta + 3 * M.ratio *
      (1 + (M.cellCount : Real) *
        bankPaperCanonicalRatioCellFloorLoss n))

/-- Total-traffic majorant obtained by using the global Mertens estimate
only once and the exact arithmetic moment for all cell cuts. -/
def bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  bankPaperCanonicalHarmonicResidualL1Majorant n W scale / 2 +
    2 * bankPaperCanonicalRatioCellMomentCutMajorant M n rho scale

/-- The exact cell-index moment is bounded by the canonical shifted
coordinate moment. -/
theorem bankPaperCanonical_ratioCellIndexMoment_le_coordinateMoment
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
        bankPaperCanonicalHarmonicPointwiseUpper scale p) <=
      scale * Real.log (y n) / Real.log rho *
        bankPaperCanonicalRatioCellCoordinateMoment
          M hdelta hn hW S := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  calc
    (∑ p : BankPaperCanonicalTangentPrime n W,
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p) <=
        ∑ p : BankPaperCanonicalTangentPrime n W,
          (scale * Real.log (y n) / Real.log rho) *
            ((1 / (p.1 : Real)) *
              (tPrime n p.1 -
                RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hW S p).1)) := by
      apply Finset.sum_le_sum
      intro p _hp
      have hpPos : (0 : Real) < p.1 := by
        exact_mod_cast (bankPaperCanonicalTangentPrimeLabel_prime p).pos
      have hidx := bankPaperCanonical_ratioCellIndex_le_coordinateGap
        M hdelta hn hW S hrho p
      unfold bankPaperCanonicalHarmonicPointwiseUpper
      calc
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p : Real) *
              (scale / (bankPaperCanonicalTangentPrimeLabel p : Real)) <=
            ((Real.log (y n) / Real.log rho) *
              (tPrime n p.1 -
                RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hW S p).1)) *
              (scale / (p.1 : Real)) :=
          mul_le_mul_of_nonneg_right hidx (div_nonneg hscale hpPos.le)
        _ = (scale * Real.log (y n) / Real.log rho) *
            ((1 / (p.1 : Real)) *
              (tPrime n p.1 -
                RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hW S p).1)) := by
          field_simp [hpPos.ne', hlogrho.ne']
    _ = (scale * Real.log (y n) / Real.log rho) *
        (∑ p : BankPaperCanonicalTangentPrime n W,
          (1 / (p.1 : Real)) *
            (tPrime n p.1 -
              RegularMeshPrimeCutoffs.Mesh.cutoffCoordinate M n W
                (bankPaperCanonicalExponentBandOf
                  M hdelta hn hW S p).1)) := by
      rw [Finset.mul_sum]
    _ = scale * Real.log (y n) / Real.log rho *
        bankPaperCanonicalRatioCellCoordinateMoment
          M hdelta hn hW S := by
      rw [bankPaperCanonical_sum_shiftedCoordinate_eq_coordinateMoment]

/-- Exact balance and the harmonic pointwise residual estimate bound the
complete cut ledger by the moment majorant, without repeating a Mertens
error at every cut. -/
theorem bankPaperCanonical_ratioCellCutTraffic_le_momentMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S p = band then residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentRatioCellCanonicalCutTraffic
        (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
        residual
        (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
        (bankPaperCanonicalRatioCellIndex
          M hdelta hn (by omega) S rho) <=
      bankPaperCanonicalRatioCellMomentCutMajorant M n rho scale := by
  let bandOf := bankPaperCanonicalExponentBandOf
    M hdelta hn (by omega : W ≠ 0) S
  let cellIndex := bankPaperCanonicalRatioCellIndex
    M hdelta hn (by omega : W ≠ 0) S rho
  let lastCell := bankPaperCanonicalLastRatioCell M
    (n := n) (W := W) rho
  have hindex : forall p : BankPaperCanonicalTangentPrime n W,
      cellIndex p <= lastCell (bandOf p) := by
    intro p
    exact bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn (by omega) S rho p
  have hprefix : forall band cut,
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
        tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          bandOf cellIndex band cut := by
    intro band cut
    exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
      residual (bankPaperCanonicalHarmonicPointwiseUpper scale)
      bandOf cellIndex hbalance hpointwise band cut
  have hcut := tangentRatioCellCanonicalCutTraffic_le_prefixUpper
    lastCell residual bandOf cellIndex
    (tangentRatioCellTailPointwiseUpper
      (bankPaperCanonicalHarmonicPointwiseUpper scale) bandOf cellIndex)
    hprefix
  have htail := tangentRatioCell_sum_tailPointwiseUpper_eq_indexMoment
    lastCell (bankPaperCanonicalHarmonicPointwiseUpper scale)
    bandOf cellIndex hindex
  have hmoment := bankPaperCanonical_ratioCellIndexMoment_le_coordinateMoment
    M hdelta hn (by omega) S hrho hscale
  have hcoordinate := bankPaperCanonical_ratioCellCoordinateMoment_le
    M hdelta hn hWtwo S hTwo R
  have hfactor : 0 <= scale * Real.log (y n) / Real.log rho := by
    have hlogy : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn))
    exact div_nonneg (mul_nonneg hscale hlogy.le)
      (Real.log_pos hrho).le
  calc
    tangentRatioCellCanonicalCutTraffic lastCell residual bandOf cellIndex <=
        ∑ band : BankPaperCanonicalExponentBand M,
          ∑ cut ∈ Finset.range (lastCell band),
            tangentRatioCellTailPointwiseUpper
              (bankPaperCanonicalHarmonicPointwiseUpper scale)
              bandOf cellIndex band cut := hcut
    _ = ∑ p : BankPaperCanonicalTangentPrime n W,
        (cellIndex p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p := htail
    _ <= scale * Real.log (y n) / Real.log rho *
        bankPaperCanonicalRatioCellCoordinateMoment
          M hdelta hn (by omega) S := by
      simpa only [bandOf, cellIndex] using hmoment
    _ <= scale * Real.log (y n) / Real.log rho *
        (2 * delta + 3 * M.ratio *
          (1 + (M.cellCount : Real) *
            bankPaperCanonicalRatioCellFloorLoss n)) :=
      mul_le_mul_of_nonneg_left hcoordinate hfactor
    _ = bankPaperCanonicalRatioCellMomentCutMajorant
        M n rho scale := rfl

/-- Complete finite total-traffic bound using one global Mertens estimate
and the exact ratio-cell moment collapse. -/
theorem bankPaperCanonical_ratioCellTotalTraffic_le_momentMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (R : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S p = band then residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
          residual
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex
            M hdelta hn (by omega) S rho)) <=
      bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
        M n W rho scale := by
  have hresidualEnvelope :
      (∑ p : BankPaperCanonicalTangentPrime n W, |residual p|) <=
        bankPaperCanonicalHarmonicResidualL1Envelope n W scale := by
    unfold bankPaperCanonicalHarmonicResidualL1Envelope
    exact Finset.sum_le_sum (fun p _hp => hpointwise p)
  have hresidualMajorant :=
    bankPaperCanonicalHarmonicResidualL1Envelope_le_majorant
      M hdelta hn (by omega) S hscale hMertens
  have hcut := bankPaperCanonical_ratioCellCutTraffic_le_momentMajorant
    M hdelta hn hWtwo S hrho hscale hTwo R residual hbalance hpointwise
  unfold tangentDistributedTotalTrafficLedger
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
  exact add_le_add
    (div_le_div_of_nonneg_right
      (hresidualEnvelope.trans hresidualMajorant) (by norm_num))
    (mul_le_mul_of_nonneg_left hcut (by norm_num))

/-! ## Paper-scale scalar reduction -/

/-- Fixed main-term traffic constant supplied by the moment collapse. -/
def bankPaperCanonicalRatioCellTrafficConstant (rho : Real) : Real :=
  6 / Real.log rho

/-- Every non-main contribution after the paper specialization
`scale = tangentConstant * N / log y`.  For fixed parameters this is an
explicit scalar tending to zero; no traffic quantity remains in it. -/
def bankPaperCanonicalRatioCellTrafficErrorCoefficient
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho tangentConstant : Real) : Real :=
  tangentConstant /
      (2 * Real.log (y n)) *
    (Real.log (Real.log (yNat n : Real)) -
        Real.log (Real.log (W : Real)) +
      5 * fullReciprocalSumUniformConstant /
        Real.log (W : Real) ^ 3) +
    6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
      (Real.log rho * Real.log (y n))

/-- The moment majorant at the paper scale has the required main/error
shape.  This is the smallest remaining scalar inequality for total traffic:
the first coefficient is fixed once `rho` is fixed, and every term in the
second coefficient contains `1 / log y`. -/
theorem bankPaperCanonical_ratioCellMomentTotalTrafficMajorant_paperScale
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} {rho tangentConstant N : Real}
    (hdelta : 0 < delta) (hn : 1 < n) (hWtwo : 2 <= W)
    (hrho : 1 < rho)
    (htangent : 0 <= tangentConstant) (hN : 0 <= N) :
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M n W rho
        (tangentConstant * N / Real.log (y n)) <=
      bankPaperCanonicalRatioCellTrafficConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hlogW : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hmain :
      2 * (tangentConstant * N / Real.log rho) *
          (2 * delta + 3 * M.ratio) <=
        (6 / Real.log rho) * tangentConstant * N *
          (delta + M.ratio) := by
    have hfactor : 0 <= tangentConstant * N / Real.log rho :=
      div_nonneg (mul_nonneg htangent hN) hlogrho.le
    have hfactorDelta :
        0 <= (tangentConstant * N / Real.log rho) * delta :=
      mul_nonneg hfactor hdelta.le
    ring_nf at hfactorDelta ⊢
    nlinarith
  calc
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M n W rho
        (tangentConstant * N / Real.log (y n)) =
      2 * (tangentConstant * N / Real.log rho) *
          (2 * delta + 3 * M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N := by
      unfold bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
        bankPaperCanonicalRatioCellMomentCutMajorant
        bankPaperCanonicalHarmonicResidualL1Majorant
        bankPaperCanonicalHarmonicTailMajorant
        bankPaperCanonicalRatioCellFloorLoss
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
      field_simp [hlogy.ne', hlogrho.ne', hlogW.ne']; ring
    _ <= (6 / Real.log rho) * tangentConstant * N *
          (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N :=
      add_le_add hmain le_rfl
    _ = bankPaperCanonicalRatioCellTrafficConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N := rfl

/-! ## Concrete geometry for the normalized pointwise port -/

/-- The natural start of the merged ratio cell containing `p`. -/
def bankPaperCanonicalRatioCellCurrentLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Nat :=
  tangentMultiplicativeRatioCutoff
    (bankPaperCanonicalExponentBandLower M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)) rho
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p)

/-- The current cell start remains beyond the fixed arithmetic cutoff. -/
theorem bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    W <= bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn hW S rho p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p
  exact (bankPaperCanonical_fixedCutoff_le_exponentBandLower
    M hdelta hn hW S band).trans (by
      have hmono := tangentMultiplicativeRatioCutoff_mono
        (lower := bankPaperCanonicalExponentBandLower M n W band)
        (rho := rho) hrho.le (Nat.zero_le cell)
      simpa only [bankPaperCanonicalRatioCellCurrentLower, band, cell,
        tangentMultiplicativeRatioCutoff_zero] using hmono)

/-- The start of the current merged cell lies strictly below its vertex. -/
theorem bankPaperCanonical_ratioCellCurrentLower_lt_label
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRatioCellCurrentLower M hdelta hn hW S rho p <
      bankPaperCanonicalTangentPrimeLabel p := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn hW S rho p
  let cell := bankPaperCanonicalRatioCellIndex
    M hdelta hn hW S rho p
  have hlower : 0 < lower :=
    bankPaperCanonicalExponentBandLower_pos M hdelta hn hW S band
  have hpLower : lower < p.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S p).1
  have hcellRaw : cell <= raw := by
    exact tangentMergedRatioCellIndex_le_raw _ _
  have hmono := tangentMultiplicativeRatioCutoff_mono
    (lower := lower) (rho := rho) hrho.le hcellRaw
  have hraw := tangentMultiplicativeRatioCutoff_rawCell_lt_label
    hlower hrho hpLower
  exact hmono.trans_lt (by
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, band]
      using hraw)

/-- Terminal merging can move a vertex by at most one raw cell.  Together
with the floor loss this gives the uniform ratio `p/A <= 2*rho^2` between
a vertex label and the start `A` used in its PNT denominator. -/
theorem bankPaperCanonical_label_le_two_mul_rho_sq_mul_currentLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) <=
      2 * rho ^ 2 *
        (bankPaperCanonicalRatioCellCurrentLower
          M hdelta hn (by omega) S rho p : Real) := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let raw := bankPaperCanonicalRawRatioCellIndex
    M hdelta hn (by omega : W ≠ 0) S rho p
  let cell := bankPaperCanonicalRatioCellIndex
    M hdelta hn (by omega : W ≠ 0) S rho p
  let A := tangentMultiplicativeRatioCutoff lower rho cell
  have hlower : 0 < lower :=
    bankPaperCanonicalExponentBandLower_pos
      M hdelta hn (by omega) S band
  have hlowerTwo : 2 <= lower :=
    hWtwo.trans (bankPaperCanonical_fixedCutoff_le_exponentBandLower
      M hdelta hn (by omega) S band)
  have hrhoPos : 0 < rho := by linarith
  have hrawLast : raw <= bankPaperCanonicalLastRawRatioCell M
      (n := n) (W := W) rho band := by
    simpa only [raw, band] using
      bankPaperCanonicalRawRatioCellIndex_le_lastRaw
        M hdelta hn (by omega) S rho hrho p
  have hrawCell : raw <= cell + 1 := by
    simpa only [cell, raw, band, bankPaperCanonicalRatioCellIndex] using
      raw_le_tangentMergedRatioCellIndex_add_one hrawLast
  have hpUpper : (p.1 : Real) <= (lower : Real) * rho ^ (raw + 1) := by
    simpa only [raw, lower, bankPaperCanonicalRawRatioCellIndex, band] using
      tangentMultiplicativeRawCell_real_upper
        hlower hrho (label := p.1)
  have hpow : rho ^ (raw + 1) <= rho ^ (cell + 2) :=
    pow_le_pow_right₀ hrho.le (by omega)
  have hxTwo : (2 : Real) <= (lower : Real) * rho ^ cell := by
    have hpowOne : (1 : Real) <= rho ^ cell := one_le_pow₀ hrho.le
    have hlowerReal : (2 : Real) <= lower := by exact_mod_cast hlowerTwo
    nlinarith [mul_le_mul_of_nonneg_left hpowOne
      (show (0 : Real) <= lower by positivity)]
  have hfloorLe : ((lower : Real) * rho ^ cell) / 2 <= (A : Real) := by
    have hxPos : 0 < (lower : Real) * rho ^ cell := by positivity
    have hfloorLt : (lower : Real) * rho ^ cell < (A : Real) + 1 := by
      simpa only [A, tangentMultiplicativeRatioCutoff] using
        Nat.lt_floor_add_one ((lower : Real) * rho ^ cell)
    linarith
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) <=
        (lower : Real) * rho ^ (raw + 1) := hpUpper
    _ <= (lower : Real) * rho ^ (cell + 2) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = ((lower : Real) * rho ^ cell) * rho ^ 2 := by
      rw [show cell + 2 = cell + 2 by rfl, pow_add]
      ring
    _ <= (2 * (A : Real)) * rho ^ 2 := by
      have hx : (lower : Real) * rho ^ cell <= 2 * (A : Real) := by
        linarith
      exact mul_le_mul_of_nonneg_right hx (sq_nonneg rho)
    _ = 2 * rho ^ 2 *
        (bankPaperCanonicalRatioCellCurrentLower
          M hdelta hn (by omega) S rho p : Real) := by
      simp only [bankPaperCanonicalRatioCellCurrentLower, A, lower, cell,
        band]
      ring

/-! ## Scalar Mertens cancellation in one PNT-normalized port -/

/-- Moving the lower endpoint to the left can only enlarge the explicit
Mertens tail majorant. -/
theorem bankPaperCanonicalHarmonicTailMajorant_mono_lower
    {scale : Real} (hscale : 0 <= scale)
    {A B Y : Nat} (hA : 2 <= A) (hAB : A <= B) (hBY : B <= Y) :
    bankPaperCanonicalHarmonicTailMajorant scale B Y <=
      bankPaperCanonicalHarmonicTailMajorant scale A Y := by
  have hB : 2 <= B := hA.trans hAB
  have hY : 2 <= Y := hB.trans hBY
  have hAR : (0 : Real) < A := by positivity
  have hBR : (0 : Real) < B := by positivity
  have hYR : (0 : Real) < Y := by positivity
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogB : 0 < Real.log (B : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  have hlogAB : Real.log (A : Real) <= Real.log (B : Real) :=
    Real.log_le_log hAR (by exact_mod_cast hAB)
  have hloglogAB :
      Real.log (Real.log (A : Real)) <=
        Real.log (Real.log (B : Real)) :=
    Real.log_le_log hlogA hlogAB
  have hpowAB : Real.log (A : Real) ^ 3 <=
      Real.log (B : Real) ^ 3 :=
    pow_le_pow_left₀ hlogA.le hlogAB 3
  have hconstant : 0 <=
      5 * fullReciprocalSumUniformConstant := by
    exact mul_nonneg (by norm_num)
      fullReciprocalSumUniformConstant_pos.le
  have herror :
      5 * fullReciprocalSumUniformConstant /
          Real.log (B : Real) ^ 3 <=
        5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hlogB 3) (pow_pos hlogA 3)).2
    exact mul_le_mul_of_nonneg_left hpowAB hconstant
  unfold bankPaperCanonicalHarmonicTailMajorant
  apply mul_le_mul_of_nonneg_left _ hscale
  exact add_le_add (sub_le_sub_left hloglogAB _) herror

/-- The logarithm in a harmonic tail cancels the logarithm in the PNT
denominator. -/
theorem bankPaperCanonical_log_mul_logLogGap_le_logGap
    {A Y : Nat} (hA : 2 <= A) (hAY : A <= Y) :
    Real.log (A : Real) *
        (Real.log (Real.log (Y : Real)) -
          Real.log (Real.log (A : Real))) <=
      Real.log (Y : Real) - Real.log (A : Real) := by
  have hY : 2 <= Y := hA.trans hAY
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogY : 0 < Real.log (Y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hratio : 0 < Real.log (Y : Real) / Real.log (A : Real) :=
    div_pos hlogY hlogA
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hidentity :
      Real.log (Real.log (Y : Real)) -
          Real.log (Real.log (A : Real)) =
        Real.log (Real.log (Y : Real) / Real.log (A : Real)) := by
    rw [Real.log_div hlogY.ne' hlogA.ne']
  rw [hidentity]
  calc
    Real.log (A : Real) *
          Real.log (Real.log (Y : Real) / Real.log (A : Real)) <=
        Real.log (A : Real) *
          (Real.log (Y : Real) / Real.log (A : Real) - 1) :=
      mul_le_mul_of_nonneg_left hlog hlogA.le
    _ = Real.log (Y : Real) - Real.log (A : Real) := by
      field_simp [hlogA.ne']

/-- After multiplying by the denominator logarithm, two incident Mertens
tails cost at most twice the ordinary logarithmic gap plus the square-log
error. -/
theorem bankPaperCanonical_logCurrentLower_mul_portNumerator_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (p : BankPaperCanonicalTangentPrime n W) :
    let A := bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn (by omega) S rho p
    let Y := bankPaperCanonicalExponentBandUpper M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
    Real.log (A : Real) *
        bankPaperCanonicalRatioCellPortNumeratorEnvelope
          M hdelta hn (by omega) S rho scale p <=
      2 * scale *
        (Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
  dsimp only
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
    (by omega : W ≠ 0) S rho p
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  let Y := bankPaperCanonicalExponentBandUpper M n W band
  have hWA : W <= A := by
    simpa only [A] using
      bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
        M hdelta hn (by omega) S hrho p
  have hA2 : 2 <= A := hWtwo.trans hWA
  have hAY : A <= Y := by
    have hAp := bankPaperCanonical_ratioCellCurrentLower_lt_label
      M hdelta hn (by omega) S hrho p
    have hpY :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn (by omega) S p).2
    simpa only [A, Y, band] using hAp.le.trans hpY
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  let baseMajorant := bankPaperCanonicalHarmonicTailMajorant scale A Y
  have htailCurrent :
      bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band cell <= baseMajorant := by
    let B := bankPaperCanonicalRatioCellTailLower M n W rho band cell
    have hAB : A <= B := by
      unfold A bankPaperCanonicalRatioCellCurrentLower B
        bankPaperCanonicalRatioCellTailLower
      apply le_min
      · exact tangentMultiplicativeRatioCutoff_mono
          (lower := bankPaperCanonicalExponentBandLower M n W band)
          (rho := rho) hrho.le (by omega)
      · exact hAY
    have hBY := bankPaperCanonicalRatioCellTailLower_le_upper
      M n W rho band cell
    exact bankPaperCanonicalHarmonicTailMajorant_mono_lower
      hscale hA2 hAB (by simpa only [B, Y,
        bankPaperCanonicalRatioCellTailUpper] using hBY)
  have htailPrevious :
      (if cell = 0 then 0
        else bankPaperCanonicalRatioCellTailMajorant
          M n W rho scale band (cell - 1)) <= baseMajorant := by
    by_cases hcell : cell = 0
    · simp [hcell]
      have hcurrentNonneg := bankPaperCanonicalRatioCellTailMajorant_nonneg
        M hdelta hn (by omega) S hrho hscale
        hMertens band cell
      exact hcurrentNonneg.trans htailCurrent
    · simp only [hcell, if_false]
      have hprevNext : cell - 1 + 1 = cell := by omega
      have htailLower :
          bankPaperCanonicalRatioCellTailLower M n W rho band (cell - 1) =
            A := by
        change min
          (tangentMultiplicativeRatioCutoff
            (bankPaperCanonicalExponentBandLower M n W band)
            rho (cell - 1 + 1))
          Y = A
        rw [hprevNext]
        exact Nat.min_eq_left hAY
      unfold bankPaperCanonicalRatioCellTailMajorant
      rw [htailLower]
      rfl
  have hnum :
      bankPaperCanonicalRatioCellPortNumeratorEnvelope
          M hdelta hn (by omega) S rho scale p <= 2 * baseMajorant := by
    unfold bankPaperCanonicalRatioCellPortNumeratorEnvelope
    simpa only [band, cell, two_mul] using
      add_le_add htailPrevious htailCurrent
  have hlogMain := bankPaperCanonical_log_mul_logLogGap_le_logGap hA2 hAY
  have hbaseIdentity :
      Real.log (A : Real) * baseMajorant =
        scale *
          (Real.log (A : Real) *
              (Real.log (Real.log (Y : Real)) -
                Real.log (Real.log (A : Real))) +
            5 * fullReciprocalSumUniformConstant /
              Real.log (A : Real) ^ 2) := by
    unfold baseMajorant bankPaperCanonicalHarmonicTailMajorant
    field_simp [hlogA.ne']
  calc
    Real.log (A : Real) *
          bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p <=
        Real.log (A : Real) * (2 * baseMajorant) :=
      mul_le_mul_of_nonneg_left hnum hlogA.le
    _ = 2 * (Real.log (A : Real) * baseMajorant) := by ring
    _ = 2 * scale *
        (Real.log (A : Real) *
            (Real.log (Real.log (Y : Real)) -
              Real.log (Real.log (A : Real))) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
      rw [hbaseIdentity]
      ring
    _ <= 2 * scale *
        (Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
      gcongr

/-- The PNT-normalized pointwise envelope after the two exact
cancellations: `p/A <= 2*rho^2` and
`log A * log(log Y/log A) <= log Y-log A`. -/
theorem bankPaperCanonical_weightedPNTEnvelope_le_logGap
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (p : BankPaperCanonicalTangentPrime n W) :
    let A := bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn (by omega) S rho p
    let Y := bankPaperCanonicalExponentBandUpper M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) <=
      (8 * rho ^ 2 / (rho - 1)) * scale *
        (Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by
  dsimp only
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  let Y := bankPaperCanonicalExponentBandUpper M n W band
  let numerator := bankPaperCanonicalRatioCellPortNumeratorEnvelope
    M hdelta hn (by omega : W ≠ 0) S rho scale p
  have hWA : W <= A := by
    simpa only [A] using
      bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
        M hdelta hn (by omega) S hrho p
  have hA2 : 2 <= A := hWtwo.trans hWA
  have hApos : (0 : Real) < A := by positivity
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hrhoGap : 0 < rho - 1 := sub_pos.mpr hrho
  have hlabel :=
    bankPaperCanonical_label_le_two_mul_rho_sq_mul_currentLower
      M hdelta hn hWtwo S hrho p
  have hcoefficient :
      2 * (bankPaperCanonicalTangentPrimeLabel p : Real) /
          ((rho - 1) * (A : Real)) <=
        4 * rho ^ 2 / (rho - 1) := by
    apply (div_le_div_iff₀
      (mul_pos hrhoGap hApos) hrhoGap).2
    have htwice := mul_le_mul_of_nonneg_left hlabel
      (show (0 : Real) <= 2 by norm_num)
    calc
      2 * (bankPaperCanonicalTangentPrimeLabel p : Real) * (rho - 1) <=
          (2 * (2 * rho ^ 2 * (A : Real))) * (rho - 1) :=
        mul_le_mul_of_nonneg_right htwice hrhoGap.le
      _ = 4 * rho ^ 2 * ((rho - 1) * (A : Real)) := by ring
  have hnumNonneg : 0 <= numerator := by
    unfold numerator bankPaperCanonicalRatioCellPortNumeratorEnvelope
    let cell := bankPaperCanonicalRatioCellIndex M hdelta hn
      (by omega : W ≠ 0) S rho p
    let pband := bankPaperCanonicalExponentBandOf M hdelta hn
      (by omega : W ≠ 0) S p
    by_cases hcell : cell = 0
    · simp only [cell, hcell, if_true, zero_add]
      exact bankPaperCanonicalRatioCellTailMajorant_nonneg
        M hdelta hn (by omega) S hrho hscale hMertens pband 0
    · simp only [cell, hcell, if_false]
      exact add_nonneg
        (bankPaperCanonicalRatioCellTailMajorant_nonneg
          M hdelta hn (by omega) S hrho hscale hMertens
          pband (cell - 1))
        (bankPaperCanonicalRatioCellTailMajorant_nonneg
          M hdelta hn (by omega) S hrho hscale hMertens pband cell)
  have hlogNum :
      Real.log (A : Real) * numerator <=
        2 * scale *
          (Real.log (Y : Real) - Real.log (A : Real) +
            5 * fullReciprocalSumUniformConstant /
              Real.log (A : Real) ^ 2) := by
    simpa only [A, Y, band, numerator] using
      bankPaperCanonical_logCurrentLower_mul_portNumerator_le
        M hdelta hn hWtwo S hrho hscale hMertens p
  have hlogNumNonneg : 0 <= Real.log (A : Real) * numerator :=
    mul_nonneg hlogA.le hnumNonneg
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          (numerator /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p) =
        (2 * (bankPaperCanonicalTangentPrimeLabel p : Real) /
            ((rho - 1) * (A : Real))) *
          (Real.log (A : Real) * numerator) := by
      unfold bankPaperCanonicalRatioCellPNTDenominator A
        bankPaperCanonicalRatioCellCurrentLower
      field_simp [hApos.ne', hlogA.ne', hrhoGap.ne']
    _ <= (4 * rho ^ 2 / (rho - 1)) *
          (Real.log (A : Real) * numerator) :=
      mul_le_mul_of_nonneg_right hcoefficient hlogNumNonneg
    _ <= (4 * rho ^ 2 / (rho - 1)) *
        (2 * scale *
          (Real.log (Y : Real) - Real.log (A : Real) +
            5 * fullReciprocalSumUniformConstant /
              Real.log (A : Real) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hlogNum
        (div_nonneg (by positivity) hrhoGap.le)
    _ = (8 * rho ^ 2 / (rho - 1)) * scale *
        (Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2) := by ring

/-! ## Collapse of the remaining band endpoint gap -/

/-- Every canonical exponent band has ordinary logarithmic width at most
`(delta + ratio) * log y`, up to the single `log 2` floor loss. -/
theorem bankPaperCanonical_exponentBand_logWidth_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (band : BankPaperCanonicalExponentBand M) :
    Real.log (bankPaperCanonicalExponentBandUpper M n W band : Real) -
        Real.log (bankPaperCanonicalExponentBandLower M n W band : Real) <=
      (delta + M.ratio) * Real.log (y n) + Real.log 2 := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  refine Fin.cases ?_ (fun k => ?_) band
  · have hxTwo : 2 <= scalePoint n delta := by
      have hWReal : (2 : Real) <= W := by exact_mod_cast hWtwo
      nlinarith [S.low]
    have hupperCoord := (floor_scalePoint_coordinate_bounds hn hxTwo).2
    have hupper :
        Real.log (fullCutoff M n W 1 : Real) <=
          delta * Real.log (y n) := by
      have hmul := mul_le_mul_of_nonneg_right hupperCoord hlogy.le
      simpa only [RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
        M.endpoint_zero, KernelPrimeQuadrature.realLogCoordinate,
        div_mul_cancel₀ _ hlogy.ne'] using hmul
    have hlower : 0 <= Real.log (W : Real) :=
      Real.log_nonneg (by exact_mod_cast (show 1 <= W by omega))
    have hratioLog :
        0 <= M.ratio * Real.log (y n) :=
      mul_nonneg M.ratio_pos.le hlogy.le
    have hlogTwo : 0 <= Real.log 2 :=
      Real.log_nonneg (by norm_num)
    simp only [bankPaperCanonicalExponentBandUpper,
      bankPaperCanonicalExponentBandLower, Fin.val_zero,
      Nat.zero_add, RegularMeshPrimeCutoffs.Mesh.fullCutoff_zero]
    nlinarith
  · let q : Fin M.cellCount := k
    have hLower := (floor_scalePoint_coordinate_bounds hn (hTwo q)).1
    have hUpperTwo : 2 <= scalePoint n (M.upper q) := by
      have hsep := (S.positive q).2
      nlinarith [hTwo q]
    have hUpper := (floor_scalePoint_coordinate_bounds hn hUpperTwo).2
    have hcoordGap :
        KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 2) : Real) -
            KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 1) : Real) <=
          M.width q + Real.log 2 / Real.log (y n) := by
      have hLower' :
          M.lower q - Real.log 2 / Real.log (y n) <=
            KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 1) : Real) := by
        simpa only [RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
          RegularRelativeMesh.Mesh.lower] using hLower
      have hUpper' :
          KernelPrimeQuadrature.realLogCoordinate (y n)
              (fullCutoff M n W (q.1 + 2) : Real) <= M.upper q := by
        simpa only [show q.1 + 2 = (q.1 + 1) + 1 by omega,
          RegularMeshPrimeCutoffs.Mesh.fullCutoff_succ,
          RegularRelativeMesh.Mesh.upper] using hUpper
      unfold RegularRelativeMesh.Mesh.width
      linarith
    have hlogGap :
        Real.log (fullCutoff M n W (q.1 + 2) : Real) -
            Real.log (fullCutoff M n W (q.1 + 1) : Real) <=
          M.width q * Real.log (y n) + Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hcoordGap hlogy.le
      unfold KernelPrimeQuadrature.realLogCoordinate at hmul
      field_simp [hlogy.ne'] at hmul
      nlinarith
    have hwidth := M.width_le_ratio hdelta q
    have hscaled :
        M.width q * Real.log (y n) <=
          (delta + M.ratio) * Real.log (y n) := by
      apply mul_le_mul_of_nonneg_right _ hlogy.le
      linarith
    simpa only [bankPaperCanonicalExponentBandUpper,
      bankPaperCanonicalExponentBandLower, Fin.val_succ, q] using
      hlogGap.trans (by nlinarith [hscaled])

/-- Replacing the band lower endpoint by the later current-cell start can
only shorten the logarithmic gap. -/
theorem bankPaperCanonical_currentLower_bandUpper_logGap_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (p : BankPaperCanonicalTangentPrime n W) :
    let A := bankPaperCanonicalRatioCellCurrentLower
      M hdelta hn (by omega) S rho p
    let Y := bankPaperCanonicalExponentBandUpper M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
    Real.log (Y : Real) - Real.log (A : Real) <=
      (delta + M.ratio) * Real.log (y n) + Real.log 2 := by
  dsimp only
  let band := bankPaperCanonicalExponentBandOf M hdelta hn
    (by omega : W ≠ 0) S p
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  have hLowerA : lower <= A := by
    unfold A bankPaperCanonicalRatioCellCurrentLower lower
    have hmono := tangentMultiplicativeRatioCutoff_mono
      (lower := bankPaperCanonicalExponentBandLower M n W band)
      (rho := rho) hrho.le
      (Nat.zero_le (bankPaperCanonicalRatioCellIndex
        M hdelta hn (by omega) S rho p))
    simpa only [tangentMultiplicativeRatioCutoff_zero] using hmono
  have hlowerPos : (0 : Real) < lower := by
    exact_mod_cast bankPaperCanonicalExponentBandLower_pos
      M hdelta hn (by omega) S band
  have hlogLowerA : Real.log (lower : Real) <= Real.log (A : Real) :=
    Real.log_le_log hlowerPos (by exact_mod_cast hLowerA)
  calc
    Real.log (bankPaperCanonicalExponentBandUpper M n W band : Real) -
          Real.log (A : Real) <=
        Real.log (bankPaperCanonicalExponentBandUpper M n W band : Real) -
          Real.log (lower : Real) := sub_le_sub_left hlogLowerA _
    _ <= (delta + M.ratio) * Real.log (y n) + Real.log 2 :=
      bankPaperCanonical_exponentBand_logWidth_le
        M hdelta hn hWtwo S hTwo band

/-! ## Uniform paper-scale port envelope -/

/-- Scalar port majorant, uniform in the vertex. -/
def bankPaperCanonicalRatioCellUniformPortMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (rho scale : Real) : Real :=
  (8 * rho ^ 2 / (rho - 1)) * scale *
    ((delta + M.ratio) * Real.log (y n) + Real.log 2 +
      5 * fullReciprocalSumUniformConstant /
        Real.log (W : Real) ^ 2)

/-- The PNT-normalized analytic envelope is uniformly bounded by the
paper-sized scalar port majorant. -/
theorem bankPaperCanonical_weightedPNTEnvelope_le_uniformPortMajorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        (bankPaperCanonicalRatioCellPortNumeratorEnvelope
            M hdelta hn (by omega) S rho scale p /
          bankPaperCanonicalRatioCellPNTDenominator
            M hdelta hn (by omega) S rho p) <=
      bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale := by
  let A := bankPaperCanonicalRatioCellCurrentLower
    M hdelta hn (by omega : W ≠ 0) S rho p
  let Y := bankPaperCanonicalExponentBandUpper M n W
    (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S p)
  have hWA : W <= A := by
    simpa only [A] using
      bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
        M hdelta hn (by omega) S hrho p
  have hWlog : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hAlog : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogWA : Real.log (W : Real) <= Real.log (A : Real) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hWA)
  have hpowWA : Real.log (W : Real) ^ 2 <=
      Real.log (A : Real) ^ 2 :=
    pow_le_pow_left₀ hWlog.le hlogWA 2
  have hconstant : 0 <=
      5 * fullReciprocalSumUniformConstant := by
    exact mul_nonneg (by norm_num)
      fullReciprocalSumUniformConstant_pos.le
  have herror :
      5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 2 <=
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hAlog) (sq_pos_of_pos hWlog)).2
    exact mul_le_mul_of_nonneg_left hpowWA hconstant
  have hgap := bankPaperCanonical_currentLower_bandUpper_logGap_le
    M hdelta hn hWtwo S hrho hTwo p
  have hinside :
      Real.log (Y : Real) - Real.log (A : Real) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 2 <=
        (delta + M.ratio) * Real.log (y n) + Real.log 2 +
          5 * fullReciprocalSumUniformConstant /
            Real.log (W : Real) ^ 2 := by
    linarith
  have hfactor : 0 <= (8 * rho ^ 2 / (rho - 1)) * scale := by
    exact mul_nonneg (div_nonneg (by positivity) (sub_pos.mpr hrho).le) hscale
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          (bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p) <=
        (8 * rho ^ 2 / (rho - 1)) * scale *
          (Real.log (Y : Real) - Real.log (A : Real) +
            5 * fullReciprocalSumUniformConstant /
              Real.log (A : Real) ^ 2) := by
      simpa only [A, Y] using
        bankPaperCanonical_weightedPNTEnvelope_le_logGap
          M hdelta hn hWtwo S hrho hscale hMertens p
    _ <= (8 * rho ^ 2 / (rho - 1)) * scale *
        ((delta + M.ratio) * Real.log (y n) + Real.log 2 +
          5 * fullReciprocalSumUniformConstant /
            Real.log (W : Real) ^ 2) :=
      mul_le_mul_of_nonneg_left hinside hfactor
    _ = bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale := rfl

/-- Assembly-facing uniform-port form: the proved PNT envelope and its
uniform scalar collapse are composed in one statement. -/
theorem bankPaperCanonical_weightedRatioCellUniformPortLoad_le_majorant
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ q : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S q = band then residual q else 0) = 0)
    (hpointwise : forall q : BankPaperCanonicalTangentPrime n W,
      |residual q| <= bankPaperCanonicalHarmonicPointwiseUpper scale q)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellUniformPortLoad residual
          (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
          (bankPaperCanonicalRatioCellIndex
            M hdelta hn (by omega) S rho) p <=
      bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad residual
            (bankPaperCanonicalExponentBandOf M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta hn (by omega) S rho) p <=
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          (bankPaperCanonicalRatioCellPortNumeratorEnvelope
              M hdelta hn (by omega) S rho scale p /
            bankPaperCanonicalRatioCellPNTDenominator
              M hdelta hn (by omega) S rho p) :=
      bankPaperCanonical_weightedRatioCellUniformPortLoad_le_PNTEnvelope
        M hdelta hn hWtwo S hrho hscale hMertens hPNT
          residual hbalance hpointwise p
    _ <= bankPaperCanonicalRatioCellUniformPortMajorant
        M n W rho scale :=
      bankPaperCanonical_weightedPNTEnvelope_le_uniformPortMajorant
        M hdelta hn hWtwo S hrho hscale hMertens hTwo p

/-! ## Paper-scale scalar reduction for the incident ledger -/

/-- Fixed coefficient of one weighted uniform port. -/
def bankPaperCanonicalRatioCellPortConstant (rho : Real) : Real :=
  8 * rho ^ 2 / (rho - 1)

/-- Fixed coefficient after the two ports in the incident ledger. -/
def bankPaperCanonicalRatioCellIncidentConstant (rho : Real) : Real :=
  16 * rho ^ 2 / (rho - 1)

/-- Explicit vanishing coefficient left by the weighted residual and the
two pointwise-port errors at the paper scale. -/
def bankPaperCanonicalRatioCellIncidentErrorCoefficient
    (W n : Nat) (rho tangentConstant : Real) : Real :=
  tangentConstant / Real.log (y n) *
    (1 + 2 * bankPaperCanonicalRatioCellPortConstant rho *
      (Real.log 2 +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 2))

/-- The paper specialization of `weightedResidual + 2*weightedPort`.
The main constant is fixed by `rho`; the only remainder is the displayed
scalar multiple of `1/log y`. -/
theorem bankPaperCanonical_incidentMajorant_paperScale
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {W n : Nat} {rho tangentConstant N : Real}
    (hn : 1 < n) (hWtwo : 2 <= W) (hrho : 1 < rho) :
    tangentConstant * N / Real.log (y n) +
        2 * bankPaperCanonicalRatioCellUniformPortMajorant M n W rho
          (tangentConstant * N / Real.log (y n)) =
      bankPaperCanonicalRatioCellIncidentConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellIncidentErrorCoefficient
          W n rho tangentConstant * N := by
  have hlogy : Real.log (y n) ≠ 0 := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact (mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))).ne'
  have hrhoGap : rho - 1 ≠ 0 := (sub_pos.mpr hrho).ne'
  have hlogW : Real.log (W : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < W by omega))).ne'
  unfold bankPaperCanonicalRatioCellUniformPortMajorant
    bankPaperCanonicalRatioCellIncidentConstant
    bankPaperCanonicalRatioCellIncidentErrorCoefficient
  unfold bankPaperCanonicalRatioCellPortConstant
  field_simp [hlogy, hrhoGap, hlogW]; ring

/-- The incident error coefficient vanishes after all paper parameters are
fixed. -/
theorem tendsto_bankPaperCanonicalRatioCellIncidentErrorCoefficient_zero
    (W : Nat) (rho tangentConstant : Real) :
    Tendsto
      (fun n : Nat =>
        bankPaperCanonicalRatioCellIncidentErrorCoefficient
          W n rho tangentConstant)
      atTop (nhds 0) := by
  have hbase : Tendsto
      (fun n : Nat => tangentConstant / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop
      RegularMeshPrimeCutoffs.Mesh.tendsto_log_y_atTop
  have hconstant : Tendsto
      (fun _n : Nat =>
        1 + 2 * bankPaperCanonicalRatioCellPortConstant rho *
          (Real.log 2 +
            5 * fullReciprocalSumUniformConstant /
              Real.log (W : Real) ^ 2))
      atTop
      (nhds
        (1 + 2 * bankPaperCanonicalRatioCellPortConstant rho *
          (Real.log 2 +
            5 * fullReciprocalSumUniformConstant /
              Real.log (W : Real) ^ 2))) :=
    tendsto_const_nhds
  simpa only [bankPaperCanonicalRatioCellIncidentErrorCoefficient,
    zero_mul] using hbase.mul hconstant

/-! ## A manifestly vanishing upper coefficient for total traffic -/

/-- A nonnegative asymptotic upper form for the total-traffic error
coefficient.  It separates `log(log y)/log y` from fixed multiples of
`1/log y`. -/
def bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W n : Nat) (rho tangentConstant : Real) : Real :=
  (tangentConstant / 2) *
      (Real.log (Real.log (y n)) / Real.log (y n)) +
    (tangentConstant / 2 *
      (|Real.log (Real.log (W : Real))| +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 3)) *
      (1 / Real.log (y n)) +
    (6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
      Real.log rho) * (1 / Real.log (y n))

/-- The exact scalar remainder is bounded by the manifestly vanishing
upper coefficient as soon as the floored top endpoint is at least two. -/
theorem bankPaperCanonical_ratioCellTrafficErrorCoefficient_le_upper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {W n : Nat} {rho tangentConstant : Real}
    (hn : 1 < n) (hWtwo : 2 <= W) (hyNatTwo : 2 <= yNat n)
    (hrho : 1 < rho)
    (htangent : 0 <= tangentConstant) :
    bankPaperCanonicalRatioCellTrafficErrorCoefficient
        M n W rho tangentConstant <=
      bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
        M W n rho tangentConstant := by
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  have hyNatPos : (0 : Real) < yNat n := by positivity
  have hyFloor : (yNat n : Real) <= y n := by
    exact Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hlogNat : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hlogNatY :
      Real.log (yNat n : Real) <= Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogLogNatY :
      Real.log (Real.log (yNat n : Real)) <=
        Real.log (Real.log (y n)) :=
    Real.log_le_log hlogNat hlogNatY
  have hWlog : 0 < Real.log (W : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < W by omega))
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hglobal :
      Real.log (Real.log (yNat n : Real)) -
          Real.log (Real.log (W : Real)) +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 3 <=
        Real.log (Real.log (y n)) +
          |Real.log (Real.log (W : Real))| +
        5 * fullReciprocalSumUniformConstant /
          Real.log (W : Real) ^ 3 := by
    have habs := neg_le_abs (Real.log (Real.log (W : Real)))
    linarith
  have hfactor : 0 <= tangentConstant / (2 * Real.log (y n)) :=
    div_nonneg htangent (mul_nonneg (by norm_num) hlogy.le)
  unfold bankPaperCanonicalRatioCellTrafficErrorCoefficient
    bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
  have hscaled := mul_le_mul_of_nonneg_left hglobal hfactor
  field_simp [hlogy.ne', hWlog.ne', hlogrho.ne'] at hscaled ⊢
  nlinarith

/-- The upper total-traffic error coefficient tends to zero for every fixed
mesh, cutoff, ratio, and tangent constant. -/
theorem tendsto_bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient_zero
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant : Real) :
    Tendsto
      (fun n : Nat =>
        bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
          M W n rho tangentConstant)
      atTop (nhds 0) := by
  have hLTop : Tendsto (fun n : Nat => Real.log (y n)) atTop atTop :=
    RegularMeshPrimeCutoffs.Mesh.tendsto_log_y_atTop
  have hlogRatio : Tendsto
      (fun n : Nat =>
        Real.log (Real.log (y n)) / Real.log (y n))
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hInv : Tendsto (fun n : Nat => 1 / Real.log (y n))
      atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hLTop
  have hfirst : Tendsto
      (fun n : Nat =>
        (tangentConstant / 2) *
          (Real.log (Real.log (y n)) / Real.log (y n)))
      atTop (nhds ((tangentConstant / 2) * 0)) :=
    tendsto_const_nhds.mul hlogRatio
  have hsecond : Tendsto
      (fun n : Nat =>
        (tangentConstant / 2 *
          (|Real.log (Real.log (W : Real))| +
            5 * fullReciprocalSumUniformConstant /
              Real.log (W : Real) ^ 3)) *
          (1 / Real.log (y n)))
      atTop
        (nhds
          ((tangentConstant / 2 *
            (|Real.log (Real.log (W : Real))| +
              5 * fullReciprocalSumUniformConstant /
                Real.log (W : Real) ^ 3)) * 0)) :=
    tendsto_const_nhds.mul hInv
  have hthird : Tendsto
      (fun n : Nat =>
        (6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
            Real.log rho) *
          (1 / Real.log (y n)))
      atTop
        (nhds
          ((6 * tangentConstant * M.ratio * (M.cellCount : Real) * Real.log 2 /
              Real.log rho) * 0)) :=
    tendsto_const_nhds.mul hInv
  simpa only [bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient,
    mul_zero, zero_add] using (hfirst.add hsecond).add hthird

/-- The floored paper endpoint tends to infinity. -/
theorem bankPaperCanonical_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

/-- Once the fixed parameters have been chosen, both displayed scalar
remainders are eventually below arbitrary positive traffic and incident
error budgets. -/
theorem eventually_bankPaperCanonical_ratioCellErrorCoefficients_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant trafficError incidentError : Real)
    (htrafficError : 0 < trafficError)
    (hincidentError : 0 < incidentError) :
    ∀ᶠ n : Nat in atTop,
      2 <= yNat n ∧
      bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
          M W n rho tangentConstant <= trafficError ∧
      bankPaperCanonicalRatioCellIncidentErrorCoefficient
          W n rho tangentConstant <= incidentError := by
  have hyNat : ∀ᶠ n : Nat in atTop, 2 <= yNat n :=
    bankPaperCanonical_yNat_tendsto_atTop.eventually
      (eventually_ge_atTop 2)
  have htraffic :=
    (tendsto_bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient_zero
      M W rho tangentConstant).eventually
        (eventually_le_nhds htrafficError)
  have hincident :=
    (tendsto_bankPaperCanonicalRatioCellIncidentErrorCoefficient_zero
      W rho tangentConstant).eventually
        (eventually_le_nhds hincidentError)
  filter_upwards [hyNat, htraffic, hincident] with n hn hT hI
  exact ⟨hn, hT, hI⟩

/-! ## Explicit fixed choices for the paper budgets -/

/-- The coefficient multiplying the fixed band width in the distributed
paper main budget after inserting the concrete traffic and incident
constants. -/
def bankPaperCanonicalRatioCellMainCoefficient (rho : Real) : Real :=
  16 * bankPaperCanonicalRatioCellTrafficConstant rho +
    8 * bankPaperCanonicalRatioCellIncidentConstant rho

/-- The fixed main-budget coefficient is positive for every `rho > 1`. -/
theorem bankPaperCanonical_ratioCellMainCoefficient_pos
    {rho : Real} (hrho : 1 < rho) :
    0 < bankPaperCanonicalRatioCellMainCoefficient rho := by
  have hlogrho : 0 < Real.log rho := Real.log_pos hrho
  have hrho0 : 0 < rho := lt_trans zero_lt_one hrho
  have hrhoGap : 0 < rho - 1 := sub_pos.mpr hrho
  unfold bankPaperCanonicalRatioCellMainCoefficient
    bankPaperCanonicalRatioCellTrafficConstant
    bankPaperCanonicalRatioCellIncidentConstant
  exact add_pos
    (mul_pos (by norm_num) (div_pos (by norm_num) hlogrho))
    (mul_pos (by norm_num)
      (div_pos (mul_pos (by norm_num) (sq_pos_of_pos hrho0)) hrhoGap))

/-- A fixed positive width leaving a factor-two reserve in `hmain`.
It depends only on the already-fixed density, split parameter, cell ratio,
and tangent constant, never on the final asymptotic variable `n`. -/
def bankPaperCanonicalRatioCellPaperWidthChoice
    (density sigma rho tangentConstant : Real) : Real :=
  density ^ 2 * sigma /
    (96 * bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant)

/-- The explicit paper width choice is positive under the paper parameter
sign conditions. -/
theorem bankPaperCanonical_ratioCellPaperWidthChoice_pos
    {density sigma rho tangentConstant : Real}
    (hdensity : 0 < density) (hsigma : 0 < sigma)
    (hrho : 1 < rho) (htangent : 0 < tangentConstant) :
    0 < bankPaperCanonicalRatioCellPaperWidthChoice
      density sigma rho tangentConstant := by
  have hcoefficient :
      0 < bankPaperCanonicalRatioCellMainCoefficient rho :=
    bankPaperCanonical_ratioCellMainCoefficient_pos hrho
  unfold bankPaperCanonicalRatioCellPaperWidthChoice
  positivity

/-- At the displayed width choice, the main budget is exactly half of its
allowed `density^2 / 48` allocation. -/
theorem bankPaperCanonical_paperMainBudget_widthChoice_eq
    {density sigma rho tangentConstant : Real}
    (hsigma : 0 < sigma) (hrho : 1 < rho)
    (htangent : 0 < tangentConstant) :
    tangentDistributedPaperMainBudget
        (bankPaperCanonicalRatioCellTrafficConstant rho)
        (bankPaperCanonicalRatioCellIncidentConstant rho)
        tangentConstant
        (bankPaperCanonicalRatioCellPaperWidthChoice
          density sigma rho tangentConstant)
        sigma =
      density ^ 2 / 96 := by
  have hcoefficient :
      bankPaperCanonicalRatioCellMainCoefficient rho ≠ 0 :=
    (bankPaperCanonical_ratioCellMainCoefficient_pos hrho).ne'
  change
    (bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant *
        bankPaperCanonicalRatioCellPaperWidthChoice
          density sigma rho tangentConstant) / sigma =
      density ^ 2 / 96
  unfold bankPaperCanonicalRatioCellPaperWidthChoice
  field_simp [hcoefficient, htangent.ne', hsigma.ne']

/-- Any mesh width below the fixed choice satisfies the exact `hmain`
premise used by the Section 9 assembly. -/
theorem bankPaperCanonical_paperMainBudget_le
    {density sigma rho tangentConstant width : Real}
    (hsigma : 0 < sigma) (hrho : 1 < rho)
    (htangent : 0 < tangentConstant)
    (hwidth : width <= bankPaperCanonicalRatioCellPaperWidthChoice
      density sigma rho tangentConstant) :
    tangentDistributedPaperMainBudget
        (bankPaperCanonicalRatioCellTrafficConstant rho)
        (bankPaperCanonicalRatioCellIncidentConstant rho)
        tangentConstant width sigma <=
      density ^ 2 / 48 := by
  have hcoefficient :
      0 <= bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant :=
    mul_nonneg
      (bankPaperCanonical_ratioCellMainCoefficient_pos hrho).le htangent.le
  have hscaled := mul_le_mul_of_nonneg_left hwidth hcoefficient
  have hbudget :
      tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant width sigma <=
        tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant
          (bankPaperCanonicalRatioCellPaperWidthChoice
            density sigma rho tangentConstant)
          sigma := by
    change
      (bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant *
          width) / sigma <=
        (bankPaperCanonicalRatioCellMainCoefficient rho * tangentConstant *
          bankPaperCanonicalRatioCellPaperWidthChoice
            density sigma rho tangentConstant) / sigma
    exact div_le_div_of_nonneg_right hscaled hsigma.le
  calc
    tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant width sigma <=
        tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant
          (bankPaperCanonicalRatioCellPaperWidthChoice
            density sigma rho tangentConstant)
          sigma := hbudget
    _ = density ^ 2 / 96 :=
      bankPaperCanonical_paperMainBudget_widthChoice_eq
        hsigma hrho htangent
    _ <= density ^ 2 / 48 := by nlinarith [sq_nonneg density]

/-- A symmetric positive allocation for the two error coefficients.  The
weights `16` and `8` then sum to exactly the available `density^2 / 96`
paper error budget. -/
def bankPaperCanonicalRatioCellPaperErrorChoice
    (density sigma : Real) : Real :=
  density ^ 2 * sigma / 2304

/-- The symmetric error allocation is positive for positive density and
split scale. -/
theorem bankPaperCanonical_ratioCellPaperErrorChoice_pos
    {density sigma : Real} (hdensity : 0 < density) (hsigma : 0 < sigma) :
    0 < bankPaperCanonicalRatioCellPaperErrorChoice density sigma := by
  unfold bankPaperCanonicalRatioCellPaperErrorChoice
  positivity

/-- Using the symmetric allocation for both errors exactly fills the
`density^2 / 96` paper error budget. -/
theorem bankPaperCanonical_paperErrorBudget_choice_eq
    {density sigma : Real} (hsigma : 0 < sigma) :
    tangentDistributedPaperErrorBudget
        (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
        (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
        sigma =
      density ^ 2 / 96 := by
  unfold tangentDistributedPaperErrorBudget
    bankPaperCanonicalRatioCellPaperErrorChoice
  field_simp [hsigma.ne']; ring

/-- For the explicit fixed error allocation, the asymptotic traffic and
incident coefficients jointly satisfy the precise `herror` premise of the
Section 9 assembly. -/
theorem eventually_bankPaperCanonical_paperErrorBudget_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant density sigma : Real)
    (hdensity : 0 < density) (hsigma : 0 < sigma) :
    ∀ᶠ n : Nat in atTop,
      2 <= yNat n ∧
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
            M W n rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <= density ^ 2 / 96 := by
  have hchoice :
      0 < bankPaperCanonicalRatioCellPaperErrorChoice density sigma :=
    bankPaperCanonical_ratioCellPaperErrorChoice_pos hdensity hsigma
  have hcoefficients :=
    eventually_bankPaperCanonical_ratioCellErrorCoefficients_le
      M W rho tangentConstant
      (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
      (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
      hchoice hchoice
  filter_upwards [hcoefficients] with n hn
  refine ⟨hn.1, ?_⟩
  have htraffic := mul_le_mul_of_nonneg_left hn.2.1 (by norm_num :
    (0 : Real) <= 16)
  have hincident := mul_le_mul_of_nonneg_left hn.2.2 (by norm_num :
    (0 : Real) <= 8)
  have hbudget :
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
            M W n rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <=
        tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
          (bankPaperCanonicalRatioCellPaperErrorChoice density sigma)
          sigma := by
    unfold tangentDistributedPaperErrorBudget
    exact div_le_div_of_nonneg_right
      (add_le_add htraffic hincident) hsigma.le
  exact hbudget.trans_eq
    (bankPaperCanonical_paperErrorBudget_choice_eq hsigma)

end

end Erdos390.WholePaper
