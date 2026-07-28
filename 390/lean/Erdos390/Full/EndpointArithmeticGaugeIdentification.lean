import Erdos390.Full.EndpointContinuumMeshIdentification
import Erdos390.Full.PositiveCellTransfer

/-!
# Exact endpoint identification of the continuum gauge

The arithmetic endpoint certificate and the continuum interval mesh use
different-looking definitions of the cell centre.  This file proves that
the corresponding *continuum* centres are exactly equal.  In particular,
no arithmetic centre is silently substituted for a continuum centre.
-/

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open KernelPrimeQuadrature
open DoubleKernelPrimeQuadrature
open PrimeBandQuadrature
open PositiveCellTransfer

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

omit [DecidableEq Band] in
/-- The interval-mesh centre is exactly the coordinate length divided by
the endpoint continuum harmonic mass. -/
theorem center_eq_endpointCoordinateCenter
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i : Band) :
    M.center i =
      (realLogCoordinate z (upper i : ℝ) -
          realLogCoordinate z (lower i : ℝ)) /
        continuumCellMass z (lower i) (upper i) := by
  unfold center length
  rw [hLower i, hUpper i,
    M.harmonicMass_eq_continuumCellMass
      z lower upper hLower hUpper i]

omit [DecidableEq Band] in
/-- Specialization to an actual certified prime interval.  The continuum
centre `E.continuumCenter` used in the arithmetic gauge transfer is
literally the centre of the endpoint interval mesh. -/
theorem center_eq_intervalCertificate_continuumCenter
    {n W : ℕ}
    {P : ArithmeticBandGeometry.Partition n W Band}
    (E : PositiveCellTransfer.IntervalCertificate P)
    (hn : 1 < ArithmeticModel.y n)
    (hLowerTwo : ∀ i, 2 ≤ E.lower i)
    (hLower : ∀ i,
      M.lower i = realLogCoordinate (ArithmeticModel.y n) (E.lower i : ℝ))
    (hUpper : ∀ i,
      M.upper i = realLogCoordinate (ArithmeticModel.y n) (E.upper i : ℝ))
    (i : Band) :
    M.center i = E.continuumCenter i := by
  rw [M.center_eq_endpointCoordinateCenter
    (ArithmeticModel.y n) E.lower E.upper hLower hUpper i]
  unfold PositiveCellTransfer.IntervalCertificate.continuumCenter
  unfold PositiveCellTransfer.IntervalCertificate.continuumMoment
  unfold PositiveCellTransfer.IntervalCertificate.continuumMass
  have hAY : E.lower i ≤ E.upper i := E.lower_le_upper i
  have hmass := log_logCoordinate_sub hn (hLowerTwo i) hAY
  have hmoment := logCoordinate_sub
    (z := ArithmeticModel.y n) (A := E.lower i) (Y := E.upper i) hn
  change
    (logCoordinate (ArithmeticModel.y n) (E.upper i) -
        logCoordinate (ArithmeticModel.y n) (E.lower i)) /
      (Real.log (logCoordinate (ArithmeticModel.y n) (E.upper i)) -
        Real.log (logCoordinate (ArithmeticModel.y n) (E.lower i))) =
    ((Real.log (E.upper i : ℝ) - Real.log (E.lower i : ℝ)) /
        Real.log (ArithmeticModel.y n)) /
      (Real.log (Real.log (E.upper i : ℝ)) -
        Real.log (Real.log (E.lower i : ℝ)))
  rw [hmass, hmoment]

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
