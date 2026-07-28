import Erdos390.Full.PaperNonstepLocalDiagonal
import Erdos390.Full.PaperNonstepSlowRightLedger

open scoped BigOperators

namespace Erdos390.Full.ArithmeticBandGeometry.Partition

open ArithmeticModel ArithmeticBandGeometry PrimeSums

noncomputable section

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
  (P : Partition n W Band)

/-- Expanded audit of the two literal global moments in the low-cell
diagonal estimate. -/
example (hn : 1 < n) (i : Band) :
    (1 / P.mass i) *
        ∑ p ∈ P.data.fiber i,
          |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤
      (1 / P.mass i) *
        (P.center i * bandReciprocalSquareSum n W +
          bandTReciprocalSquareSum n W) := by
  exact P.normalizedDeviationReciprocalSquare_le_global_moments hn i

/-- Expanded audit of the positive-cell moving-lower-endpoint estimate. -/
example {i : Band} {A w : ℝ}
    (hA : 0 < A)
    (hlower : ∀ p ∈ P.data.fiber i, A < (p.1 : ℝ))
    (hdev : ∀ p ∈ P.data.fiber i, |P.deviation p| ≤ w)
    (hw : 0 ≤ w) :
    (1 / P.mass i) *
        ∑ p ∈ P.data.fiber i,
          |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤ w / A := by
  exact P.normalizedDeviationReciprocalSquare_le_scale_div_lower
    hA hlower hdev hw

end

end Erdos390.Full.ArithmeticBandGeometry.Partition

namespace Erdos390.Full.PaperBridgeFit.BridgeData

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The partition helper is definitionally the diagonal exported by the
non-step full-versus-squarefree ledger. -/
example (i : Band) :
    B.bandDeviationReciprocalSquare i =
      B.partition.normalizedDeviationReciprocalSquare i := rfl

end

end Erdos390.Full.PaperBridgeFit.BridgeData
