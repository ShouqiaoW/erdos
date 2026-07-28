import Erdos390.Full.PaperNonstepReferenceSlowDirect

/-!
Expanded statement audit for the exact direct harmonic-centering bound.
The displayed interface contains neither a row-residual hypothesis nor a
least-cell or `delta` loss.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference ConditionedPoissonLimit DickmanBasic

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

example {w CF CKernel : ℝ}
    (hw : 0 ≤ w) (hCKernel : 0 ≤ CKernel)
    (hFone : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) - 1| ≤
        CF * tPrime B.sampleData.n p.1)
    (hKernelProduct : ∀ p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.referenceSlowRow i| ≤
      (CF + 7 * CKernel) * w * B.bandCenter i := by
  exact B.abs_referenceSlowRow_le_of_harmonicCentering
    hw hCKernel hFone hKernelProduct hdevSup hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

#print Erdos390.Full.PaperBridgeFit.BridgeData.abs_referenceSlowRow_le_of_harmonicCentering
