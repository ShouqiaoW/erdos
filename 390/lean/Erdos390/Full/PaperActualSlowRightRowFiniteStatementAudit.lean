import Erdos390.Full.PaperActualSlowRightRowFinite

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open ConditionedPoissonLimit DickmanBasic

namespace PaperActualSlowRightRowFinite

/-- Independently elaborated paper-facing statement of the global structural
Lipschitz constant used by the finite moving-low estimate. -/
theorem expanded_exists_F_lipschitz_unit :
    ∃ CF : ℝ, 0 < CF ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |F s - F t| ≤ CF * |s - t| := by
  exact exists_F_lipschitz_unit

end PaperActualSlowRightRowFinite

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Independently elaborated paper-facing statement of the finite moving-low
reference-row estimate. -/
theorem expanded_referenceBandRow_bandCenter_le_of_rowResidual
    (B : BridgeData Head Band)
    {rowError w CF CKernel : ℝ}
    (hw : 0 ≤ w) (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hrowResidual : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |referenceBandRow B.partition B.bandCenter i| ≤
      (rowError + (2 * CF + 7 * CKernel) * w) * B.bandCenter i := by
  exact B.referenceBandRow_bandCenter_le_of_rowResidual
    hw hCF hCKernel hrowResidual hFdiff hKernelProduct hdevSup hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
