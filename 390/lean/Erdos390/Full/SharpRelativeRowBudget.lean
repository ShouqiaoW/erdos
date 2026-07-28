import Erdos390.Full.MovingLowSharpRowAggregation
import Erdos390.Full.ContinuumSharpArithmeticTransfer

/-!
# Complete row budget with moving-low relative errors

Uniform absolute pairwise centre-ratio errors are not the correct input when
the low centre tends to zero.  This theorem packages the exact four terms of
`arithmeticGraphRowBudget`, using a relative error for individual centres and
the already weighted kernel-quadrature row sum.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

theorem arithmeticGraphRowBudget_le_of_relativeCenter
    (P : M.TwoTailPartitionCertificate)
    (diagonalError : Band → ℝ)
    (kernelError centerRatioError : Band → Band → ℝ)
    (alpha : Band → ℝ) {d k e r C : ℝ}
    (hd : ∀ i, diagonalError i ≤ d)
    (hk : ∀ i,
      (∑ j, kernelError i j * |alpha j / alpha i|) ≤ k)
    (he : 0 ≤ e) (heHalf : e ≤ 1 / 2)
    (hrel : ∀ j, |alpha j / M.center j - 1| ≤ e)
    (hcenterError : ∀ i j,
      centerRatioError i j =
        |alpha j / alpha i - M.center j / M.center i|)
    (hKernelBound : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ C)
    (hresidual : ∀ i, |M.rowResidual i| ≤ r)
    (i : Band) :
    M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i ≤
      d + k + 4 * e * C + r := by
  have hcenter := M.centerRatio_weightedRow_le P alpha he heHalf hrel
    hKernelBound i
  unfold arithmeticGraphRowBudget
  calc
    diagonalError i +
        (∑ j, kernelError i j * |alpha j / alpha i|) +
        (∑ j, |M.normalizedKernelCell i j| * centerRatioError i j) +
        |M.rowResidual i| ≤
      d + k + 4 * e * C + r := by
        have hcenter' :
            (∑ j, |M.normalizedKernelCell i j| * centerRatioError i j) ≤
              4 * e * C := by
          simpa only [hcenterError] using hcenter
        linarith [hd i, hk i, hcenter', hresidual i]

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
