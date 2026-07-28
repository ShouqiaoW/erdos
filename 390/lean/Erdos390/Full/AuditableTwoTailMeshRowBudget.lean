import Erdos390.Full.ArithmeticRowBudgetAggregation
import Erdos390.Full.ContinuumTwoTailResidualBound

/-! # Auditable two-tail mesh-to-row-budget transfer -/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Two-tail version of the complete arithmetic row-budget theorem. -/
theorem exists_twoTail_tolerances_imply_arithmeticGraphRowBudget
    {target : ℝ} (htarget : 0 < target) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ beta : ℝ, 0 < beta ∧
      ∀ P : M.TwoTailPartitionCertificate,
        P.base < beta → 1 - P.upperEnd < beta →
          (∀ j, M.length j < eta) →
      ∀ (diagonalError : Band → ℝ)
        (kernelA kernelError centerRatioError : Band → Band → ℝ)
        (alpha : Band → ℝ) (d : ℝ),
        0 ≤ d → d ≤ 1 →
        d * M.arithmeticGlobalEnvelope ≤ target / 2 →
        (∀ i, diagonalError i ≤ d) →
        (∀ i j,
          |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j) →
        (∀ i j, kernelError i j ≤ d) →
        (∀ i j,
          |alpha j / alpha i - M.center j / M.center i| ≤
            centerRatioError i j) →
        (∀ i j, centerRatioError i j ≤ d) →
        ∀ i,
          M.arithmeticGraphRowBudget diagonalError kernelError
            centerRatioError alpha i ≤ target := by
  have hhalf : 0 < target / 2 := div_pos htarget (by norm_num)
  obtain ⟨eta, heta, beta, hbeta, hresidual⟩ :=
    M.exists_rowResidual_uniform_twoTail_tolerances hhalf
  refine ⟨eta, heta, beta, hbeta, ?_⟩
  intro P hbase htop hdiam diagonalError kernelA kernelError
    centerRatioError alpha d hd hdOne hdScale hDiagonalError
    hKernelActual hKernelError hCenterActual hCenterError i
  have haggregate := M.arithmeticGraphRowBudget_le_envelope
    diagonalError kernelA kernelError centerRatioError alpha
    (delta := d) (residualBound := target / 2)
    hd hdOne hDiagonalError hKernelActual hKernelError
    hCenterActual hCenterError
    (fun k => (hresidual P hbase htop hdiam k).le) i
  have hrowScale : d * M.arithmeticRowEnvelope i ≤ target / 2 :=
    (mul_le_mul_of_nonneg_left
      (M.arithmeticRowEnvelope_le_global i) hd).trans hdScale
  exact haggregate.trans (by linarith)

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
