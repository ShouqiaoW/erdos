import Erdos390.Full.ArithmeticRowBudgetAggregation
import Erdos390.Full.ContinuumRowResidualBound

/-!
# An auditable mesh-to-row-budget theorem

The continuum tolerances are chosen first.  Every tail-certified mesh with
that diameter and cutoff then admits an explicit arithmetic accuracy
threshold, expressed through its finite global envelope, which guarantees
the complete sharp row budget.  The continuum residual is a conclusion of
the removable-kernel argument, not an assumption.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

variable {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

omit [DecidableEq Band] [Nonempty Band] in
/-- Choose the mesh diameter and omitted-tail cutoff before seeing any
arithmetic cells.  Entrywise errors at the subsequently displayed finite
scale then imply the whole row budget. -/
theorem exists_tolerances_imply_arithmeticGraphRowBudget
    {target : ℝ} (htarget : 0 < target) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ beta : ℝ, 0 < beta ∧
      ∀ P : M.TailPartitionCertificate,
        P.base < beta → (∀ j, M.length j < eta) →
      ∀ (diagonalError : Band → ℝ)
        (kernelA kernelError centerRatioError : Band → Band → ℝ)
        (alpha : Band → ℝ) (delta : ℝ),
        0 ≤ delta → delta ≤ 1 →
        delta * M.arithmeticGlobalEnvelope ≤ target / 2 →
        (∀ i, diagonalError i ≤ delta) →
        (∀ i j,
          |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j) →
        (∀ i j, kernelError i j ≤ delta) →
        (∀ i j,
          |alpha j / alpha i - M.center j / M.center i| ≤
            centerRatioError i j) →
        (∀ i j, centerRatioError i j ≤ delta) →
        ∀ i,
          M.arithmeticGraphRowBudget diagonalError kernelError
            centerRatioError alpha i ≤ target := by
  have hhalf : 0 < target / 2 := div_pos htarget (by norm_num)
  obtain ⟨eta, heta, beta, hbeta, hresidual⟩ :=
    M.exists_rowResidual_uniform_tolerances hhalf
  refine ⟨eta, heta, beta, hbeta, ?_⟩
  intro P hbase hdiam diagonalError kernelA kernelError
    centerRatioError alpha delta hdelta hdeltaOne hdeltaScale
    hDiagonalError hKernelActual hKernelError hCenterActual hCenterError i
  have haggregate := M.arithmeticGraphRowBudget_le_envelope
    diagonalError kernelA kernelError centerRatioError alpha
    (delta := delta) (residualBound := target / 2)
    hdelta hdeltaOne hDiagonalError hKernelActual hKernelError
    hCenterActual hCenterError
    (fun k => (hresidual P hbase hdiam k).le) i
  have hrowScale :
      delta * M.arithmeticRowEnvelope i ≤ target / 2 := by
    exact (mul_le_mul_of_nonneg_left
      (M.arithmeticRowEnvelope_le_global i) hdelta).trans hdeltaScale
  exact haggregate.trans (by linarith)

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
