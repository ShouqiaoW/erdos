import Erdos390.Full.UniformMeshArithmeticInverse

/-!
# Aggregating endpoint errors into the complete sharp row budget

This file makes explicit the finite summation step between entrywise
diagonal/kernel/centre estimates and the row budget used by the stable
inverse.  In particular, the arithmetic centre ratio is bounded by its
proved continuum comparison before the kernel errors are summed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open CompressedArithmeticOperator

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- A completely explicit finite envelope for one continuum row. -/
def arithmeticRowEnvelope (i : Band) : ℝ :=
  1 + (∑ j, (1 + |M.center j / M.center i|)) +
    ∑ j, |M.normalizedKernelCell i j|

omit [DecidableEq Band] in
theorem arithmeticRowEnvelope_pos (i : Band) :
    0 < M.arithmeticRowEnvelope i := by
  unfold arithmeticRowEnvelope
  have hcenter : 0 ≤ ∑ j, (1 + |M.center j / M.center i|) :=
    Finset.sum_nonneg (fun j hj => by positivity)
  have hkernel : 0 ≤ ∑ j, |M.normalizedKernelCell i j| :=
    Finset.sum_nonneg (fun j hj => abs_nonneg _)
  linarith

/-- A finite envelope valid for every row of this particular mesh. -/
def arithmeticGlobalEnvelope : ℝ :=
  ∑ i, M.arithmeticRowEnvelope i

omit [DecidableEq Band] in
theorem arithmeticRowEnvelope_le_global (i : Band) :
    M.arithmeticRowEnvelope i ≤ M.arithmeticGlobalEnvelope := by
  unfold arithmeticGlobalEnvelope
  exact Finset.single_le_sum
    (fun j hj => (M.arithmeticRowEnvelope_pos j).le)
    (Finset.mem_univ i)

omit [DecidableEq Band] in
theorem arithmeticGlobalEnvelope_pos [Nonempty Band] :
    0 < M.arithmeticGlobalEnvelope := by
  unfold arithmeticGlobalEnvelope
  exact Finset.sum_pos
    (fun i hi => M.arithmeticRowEnvelope_pos i)
    Finset.univ_nonempty

omit [DecidableEq Band] in
/-- Uniform entrywise errors bounded by `delta` aggregate with no hidden
factor: the only finite factor is the displayed row envelope. -/
theorem arithmeticGraphRowBudget_le_envelope
    (diagonalError : Band → ℝ)
    (kernelA kernelError centerRatioError : Band → Band → ℝ)
    (alpha : Band → ℝ) {delta residualBound : ℝ}
    (hdelta : 0 ≤ delta) (hdeltaOne : delta ≤ 1)
    (hDiagonalError : ∀ i, diagonalError i ≤ delta)
    (hKernelActual : ∀ i j,
      |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j)
    (hKernelError : ∀ i j, kernelError i j ≤ delta)
    (hCenterActual : ∀ i j,
      |alpha j / alpha i - M.center j / M.center i| ≤
        centerRatioError i j)
    (hCenterError : ∀ i j, centerRatioError i j ≤ delta)
    (hResidual : ∀ i, |M.rowResidual i| ≤ residualBound)
    (i : Band) :
    M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i ≤
      delta * M.arithmeticRowEnvelope i + residualBound := by
  have hKernelNonneg (j : Band) : 0 ≤ kernelError i j :=
    (abs_nonneg
      (kernelA i j - M.normalizedKernelCell i j)).trans
        (hKernelActual i j)
  have hCenterNonneg (j : Band) : 0 ≤ centerRatioError i j :=
    (abs_nonneg
      (alpha j / alpha i - M.center j / M.center i)).trans
        (hCenterActual i j)
  have hAlpha (j : Band) :
      |alpha j / alpha i| ≤ 1 + |M.center j / M.center i| := by
    have htriangle :
        |alpha j / alpha i| ≤
          |alpha j / alpha i - M.center j / M.center i| +
            |M.center j / M.center i| := by
      calc
        |alpha j / alpha i| =
            |(alpha j / alpha i - M.center j / M.center i) +
              M.center j / M.center i| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    calc
      |alpha j / alpha i| ≤
          |alpha j / alpha i - M.center j / M.center i| +
            |M.center j / M.center i| := htriangle
      _ ≤ centerRatioError i j +
            |M.center j / M.center i| :=
        add_le_add (hCenterActual i j) le_rfl
      _ ≤ 1 + |M.center j / M.center i| :=
        add_le_add ((hCenterError i j).trans hdeltaOne) le_rfl
  have hKernelSum :
      (∑ j, kernelError i j * |alpha j / alpha i|) ≤
        delta * (∑ j, (1 + |M.center j / M.center i|)) := by
    calc
      (∑ j, kernelError i j * |alpha j / alpha i|) ≤
          ∑ j, delta * (1 + |M.center j / M.center i|) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul (hKernelError i j) (hAlpha j)
          (abs_nonneg _) (hdelta)
      _ = delta * (∑ j, (1 + |M.center j / M.center i|)) := by
        rw [Finset.mul_sum]
  have hCenterSum :
      (∑ j, |M.normalizedKernelCell i j| * centerRatioError i j) ≤
        delta * ∑ j, |M.normalizedKernelCell i j| := by
    calc
      (∑ j, |M.normalizedKernelCell i j| * centerRatioError i j) ≤
          ∑ j, |M.normalizedKernelCell i j| * delta := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (hCenterError i j) (abs_nonneg _)
      _ = delta * ∑ j, |M.normalizedKernelCell i j| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  unfold arithmeticGraphRowBudget arithmeticRowEnvelope
  calc
    diagonalError i +
          (∑ j, kernelError i j * |alpha j / alpha i|) +
          (∑ j, |M.normalizedKernelCell i j| * centerRatioError i j) +
          |M.rowResidual i| ≤
        delta +
          delta * (∑ j, (1 + |M.center j / M.center i|)) +
          (delta * ∑ j, |M.normalizedKernelCell i j|) +
          residualBound := by
      exact add_le_add
        (add_le_add (add_le_add (hDiagonalError i) hKernelSum) hCenterSum)
        (hResidual i)
    _ = delta *
          (1 + (∑ j, (1 + |M.center j / M.center i|)) +
            ∑ j, |M.normalizedKernelCell i j|) + residualBound := by
      ring

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
