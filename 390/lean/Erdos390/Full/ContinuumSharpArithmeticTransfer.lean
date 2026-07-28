import Erdos390.Full.ContinuumCellGraph
import Erdos390.Full.CompressedArithmeticOperator

/-!
# From normalized arithmetic cells to the continuum graph

The exact sharp continuum matrix differs from its positive graph Laplacian
only by an explicit row residual.  Arithmetic quadrature errors, center
errors, and that residual are aggregated here into one sharp row budget.
No inverse or coercivity statement occurs among the hypotheses.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open CompressedArithmeticOperator
open DickmanBasic

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Harmonic cell average of the diagonal multiplier. -/
def normalizedDiagonalCell (i : Band) : ℝ :=
  (∫ s in M.lower i..M.upper i, F s / s) / M.harmonicMass i

def continuumSharpOperator (q : Band → ℝ) : Band → ℝ :=
  sharpOperator M.normalizedDiagonalCell M.normalizedKernelCell M.center q

/-- Failure of the piecewise-center physical vector to be the exact
continuum null vector.  This is an explicit mesh remainder. -/
def rowResidual (i : Band) : ℝ :=
  M.normalizedDiagonalCell i +
    ∑ j, M.normalizedKernelCell i j * (M.center j / M.center i)

theorem continuumSharpOperator_eq_graph_add_residual
    (q : Band → ℝ) (i : Band) :
    M.continuumSharpOperator q i =
      FiniteGraphQuotientInverse.graphOperator M.sharpKernelEdge q i +
        M.rowResidual i * q i := by
  unfold continuumSharpOperator sharpOperator rowResidual
  have hedge (j : Band) :
      M.normalizedKernelCell i j * (M.center j / M.center i) =
        -M.sharpKernelEdge i j := by
    rw [M.sharpKernelEdge_eq_normalizedKernelCell]
    ring
  simp_rw [hedge]
  unfold FiniteGraphQuotientInverse.graphOperator
  have hgraph :
      (∑ j, M.sharpKernelEdge i j * (q i - q j)) =
        (∑ j, M.sharpKernelEdge i j) * q i -
          ∑ j, M.sharpKernelEdge i j * q j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hsumneg :
      (∑ x, (-M.sharpKernelEdge i x) * q x) =
        -(∑ x, M.sharpKernelEdge i x * q x) := by
    calc
      _ = ∑ x, -(M.sharpKernelEdge i x * q x) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := by simp
  have hedgeneg :
      (∑ x, -M.sharpKernelEdge i x) =
        -(∑ x, M.sharpKernelEdge i x) := by simp
  rw [hgraph, hsumneg, hedgeneg]
  ring

/-- Total sharp row budget: normalized quadrature, arithmetic/continuum
center comparison, and the explicit piecewise-center residual. -/
def arithmeticGraphRowBudget
    (diagonalError : Band → ℝ)
    (kernelError centerRatioError : Band → Band → ℝ)
    (alpha : Band → ℝ) (i : Band) : ℝ :=
  diagonalError i +
    (∑ j, kernelError i j * |alpha j / alpha i|) +
    (∑ j, |M.normalizedKernelCell i j| * centerRatioError i j) +
    |M.rowResidual i|

/-- The complete pointwise arithmetic-to-graph estimate. -/
theorem abs_arithmeticSharp_sub_graph_le
    (diagonalA diagonalError : Band → ℝ)
    (kernelA kernelError centerRatioError : Band → Band → ℝ)
    (alpha q : Band → ℝ) (B : ℝ)
    (hq : ∀ j, |q j| ≤ B)
    (hDiagonal : ∀ i,
      |diagonalA i - M.normalizedDiagonalCell i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j)
    (hCenter : ∀ i j,
      |alpha j / alpha i - M.center j / M.center i| ≤
        centerRatioError i j)
    (i : Band) :
    |sharpOperator diagonalA kernelA alpha q i -
        FiniteGraphQuotientInverse.graphOperator
          M.sharpKernelEdge q i| ≤
      B * M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i := by
  have hfirst := abs_sharpOperator_sub_le
    diagonalA M.normalizedDiagonalCell diagonalError
    kernelA M.normalizedKernelCell kernelError alpha q B hq
    hDiagonal hKernel i
  have hcenterStep :
      |sharpOperator M.normalizedDiagonalCell M.normalizedKernelCell alpha q i -
        M.continuumSharpOperator q i| ≤
      B * (∑ j,
        |M.normalizedKernelCell i j| * centerRatioError i j) := by
    unfold continuumSharpOperator sharpOperator
    have hsum :
        (∑ j, M.normalizedKernelCell i j * (alpha j / alpha i) * q j) -
            ∑ j, M.normalizedKernelCell i j *
              (M.center j / M.center i) * q j =
          ∑ j, M.normalizedKernelCell i j *
            ((alpha j / alpha i) - (M.center j / M.center i)) * q j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [show M.normalizedDiagonalCell i * q i +
        (∑ j, M.normalizedKernelCell i j * (alpha j / alpha i) * q j) -
        (M.normalizedDiagonalCell i * q i +
          ∑ j, M.normalizedKernelCell i j *
            (M.center j / M.center i) * q j) =
      ((∑ j, M.normalizedKernelCell i j * (alpha j / alpha i) * q j) -
        ∑ j, M.normalizedKernelCell i j *
          (M.center j / M.center i) * q j) by ring, hsum]
    calc
      |∑ j, M.normalizedKernelCell i j *
          (alpha j / alpha i - M.center j / M.center i) * q j| ≤
          ∑ j, |M.normalizedKernelCell i j *
            (alpha j / alpha i - M.center j / M.center i) * q j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |M.normalizedKernelCell i j| *
          centerRatioError i j * B := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul]
        have hcenterNonneg : 0 ≤ centerRatioError i j :=
          (abs_nonneg _).trans (hCenter i j)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hCenter i j)
            (abs_nonneg (M.normalizedKernelCell i j)))
          (hq j) (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) hcenterNonneg)
      _ = B * (∑ j,
          |M.normalizedKernelCell i j| * centerRatioError i j) := by
        rw [← Finset.sum_mul]
        ring
  have hresidual :
      |M.continuumSharpOperator q i -
          FiniteGraphQuotientInverse.graphOperator
            M.sharpKernelEdge q i| ≤ B * |M.rowResidual i| := by
    rw [M.continuumSharpOperator_eq_graph_add_residual]
    simp only [add_sub_cancel_left, abs_mul]
    calc
      |M.rowResidual i| * |q i| ≤ |M.rowResidual i| * B :=
        mul_le_mul_of_nonneg_left (hq i) (abs_nonneg (M.rowResidual i))
      _ = B * |M.rowResidual i| := by ring
  calc
    |sharpOperator diagonalA kernelA alpha q i -
        FiniteGraphQuotientInverse.graphOperator
          M.sharpKernelEdge q i| ≤
      |sharpOperator diagonalA kernelA alpha q i -
        sharpOperator M.normalizedDiagonalCell
          M.normalizedKernelCell alpha q i| +
      |sharpOperator M.normalizedDiagonalCell
          M.normalizedKernelCell alpha q i -
        M.continuumSharpOperator q i| +
      |M.continuumSharpOperator q i -
        FiniteGraphQuotientInverse.graphOperator
          M.sharpKernelEdge q i| := by
      calc
        _ ≤ |sharpOperator diagonalA kernelA alpha q i -
            sharpOperator M.normalizedDiagonalCell
              M.normalizedKernelCell alpha q i| +
            |sharpOperator M.normalizedDiagonalCell
              M.normalizedKernelCell alpha q i -
              FiniteGraphQuotientInverse.graphOperator
                M.sharpKernelEdge q i| := abs_sub_le _ _ _
        _ ≤ _ := by
          have htriangle := abs_sub_le
            (sharpOperator M.normalizedDiagonalCell
              M.normalizedKernelCell alpha q i)
            (M.continuumSharpOperator q i)
            (FiniteGraphQuotientInverse.graphOperator
              M.sharpKernelEdge q i)
          linarith
    _ ≤ B * (diagonalError i +
          ∑ j, kernelError i j * |alpha j / alpha i|) +
        B * (∑ j,
          |M.normalizedKernelCell i j| * centerRatioError i j) +
        B * |M.rowResidual i| :=
      add_le_add (add_le_add hfirst hcenterStep) hresidual
    _ = B * M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i := by
      unfold arithmeticGraphRowBudget
      ring

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
