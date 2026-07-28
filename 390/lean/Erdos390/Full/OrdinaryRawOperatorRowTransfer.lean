import Erdos390.Full.PaperWeightedInverseExport

/-!
# Entrywise transfer in ordinary raw row norm

This is the centre-free analogue of the sharp row aggregation lemma.  It
is deliberately stated for arbitrary finite matrices, so every later
endpoint attachment uses the same auditable deterministic estimate.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]

lemma rawOperator_sub
    (diagonalA diagonalC : Band → ℝ)
    (kernelA kernelC : Band → Band → ℝ)
    (b : Band → ℝ) (i : Band) :
    rawOperator diagonalA kernelA b i -
        rawOperator diagonalC kernelC b i =
      (diagonalA i - diagonalC i) * b i +
        ∑ j, (kernelA i j - kernelC i j) * b j := by
  unfold rawOperator
  rw [show diagonalA i * b i + (∑ j, kernelA i j * b j) -
      (diagonalC i * b i + ∑ j, kernelC i j * b j) =
    (diagonalA i - diagonalC i) * b i +
      ((∑ j, kernelA i j * b j) - ∑ j, kernelC i j * b j) by ring]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (fun x : ℝ ↦ (diagonalA i - diagonalC i) * b i + x)
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Entrywise diagonal and kernel errors aggregate in raw sup norm with no
centre ratio and no factor depending on the number of cells. -/
theorem abs_rawOperator_sub_le
    (diagonalA diagonalC diagonalError : Band → ℝ)
    (kernelA kernelC kernelError : Band → Band → ℝ)
    (b : Band → ℝ)
    (hDiagonal : ∀ i,
      |diagonalA i - diagonalC i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - kernelC i j| ≤ kernelError i j)
    (i : Band) :
    |rawOperator diagonalA kernelA b i -
        rawOperator diagonalC kernelC b i| ≤
      (diagonalError i + ∑ j, kernelError i j) * ‖b‖ := by
  rw [rawOperator_sub]
  calc
    |(diagonalA i - diagonalC i) * b i +
        ∑ j, (kernelA i j - kernelC i j) * b j| ≤
      |(diagonalA i - diagonalC i) * b i| +
        ∑ j, |(kernelA i j - kernelC i j) * b j| := by
          exact (abs_add_le _ _).trans
            (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    _ ≤ diagonalError i * ‖b‖ +
        ∑ j, kernelError i j * ‖b‖ := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul (hDiagonal i)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b i)
          (abs_nonneg _) ((abs_nonneg _).trans (hDiagonal i))
      · apply Finset.sum_le_sum
        intro j _hj
        rw [abs_mul]
        exact mul_le_mul (hKernel i j)
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b j)
          (abs_nonneg _) ((abs_nonneg _).trans (hKernel i j))
    _ = (diagonalError i + ∑ j, kernelError i j) * ‖b‖ := by
      rw [← Finset.sum_mul]
      ring

end Erdos390.Full.PaperWeightedInverseExport
