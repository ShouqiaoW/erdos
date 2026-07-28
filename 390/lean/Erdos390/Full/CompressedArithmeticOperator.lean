import Erdos390.Full.DiagonalPrimeQuadrature
import Erdos390.Full.FiniteGraphQuotientInverse

/-!
# The actual compressed arithmetic operator

This file packages the diagonal and double-kernel cells used in the
arithmetic bridge, performs the sharp conjugation, and proves the complete
row aggregation estimate.  The moving low row is not discarded: its
normalization is exactly the one provided by the proved normalized
quadrature modules.

No inverse or spectral gap is an input here.  The output is the explicit
operator error that is fed to the finite graph inverse and then to
`StableInverse`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.CompressedArithmeticOperator

open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

/-- Sharp conjugation of a row-normalized diagonal/kernel matrix.  If `b_j`
is the unscaled band coefficient and `b_j = alpha_j q_j`, this is the output
after division by the output center `alpha_i`. -/
def sharpOperator (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q : Band → ℝ) (i : Band) : ℝ :=
  diagonal i * q i +
    ∑ j, kernel i j * (alpha j / alpha i) * q j

/-- The exact row budget produced by diagonal and kernel entry errors. -/
def rowErrorBudget (diagonalError : Band → ℝ)
    (kernelError : Band → Band → ℝ) (alpha : Band → ℝ)
    (i : Band) : ℝ :=
  diagonalError i + ∑ j, kernelError i j * |alpha j / alpha i|

lemma sharpOperator_sub
    (diagonalA diagonalC : Band → ℝ)
    (kernelA kernelC : Band → Band → ℝ)
    (alpha q : Band → ℝ) (i : Band) :
    sharpOperator diagonalA kernelA alpha q i -
        sharpOperator diagonalC kernelC alpha q i =
      (diagonalA i - diagonalC i) * q i +
        ∑ j, (kernelA i j - kernelC i j) *
          (alpha j / alpha i) * q j := by
  unfold sharpOperator
  have hsum :
      (∑ j, kernelA i j * (alpha j / alpha i) * q j) -
          ∑ j, kernelC i j * (alpha j / alpha i) * q j =
        ∑ j, (kernelA i j - kernelC i j) *
          (alpha j / alpha i) * q j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [show diagonalA i * q i +
        (∑ j, kernelA i j * (alpha j / alpha i) * q j) -
        (diagonalC i * q i +
          ∑ j, kernelC i j * (alpha j / alpha i) * q j) =
      (diagonalA i - diagonalC i) * q i +
        ((∑ j, kernelA i j * (alpha j / alpha i) * q j) -
          ∑ j, kernelC i j * (alpha j / alpha i) * q j) by ring]
  rw [hsum]

/-- Entrywise quadrature errors aggregate in the sharp row norm without any
hidden factor depending on the number of cells. -/
theorem abs_sharpOperator_sub_le
    (diagonalA diagonalC diagonalError : Band → ℝ)
    (kernelA kernelC kernelError : Band → Band → ℝ)
    (alpha q : Band → ℝ) (B : ℝ)
    (hq : ∀ j, |q j| ≤ B)
    (hDiagonal : ∀ i, |diagonalA i - diagonalC i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - kernelC i j| ≤ kernelError i j)
    (i : Band) :
    |sharpOperator diagonalA kernelA alpha q i -
        sharpOperator diagonalC kernelC alpha q i| ≤
      B * rowErrorBudget diagonalError kernelError alpha i := by
  rw [sharpOperator_sub]
  calc
    |(diagonalA i - diagonalC i) * q i +
        ∑ j, (kernelA i j - kernelC i j) *
          (alpha j / alpha i) * q j| ≤
      |(diagonalA i - diagonalC i) * q i| +
        |∑ j, (kernelA i j - kernelC i j) *
          (alpha j / alpha i) * q j| := abs_add_le _ _
    _ = |diagonalA i - diagonalC i| * |q i| +
        |∑ j, (kernelA i j - kernelC i j) *
          (alpha j / alpha i) * q j| := by rw [abs_mul]
    _ ≤ |diagonalA i - diagonalC i| * |q i| +
        ∑ j, |(kernelA i j - kernelC i j) *
          (alpha j / alpha i) * q j| := by
      exact add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ diagonalError i * B +
        ∑ j, kernelError i j * |alpha j / alpha i| * B := by
      apply add_le_add
      · exact mul_le_mul (hDiagonal i) (hq i) (abs_nonneg _)
          ((abs_nonneg _).trans (hDiagonal i))
      · apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul]
        have hkernelNonneg : 0 ≤ kernelError i j :=
          (abs_nonneg _).trans (hKernel i j)
        have hfactorNonneg :
            0 ≤ kernelError i j * |alpha j / alpha i| :=
          mul_nonneg hkernelNonneg (abs_nonneg _)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (hKernel i j)
            (abs_nonneg (alpha j / alpha i)))
          (hq j) (abs_nonneg _) hfactorNonneg
    _ = B * rowErrorBudget diagonalError kernelError alpha i := by
      unfold rowErrorBudget
      rw [← Finset.sum_mul]
      ring

/-! ## Endpoint-specialized arithmetic and continuum matrices -/

def arithmeticDiagonal (z : ℝ) (lower upper : Band → ℕ)
    (i : Band) : ℝ :=
  normalizedDiagonalPrimeCell z (lower i) (upper i)

def continuumDiagonal (z : ℝ) (lower upper : Band → ℕ)
    (i : Band) : ℝ :=
  normalizedDiagonalContinuumCell z (lower i) (upper i)

def arithmeticKernel (z : ℝ) (lower upper : Band → ℕ)
    (i j : Band) : ℝ :=
  normalizedDoublePrimeKernelCell z
    (lower i) (upper i) (lower j) (upper j)

def continuumKernel (z : ℝ) (lower upper : Band → ℕ)
    (i j : Band) : ℝ :=
  normalizedDoubleContinuumKernelCell z
    (lower i) (upper i) (lower j) (upper j)

def arithmeticSharpOperator (z : ℝ) (lower upper : Band → ℕ)
    (alpha q : Band → ℝ) : Band → ℝ :=
  sharpOperator (arithmeticDiagonal z lower upper)
    (arithmeticKernel z lower upper) alpha q

def continuumSharpOperator (z : ℝ) (lower upper : Band → ℕ)
    (alpha q : Band → ℝ) : Band → ℝ :=
  sharpOperator (continuumDiagonal z lower upper)
    (continuumKernel z lower upper) alpha q

/-- The full arithmetic-versus-continuum row estimate.  The two hypotheses
are exactly the outputs of normalized diagonal and double-kernel
quadrature; the conclusion performs the previously implicit row sum. -/
theorem abs_arithmeticSharpOperator_sub_continuum_le
    (z : ℝ) (lower upper : Band → ℕ)
    (alpha q diagonalError : Band → ℝ)
    (kernelError : Band → Band → ℝ) (B : ℝ)
    (hq : ∀ j, |q j| ≤ B)
    (hDiagonal : ∀ i,
      |arithmeticDiagonal z lower upper i -
        continuumDiagonal z lower upper i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |arithmeticKernel z lower upper i j -
        continuumKernel z lower upper i j| ≤ kernelError i j)
    (i : Band) :
    |arithmeticSharpOperator z lower upper alpha q i -
        continuumSharpOperator z lower upper alpha q i| ≤
      B * rowErrorBudget diagonalError kernelError alpha i := by
  exact abs_sharpOperator_sub_le
    (arithmeticDiagonal z lower upper)
    (continuumDiagonal z lower upper) diagonalError
    (arithmeticKernel z lower upper)
    (continuumKernel z lower upper) kernelError
    alpha q B hq hDiagonal hKernel i

/-! ## Projection to the actual arithmetic gauge -/

/-- A positive weighted projection costs at most a factor two in the
pointwise norm.  This applies to the actual sharp weights
`H_j alpha_j^2`, including the moving low band. -/
theorem abs_meanProjection_sub_le
    (omega x y : Band → ℝ) (R : ℝ)
    (homega : ∀ j, 0 ≤ omega j)
    (hTotal : 0 < ∑ j, omega j)
    (hxy : ∀ j, |x j - y j| ≤ R)
    (i : Band) :
    |meanProjection omega x i - meanProjection omega y i| ≤ 2 * R := by
  have htotal0 : (∑ j, omega j) ≠ 0 := ne_of_gt hTotal
  have hmean : |weightedMean omega x - weightedMean omega y| ≤ R := by
    have hidentity :
        weightedMean omega x - weightedMean omega y =
          (∑ j, omega j * (x j - y j)) / ∑ j, omega j := by
      unfold weightedMean weightTotal
      have hsum :
          (∑ j, omega j * x j) - ∑ j, omega j * y j =
            ∑ j, omega j * (x j - y j) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [show (∑ j, omega j * x j) / (∑ j, omega j) -
          (∑ j, omega j * y j) / (∑ j, omega j) =
          ((∑ j, omega j * x j) - ∑ j, omega j * y j) /
            (∑ j, omega j) by field_simp [htotal0]]
      rw [hsum]
    rw [hidentity, abs_div, abs_of_pos hTotal]
    apply (div_le_iff₀ hTotal).2
    calc
      |∑ j, omega j * (x j - y j)| ≤
          ∑ j, |omega j * (x j - y j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, omega j * R := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (homega j)]
        exact mul_le_mul_of_nonneg_left (hxy j) (homega j)
      _ = R * ∑ j, omega j := by
        rw [← Finset.sum_mul]
        ring
  unfold meanProjection
  calc
    |(x i - weightedMean omega x) -
        (y i - weightedMean omega y)| =
    |(x i - y i) -
          (weightedMean omega x - weightedMean omega y)| := by ring
    _ = |(x i - y i) +
        (-(weightedMean omega x - weightedMean omega y))| := by
      rw [sub_eq_add_neg]
    _ ≤ |x i - y i| +
        |-(weightedMean omega x - weightedMean omega y)| := abs_add_le _ _
    _ = |x i - y i| +
        |weightedMean omega x - weightedMean omega y| := by rw [abs_neg]
    _ ≤ R + R := add_le_add (hxy i) hmean
    _ = 2 * R := by ring

end Erdos390.Full.CompressedArithmeticOperator
