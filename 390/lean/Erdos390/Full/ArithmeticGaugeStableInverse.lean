import Erdos390.Full.ContinuumSharpArithmeticTransfer

/-!
# Stable inversion of the compressed arithmetic operator

The actual sharp arithmetic matrix is projected to its weighted gauge and
compared directly with the positive continuum cell graph.  The graph gap is
obtained from the Dickman kernel; it is not supplied as an inverse or
coercivity hypothesis.  Every arithmetic error is quantified row by row,
including the moving low cell.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ArithmeticGaugeStableInverse

open CompressedArithmeticOperator
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse

variable {Band : Type*} [Fintype Band]

lemma sharpOperator_add
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q r : Band → ℝ) (i : Band) :
    sharpOperator diagonal kernel alpha (q + r) i =
      sharpOperator diagonal kernel alpha q i +
        sharpOperator diagonal kernel alpha r i := by
  unfold sharpOperator
  simp only [Pi.add_apply]
  have hsum :
      (∑ j, kernel i j * (alpha j / alpha i) * (q j + r j)) =
        (∑ j, kernel i j * (alpha j / alpha i) * q j) +
          ∑ j, kernel i j * (alpha j / alpha i) * r j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum]
  ring

lemma sharpOperator_smul
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q : Band → ℝ) (c : ℝ) (i : Band) :
    sharpOperator diagonal kernel alpha (c • q) i =
      c * sharpOperator diagonal kernel alpha q i := by
  unfold sharpOperator
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ j, kernel i j * (alpha j / alpha i) * (c * q j)) =
        c * ∑ j, kernel i j * (alpha j / alpha i) * q j := by
    calc
      _ = ∑ j, c * (kernel i j * (alpha j / alpha i) * q j) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := by rw [Finset.mul_sum]
  rw [hsum]
  ring

/-- The actual sharp arithmetic matrix, followed by projection to the exact
arithmetic weighted gauge. -/
def projectedSharpLinearMap
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha omega : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    GaugeSpace omega →ₗ[ℝ] GaugeSpace omega where
  toFun q :=
    ⟨meanProjection omega
        (sharpOperator diagonal kernel alpha (q : Band → ℝ)),
      weighted_sum_meanProjection omega
        (sharpOperator diagonal kernel alpha (q : Band → ℝ)) hTotal⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (sharpOperator diagonal kernel alpha
          ((q : Band → ℝ) + (r : Band → ℝ))) i =
      meanProjection omega
          (sharpOperator diagonal kernel alpha (q : Band → ℝ)) i +
        meanProjection omega
          (sharpOperator diagonal kernel alpha (r : Band → ℝ)) i
    rw [show sharpOperator diagonal kernel alpha
        ((q : Band → ℝ) + (r : Band → ℝ)) =
        sharpOperator diagonal kernel alpha (q : Band → ℝ) +
          sharpOperator diagonal kernel alpha (r : Band → ℝ) by
      funext j
      exact sharpOperator_add diagonal kernel alpha
        (q : Band → ℝ) (r : Band → ℝ) j]
    exact meanProjection_add omega _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (sharpOperator diagonal kernel alpha (c • (q : Band → ℝ))) i =
      c * meanProjection omega
        (sharpOperator diagonal kernel alpha (q : Band → ℝ)) i
    rw [show sharpOperator diagonal kernel alpha
        (c • (q : Band → ℝ)) =
        c • sharpOperator diagonal kernel alpha (q : Band → ℝ) by
      funext j
      exact sharpOperator_smul diagonal kernel alpha
        (q : Band → ℝ) c j]
    exact meanProjection_smul omega c _ i

def projectedSharpCLM
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha omega : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    GaugeSpace omega →L[ℝ] GaugeSpace omega :=
  (projectedSharpLinearMap diagonal kernel alpha omega hTotal).toContinuousLinearMap

/-- A uniform sharp row budget gives the operator-norm error needed by
`StableInverse`.  The factor two is exactly the weighted gauge projection
cost and is independent of the number and shape of cells. -/
theorem projectedSharpCLM_sub_reference_bound
    [Nonempty Band]
    {epsilon : ℝ} (M : IntervalMesh epsilon Band)
    (diagonalA diagonalError : Band → ℝ)
    (kernelA kernelError centerRatioError : Band → Band → ℝ)
    (alpha omega : Band → ℝ) (r : ℝ)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (hr : 0 ≤ r)
    (hDiagonal : ∀ i,
      |diagonalA i - M.normalizedDiagonalCell i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j)
    (hCenter : ∀ i j,
      |alpha j / alpha i - M.center j / M.center i| ≤
        centerRatioError i j)
    (hBudget : ∀ i,
      M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i ≤ r)
    (anchor : Band → ℝ) {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ M.sharpKernelEdge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ M.sharpKernelEdge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (q : GaugeSpace omega) :
    ‖(projectedSharpCLM diagonalA kernelA alpha omega
          (ne_of_gt homegaTotal) -
        referenceGraphCLM M.sharpKernelEdge anchor omega hedge hdom
          hkappa hanchorTotal homega homegaTotal) q‖ ≤
      (2 * r) * ‖q‖ := by
  have hraw (i : Band) :
      |sharpOperator diagonalA kernelA alpha (q : Band → ℝ) i -
          graphOperator M.sharpKernelEdge (q : Band → ℝ) i| ≤
        r * ‖(q : Band → ℝ)‖ := by
    calc
      _ ≤ ‖(q : Band → ℝ)‖ *
          M.arithmeticGraphRowBudget diagonalError kernelError
            centerRatioError alpha i :=
        M.abs_arithmeticSharp_sub_graph_le diagonalA diagonalError
          kernelA kernelError centerRatioError alpha (q : Band → ℝ)
          ‖(q : Band → ℝ)‖
          (fun j => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (q : Band → ℝ) j)
          hDiagonal hKernel hCenter i
      _ ≤ ‖(q : Band → ℝ)‖ * r :=
        mul_le_mul_of_nonneg_left (hBudget i) (norm_nonneg _)
      _ = r * ‖(q : Band → ℝ)‖ := by ring
  have hprojected (i : Band) :
      |meanProjection omega
          (sharpOperator diagonalA kernelA alpha (q : Band → ℝ)) i -
        meanProjection omega
          (graphOperator M.sharpKernelEdge (q : Band → ℝ)) i| ≤
        2 * (r * ‖(q : Band → ℝ)‖) :=
    abs_meanProjection_sub_le omega
      (sharpOperator diagonalA kernelA alpha (q : Band → ℝ))
      (graphOperator M.sharpKernelEdge (q : Band → ℝ))
      (r * ‖(q : Band → ℝ)‖) homega homegaTotal hraw i
  have hnonneg : 0 ≤ (2 * r) * ‖q‖ :=
    mul_nonneg (mul_nonneg (by norm_num) hr) (norm_nonneg q)
  change ‖((projectedSharpCLM diagonalA kernelA alpha omega
          (ne_of_gt homegaTotal) -
        referenceGraphCLM M.sharpKernelEdge anchor omega hedge hdom
          hkappa hanchorTotal homega homegaTotal) q :
      GaugeSpace omega)‖ ≤ (2 * r) * ‖q‖
  change ‖(((projectedSharpCLM diagonalA kernelA alpha omega
          (ne_of_gt homegaTotal) -
        referenceGraphCLM M.sharpKernelEdge anchor omega hedge hdom
          hkappa hanchorTotal homega homegaTotal) q :
      GaugeSpace omega) : Band → ℝ)‖ ≤ (2 * r) * ‖q‖
  rw [pi_norm_le_iff_of_nonneg hnonneg]
  intro i
  rw [Real.norm_eq_abs]
  change |meanProjection omega
          (sharpOperator diagonalA kernelA alpha (q : Band → ℝ)) i -
        meanProjection omega
          (graphOperator M.sharpKernelEdge (q : Band → ℝ)) i| ≤
      (2 * r) * ‖q‖
  calc
    _ ≤ 2 * (r * ‖(q : Band → ℝ)‖) := hprojected i
    _ = (2 * r) * ‖q‖ := by simp [mul_assoc]

/-- The Dickman cell gap and all-cell row error together yield a stable
inverse on the exact arithmetic gauge.  The selected `kappa` is produced
before the small-error condition is invoked, making the quantifier order
explicit. -/
theorem exists_geometry_and_stable_arithmetic_inverse
    [Nonempty Band] [DecidableEq Band]
    {epsilon : ℝ} (M : IntervalMesh epsilon Band)
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (diagonalA diagonalError : Band → ℝ)
    (kernelA kernelError centerRatioError : Band → Band → ℝ)
    (alpha omega : Band → ℝ) (r : ℝ)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (hr : 0 ≤ r)
    (hDiagonal : ∀ i,
      |diagonalA i - M.normalizedDiagonalCell i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j)
    (hCenter : ∀ i j,
      |alpha j / alpha i - M.center j / M.center i| ≤
        centerRatioError i j)
    (hBudget : ∀ i,
      M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i ≤ r) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ((4 / (kappa * ∑ j, M.anchor j)) * (2 * r) < 1 →
        ∃ actualEquiv : GaugeSpace omega ≃L[ℝ] GaugeSpace omega,
          (∀ q, actualEquiv q =
            projectedSharpCLM diagonalA kernelA alpha omega
              (ne_of_gt homegaTotal) q) ∧
          ∀ v, ‖actualEquiv.symm v‖ ≤
            ((4 / (kappa * ∑ j, M.anchor j)) /
              (1 - (4 / (kappa * ∑ j, M.anchor j)) * (2 * r))) *
                ‖v‖) := by
  obtain ⟨kappa, hkappa, hedge, hdom, hanchorTotal⟩ :=
    M.exists_sharpKernelEdge_geometry hepsilon hhalf
  refine ⟨kappa, hkappa, ?_⟩
  intro hsmall
  apply exists_actualGaugeEquiv_of_graph_error
    M.sharpKernelEdge M.anchor omega hedge hdom hkappa hanchorTotal
      homega homegaTotal
      (projectedSharpCLM diagonalA kernelA alpha omega
        (ne_of_gt homegaTotal)) hsmall
  intro q
  exact projectedSharpCLM_sub_reference_bound M
    diagonalA diagonalError kernelA kernelError centerRatioError
    alpha omega r homega homegaTotal hr hDiagonal hKernel hCenter hBudget
    M.anchor hedge hdom hkappa hanchorTotal q

end Erdos390.Full.ArithmeticGaugeStableInverse
