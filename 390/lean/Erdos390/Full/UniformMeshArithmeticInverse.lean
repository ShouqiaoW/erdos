import Erdos390.Full.ArithmeticGaugeStableInverse

/-!
# Mesh-uniform arithmetic inversion from the Dickman gap

The Dickman kernel gap is selected before any finite mesh.  Given that
single gap and a positive lower bound for the mesh's interior anchor mass,
the displayed row budget below automatically satisfies the Neumann-series
smallness condition.  Thus the finite dimension and the locations of the
moving cells do not enter the perturbative constant.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.UniformMeshArithmeticInverse

open CompressedArithmeticOperator
open ConditionedPoissonLimit
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open ArithmeticGaugeStableInverse
open FiniteGraphStableInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band]

/-- A mesh-independent Dickman gap and a uniform anchor-mass floor make the
stable-inverse inequality automatic.  The only approximation hypothesis is
the complete, explicit arithmetic graph row budget. -/
theorem exists_stable_arithmetic_inverse_of_uniform_gap
    {epsilon kappa anchorFloor : ℝ}
    (hkappa : 0 < kappa)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (hAnchorFloor : 0 < anchorFloor)
    (M : IntervalMesh epsilon Band)
    (hAnchorMass : anchorFloor ≤ ∑ j, M.anchor j)
    (diagonalA diagonalError : Band → ℝ)
    (kernelA kernelError centerRatioError : Band → Band → ℝ)
    (alpha omega : Band → ℝ)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (hDiagonal : ∀ i,
      |diagonalA i - M.normalizedDiagonalCell i| ≤ diagonalError i)
    (hKernel : ∀ i j,
      |kernelA i j - M.normalizedKernelCell i j| ≤ kernelError i j)
    (hCenter : ∀ i j,
      |alpha j / alpha i - M.center j / M.center i| ≤
        centerRatioError i j)
    (hBudget : ∀ i,
      M.arithmeticGraphRowBudget diagonalError kernelError
        centerRatioError alpha i ≤ kappa * anchorFloor / 16) :
    ∃ actualEquiv : GaugeSpace omega ≃L[ℝ] GaugeSpace omega,
      (∀ q, actualEquiv q =
        projectedSharpCLM diagonalA kernelA alpha omega
          (ne_of_gt homegaTotal) q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        ((4 / (kappa * ∑ j, M.anchor j)) /
          (1 - (4 / (kappa * ∑ j, M.anchor j)) *
            (2 * (kappa * anchorFloor / 16)))) * ‖v‖ := by
  have hedge : ∀ i j, 0 ≤ M.sharpKernelEdge i j :=
    M.sharpKernelEdge_nonneg
  have hdom : ∀ i j,
      kappa * M.anchor j ≤ M.sharpKernelEdge i j :=
    M.gap_mul_anchor_le_sharpKernelEdge hgap
  have hanchorTotal : 0 < ∑ j, M.anchor j := M.sum_anchor_pos
  let r := kappa * anchorFloor / 16
  have hr : 0 ≤ r := by
    dsimp only [r]
    positivity
  have hsmall :
      (4 / (kappa * ∑ j, M.anchor j)) * (2 * r) < 1 := by
    have hk0 : kappa ≠ 0 := ne_of_gt hkappa
    have hs0 : (∑ j, M.anchor j) ≠ 0 := ne_of_gt hanchorTotal
    have heq :
        (4 / (kappa * ∑ j, M.anchor j)) * (2 * r) =
          anchorFloor / (2 * ∑ j, M.anchor j) := by
      dsimp only [r]
      field_simp [hk0, hs0]
      ring
    rw [heq]
    have hhalf : anchorFloor / (2 * ∑ j, M.anchor j) ≤ 1 / 2 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) hanchorTotal)).2
      nlinarith
    exact hhalf.trans_lt (by norm_num)
  apply exists_actualGaugeEquiv_of_graph_error
    M.sharpKernelEdge M.anchor omega hedge hdom hkappa hanchorTotal
      homega homegaTotal
      (projectedSharpCLM diagonalA kernelA alpha omega
        (ne_of_gt homegaTotal)) hsmall
  intro q
  exact projectedSharpCLM_sub_reference_bound M
    diagonalA diagonalError kernelA kernelError centerRatioError
    alpha omega r homega homegaTotal hr hDiagonal hKernel hCenter
    (by simpa only [r] using hBudget) M.anchor hedge hdom hkappa
    hanchorTotal q

end Erdos390.Full.UniformMeshArithmeticInverse
