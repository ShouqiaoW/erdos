import Erdos390.Full.ArithmeticGaugeStableInverse
import Erdos390.Full.EndpointContinuumMeshIdentification

/-!
# Eventual arithmetic-gauge inverse without a smallness hypothesis

Once the proved endpoint estimates give convergence of the complete sharp
row budget, the Dickman graph gap itself supplies a numerical target.  This
module chooses that target and proves the StableInverse inequality
automatically.  Thus no `r` or `C*r < 1` assumption remains in the eventual
inverse statement.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ArithmeticGaugeStableInverseAsymptotic

open CompressedArithmeticOperator
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open FiniteGraphStableInverse
open ArithmeticGaugeStableInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band] [Nonempty Band]

/-- Complete endpoint row-budget convergence implies eventual invertibility
on each exact arithmetic gauge.  The threshold is chosen only after the
mesh-independent Dickman edge constant has been produced. -/
theorem eventually_exists_stable_arithmetic_inverse
    {epsilon : ℝ} (M : IntervalMesh epsilon Band)
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (diagonalA diagonalError : ℕ → Band → ℝ)
    (kernelA kernelError centerRatioError :
      ℕ → Band → Band → ℝ)
    (alpha omega : ℕ → Band → ℝ)
    (homega : ∀ n i, 0 ≤ omega n i)
    (homegaTotal : ∀ n, 0 < ∑ i, omega n i)
    (hDiagonal : ∀ n i,
      |diagonalA n i - M.normalizedDiagonalCell i| ≤ diagonalError n i)
    (hKernel : ∀ n i j,
      |kernelA n i j - M.normalizedKernelCell i j| ≤ kernelError n i j)
    (hCenter : ∀ n i j,
      |alpha n j / alpha n i - M.center j / M.center i| ≤
        centerRatioError n i j)
    (hBudgetConverges : ∀ target : ℝ, 0 < target →
      ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ i,
        M.arithmeticGraphRowBudget (diagonalError n) (kernelError n)
          (centerRatioError n) (alpha n) i ≤ target) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∃ actualEquiv : GaugeSpace (omega n) ≃L[ℝ] GaugeSpace (omega n),
        (∀ q, actualEquiv q =
          projectedSharpCLM (diagonalA n) (kernelA n) (alpha n) (omega n)
            (ne_of_gt (homegaTotal n)) q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤
          ((4 / (kappa * ∑ j, M.anchor j)) /
            (1 - (4 / (kappa * ∑ j, M.anchor j)) *
              (2 * (kappa * (∑ j, M.anchor j) / 16)))) * ‖v‖ := by
  obtain ⟨kappa, hkappa, hedge, hdom, hanchorTotal⟩ :=
    M.exists_sharpKernelEdge_geometry hepsilon hhalf
  let target := kappa * (∑ j, M.anchor j) / 16
  have htarget : 0 < target := by
    dsimp only [target]
    positivity
  obtain ⟨n₀, hn₀⟩ := hBudgetConverges target htarget
  refine ⟨kappa, hkappa, n₀, ?_⟩
  intro n hn
  have hsmall :
      (4 / (kappa * ∑ j, M.anchor j)) * (2 * target) < 1 := by
    dsimp only [target]
    have hden : kappa * (∑ j, M.anchor j) ≠ 0 := by positivity
    field_simp [hden]
    nlinarith [mul_pos hkappa hanchorTotal]
  apply exists_actualGaugeEquiv_of_graph_error
    M.sharpKernelEdge M.anchor (omega n) hedge hdom hkappa hanchorTotal
      (homega n) (homegaTotal n)
      (projectedSharpCLM (diagonalA n) (kernelA n) (alpha n) (omega n)
        (ne_of_gt (homegaTotal n))) hsmall
  intro q
  exact projectedSharpCLM_sub_reference_bound M
    (diagonalA n) (diagonalError n) (kernelA n) (kernelError n)
    (centerRatioError n) (alpha n) (omega n) target
    (homega n) (homegaTotal n) htarget.le (hDiagonal n) (hKernel n)
    (hCenter n) (hn₀ n hn) M.anchor hedge hdom hkappa hanchorTotal q

/-! ## Full order of asymptotic choices -/

/-- A reusable four-stage quantifier lemma.  The cutoff is chosen first,
then the continuum tolerances, then an arbitrary box/mesh object, and only
the final arithmetic threshold may depend on that object. -/
theorem choose_cutoff_tolerances_before_box_mesh
    {BoxMesh : Type*}
    (cutoffError : ℕ → ℝ)
    (remainder : ℕ → ℝ → ℝ → BoxMesh → ℕ → ℝ)
    (gap : ℝ) (hgap : 0 < gap)
    (hcutoff : ∀ target : ℝ, 0 < target →
      ∃ W : ℕ, 0 < W ∧ |cutoffError W| < target)
    (hremainder : ∀ W delta eta boxMesh target,
      0 < target → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        |remainder W delta eta boxMesh n| < target) :
    ∃ W : ℕ, 0 < W ∧ |cutoffError W| < gap / 4 ∧
      ∃ delta : ℝ, 0 < delta ∧ delta < gap / 4 ∧
      ∃ eta : ℝ, 0 < eta ∧ eta < gap / 4 ∧
        ∀ boxMesh, ∃ n₀ : ℕ, ∀ n ≥ n₀,
          |remainder W delta eta boxMesh n| < gap / 4 := by
  have hquarter : 0 < gap / 4 := div_pos hgap (by norm_num)
  obtain ⟨W, hW, hcut⟩ := hcutoff (gap / 4) hquarter
  refine ⟨W, hW, hcut, gap / 8, div_pos hgap (by norm_num),
    by linarith, gap / 8, div_pos hgap (by norm_num), by linarith, ?_⟩
  intro boxMesh
  exact hremainder W (gap / 8) (gap / 8) boxMesh (gap / 4) hquarter

end Erdos390.Full.ArithmeticGaugeStableInverseAsymptotic
