import Erdos390.Full.CanonicalEndpointDoubleKernelOrdinaryRowEventually
import Erdos390.Full.OrdinaryRawOperatorRowTransfer

/-!
# Canonical arithmetic/continuum transfer in ordinary raw row norm

The global PNT cutoff is chosen before both mesh parameters and before the
mesh.  The only fixed-cutoff remainder is `CRow / log(W)^3`; all other row
errors are absorbed by the later eventual threshold in `n`.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open CompressedArithmeticOperator PaperWeightedInverseExport

namespace Mesh

/-- Literal paper-order ordinary raw row transfer for the canonical endpoint
matrix.  The estimate applies to every coefficient vector, not merely to a
gauge subspace. -/
theorem exists_cutoff_before_mesh_eventually_canonical_ordinaryRawRowError :
    ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
      ∀ {delta eta : ℝ} (M : Mesh delta eta), 0 < delta →
      ∀ W : ℕ, W₀ ≤ W → ∀ e : ℝ, 0 < e →
        ∀ᶠ n : ℕ in atTop,
          ∃ _hW : W ≠ 0, ∃ _hn : 1 < n,
            ∃ _S : ScaleSeparation M n W,
              ∀ b : Fin (M.cellCount + 1) → ℝ,
              ∀ i : Fin (M.cellCount + 1),
                |rawOperator
                    (arithmeticDiagonal (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1)))
                    (arithmeticKernel (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1))) b i -
                  rawOperator
                    (continuumDiagonal (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1)))
                    (continuumKernel (y n)
                      (fun j ↦ fullCutoff M n W j.1)
                      (fun j ↦ fullCutoff M n W (j.1 + 1))) b i| ≤
                    (CRow / Real.log (W : ℝ) ^ 3 + e) * ‖b‖ := by
  obtain ⟨CRow, hCRow, WKernel, hKernel⟩ :=
    exists_cutoff_eventually_canonical_doubleKernelOrdinaryRowError
  obtain ⟨WDiagonal, hDiagonal⟩ :=
    exists_global_cutoff_eventually_canonical_diagonalError
  let W₀ : ℕ := max WKernel WDiagonal
  refine ⟨CRow, hCRow, W₀, ?_⟩
  intro delta eta M hdelta W hW e he
  have hWKernel : WKernel ≤ W :=
    (le_max_left WKernel WDiagonal).trans hW
  have hWDiagonal : WDiagonal ≤ W :=
    (le_max_right WKernel WDiagonal).trans hW
  have hKernelN := hKernel M hdelta W hWKernel (e / 2) (half_pos he)
  have hDiagonalN := hDiagonal M hdelta W hWDiagonal (e / 2) (half_pos he)
  filter_upwards [hKernelN, hDiagonalN] with n hKernelAt hDiagonalAt
  obtain ⟨hWne, hn, S, hKernelRows⟩ := hKernelAt
  refine ⟨hWne, hn, S, ?_⟩
  intro b i
  have hDiagonalEntry (r : Fin (M.cellCount + 1)) :
      |arithmeticDiagonal (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r -
        continuumDiagonal (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r| ≤
        endpointDiagonalError M n W r := le_rfl
  have hKernelEntry (r s : Fin (M.cellCount + 1)) :
      |arithmeticKernel (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r s -
        continuumKernel (y n)
          (fun j ↦ fullCutoff M n W j.1)
          (fun j ↦ fullCutoff M n W (j.1 + 1)) r s| ≤
        endpointDoubleKernelError M n W r s := le_rfl
  have hRaw := abs_rawOperator_sub_le
    (arithmeticDiagonal (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (continuumDiagonal (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (endpointDiagonalError M n W)
    (arithmeticKernel (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (continuumKernel (y n)
      (fun j ↦ fullCutoff M n W j.1)
      (fun j ↦ fullCutoff M n W (j.1 + 1)))
    (endpointDoubleKernelError M n W) b
    hDiagonalEntry hKernelEntry i
  calc
    |rawOperator
          (arithmeticDiagonal (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1)))
          (arithmeticKernel (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1))) b i -
        rawOperator
          (continuumDiagonal (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1)))
          (continuumKernel (y n)
            (fun j ↦ fullCutoff M n W j.1)
            (fun j ↦ fullCutoff M n W (j.1 + 1))) b i| ≤
      (endpointDiagonalError M n W i +
        ∑ j, endpointDoubleKernelError M n W i j) * ‖b‖ := hRaw
    _ ≤ (CRow / Real.log (W : ℝ) ^ 3 + e) * ‖b‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg b)
      have hDiag := hDiagonalAt i
      have hKer := hKernelRows i
      linarith

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
