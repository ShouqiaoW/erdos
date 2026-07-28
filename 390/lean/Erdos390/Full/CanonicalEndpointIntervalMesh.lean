import Erdos390.Full.CanonicalRegularMeshEndpointFamily
import Erdos390.Full.ContinuumCellGraph
import Erdos390.Full.DoubleKernelPrimeQuadrature

/-!
# The exact endpoint interval mesh

The cells use the literal natural cutoffs, including the final cutoff
`floor y`.  A selected positive cell supplies the interior anchor.  The
resulting mesh is therefore exactly the one used by endpoint quadrature;
its upper endpoint is not silently replaced by `1`.
-/

open Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Exact logarithmic-coordinate interval mesh of the canonical natural
cutoffs.  The two interior inequalities are the only anchor inputs. -/
def canonicalIntervalMesh
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower : epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M anchorCell) : ℝ))
    (hInteriorUpper :
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon) :
    IntervalMesh epsilon (Fin (M.cellCount + 1)) where
  lower j := realLogCoordinate (y n)
    ((canonicalCertificate M hdelta hn hW S).lower j : ℝ)
  upper j := realLogCoordinate (y n)
    ((canonicalCertificate M hdelta hn hW S).upper j : ℝ)
  lower_pos j := by
    apply realLogCoordinate_pos_nat
    · have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog
    · exact hWTwo.trans
        (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S j)
  lower_lt_upper j := by
    let E := canonicalCertificate M hdelta hn hW S
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      every_fullCutoff_cell_has_prime M hW S j
    have hCut : E.lower j < E.upper j := by
      change fullCutoff M n W j.1 < fullCutoff M n W (j.1 + 1)
      exact hpLower.trans_le hpUpper
    have hLowerPos : (0 : ℝ) < (E.lower j : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W)
        (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S j))
    have hUpperPos : (0 : ℝ) < (E.upper j : ℝ) :=
      hLowerPos.trans (by exact_mod_cast hCut)
    have hlogStrict : Real.log (E.lower j : ℝ) <
        Real.log (E.upper j : ℝ) :=
      Real.strictMonoOn_log
        hLowerPos hUpperPos
        (by exact_mod_cast hCut)
    unfold realLogCoordinate
    exact div_lt_div_of_pos_right hlogStrict (by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num)
        (Real.log_pos (by exact_mod_cast hn)))
  upper_le_one j := by
    let E := canonicalCertificate M hdelta hn hW S
    have hypos : 0 < y n := Scale.y_pos (Nat.zero_lt_of_lt hn)
    have hUpperPos : (0 : ℝ) < (E.upper j : ℝ) := by
      have hLower := canonicalCertificate_lower_ge_cutoff
        M hdelta hn hW S j
      have hle := E.lower_le_upper j
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W) (hLower.trans hle))
    have hUpperY : (E.upper j : ℝ) ≤ y n := by
      exact (by exact_mod_cast E.upper_le_yNat j :
        (E.upper j : ℝ) ≤ (yNat n : ℝ)) |>.trans
          (Nat.floor_le hypos.le)
    unfold realLogCoordinate
    apply (div_le_iff₀ (Real.log_pos (by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff hypos.le).mp hlog))).2
    simpa only [one_mul] using Real.log_le_log hUpperPos hUpperY
  interiorCells := {positiveBand M anchorCell}
  interior_lower j hj := by
    have hjEq : j = positiveBand M anchorCell := by simpa using hj
    simpa only [hjEq] using hInteriorLower
  interior_upper j hj := by
    have hjEq : j = positiveBand M anchorCell := by simpa using hj
    simpa only [hjEq] using hInteriorUpper
  interiorTotal_pos := by
    simp only [Finset.sum_singleton]
    exact sub_pos.mpr (by
      let E := canonicalCertificate M hdelta hn hW S
      obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
        every_fullCutoff_cell_has_prime M hW S (positiveBand M anchorCell)
      have hCut : E.lower (positiveBand M anchorCell) <
          E.upper (positiveBand M anchorCell) := by
        change fullCutoff M n W (anchorCell.1 + 1) <
          fullCutoff M n W (anchorCell.1 + 1 + 1)
        exact hpLower.trans_le hpUpper
      have hLowerPos : (0 : ℝ) <
          (E.lower (positiveBand M anchorCell) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W)
          (canonicalCertificate_lower_ge_cutoff M hdelta hn hW S _))
      have hUpperPos : (0 : ℝ) <
          (E.upper (positiveBand M anchorCell) : ℝ) :=
        hLowerPos.trans (by exact_mod_cast hCut)
      unfold realLogCoordinate
      exact div_lt_div_of_pos_right
        (Real.strictMonoOn_log hLowerPos hUpperPos (by exact_mod_cast hCut))
        (by
          rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
          exact mul_pos (by norm_num)
            (Real.log_pos (by exact_mod_cast hn))))

@[simp] theorem canonicalIntervalMesh_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower hInteriorUpper) (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).lower j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower j : ℝ) := rfl

@[simp] theorem canonicalIntervalMesh_upper
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower hInteriorUpper) (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).upper j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper j : ℝ) := rfl

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
