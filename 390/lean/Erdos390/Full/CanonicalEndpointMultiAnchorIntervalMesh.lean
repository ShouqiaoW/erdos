import Erdos390.Full.CanonicalEndpointTwoTailCertificate

/-!
# Canonical endpoint meshes with a positive-mass interior anchor block

The earlier singleton-anchor constructor is convenient for a fixed mesh,
but its inverse constant degenerates when that one cell is refined.  This
file keeps the same literal endpoint cells and allows a finite collection of
positive cells to supply the interior anchor.  The operator entries are
unchanged; only the graph anchor measure is enlarged.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The positive-band inclusion as a finite-set embedding. -/
def positiveBandEmbedding : Fin M.cellCount ↪ Fin (M.cellCount + 1) where
  toFun := positiveBand M
  inj' := by
    intro i j hij
    apply Fin.ext
    have hij' := congrArg Fin.val hij
    change i.1 + 1 = j.1 + 1 at hij'
    omega

/-- Exact logarithmic-coordinate interval mesh whose interior anchor is the
union of the selected positive cells. -/
def canonicalIntervalMeshOfAnchors
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon) :
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
    unfold realLogCoordinate
    exact div_lt_div_of_pos_right
      (Real.strictMonoOn_log hLowerPos hUpperPos (by exact_mod_cast hCut))
      (by
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
  interiorCells := anchors.map (positiveBandEmbedding M)
  interior_lower j hj := by
    rw [Finset.mem_map] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact hInteriorLower k hk
  interior_upper j hj := by
    rw [Finset.mem_map] at hj
    obtain ⟨k, hk, rfl⟩ := hj
    exact hInteriorUpper k hk
  interiorTotal_pos := by
    obtain ⟨k, hk⟩ := hAnchors
    let IM₁ := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon k
      (hInteriorLower k hk) (hInteriorUpper k hk)
    apply Finset.sum_pos
    · intro j hj
      exact sub_pos.mpr (by
        simpa only [IM₁, canonicalIntervalMesh] using IM₁.lower_lt_upper j)
    · exact ⟨positiveBand M k,
        (Finset.mem_map' (positiveBandEmbedding M)).2 hk⟩

@[simp] theorem canonicalIntervalMeshOfAnchors_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors hInteriorLower hInteriorUpper)
    (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon anchors
      hAnchors hInteriorLower hInteriorUpper).lower j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower j : ℝ) := rfl

@[simp] theorem canonicalIntervalMeshOfAnchors_upper
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors hInteriorLower hInteriorUpper)
    (j : Fin (M.cellCount + 1)) :
    (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon anchors
      hAnchors hInteriorLower hInteriorUpper).upper j =
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper j : ℝ) := rfl

/-- The multi-anchor mesh has the same exact endpoint coverage as the
singleton constructor. -/
def canonicalTwoTailCertificateOfAnchors
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (anchor : Fin M.cellCount) (hAnchor : anchor ∈ anchors)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon) :
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S
      epsilon anchors hAnchors hInteriorLower hInteriorUpper
    IM.TwoTailPartitionCertificate := by
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S
    epsilon anchors hAnchors hInteriorLower hInteriorUpper
  let IM₁ := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchor
    (hInteriorLower anchor hAnchor) (hInteriorUpper anchor hAnchor)
  let T₁ := canonicalTwoTailCertificate M hdelta hn hW hWTwo S epsilon anchor
    (hInteriorLower anchor hAnchor) (hInteriorUpper anchor hAnchor)
  exact {
    base := T₁.base
    upperEnd := T₁.upperEnd
    base_nonneg := T₁.base_nonneg
    base_le_upperEnd := T₁.base_le_upperEnd
    upperEnd_le_one := T₁.upperEnd_le_one
    totalLength := by
      simpa only [IM, IM₁, canonicalIntervalMeshOfAnchors,
        canonicalIntervalMesh] using T₁.totalLength
    kernelDoubleIntegral_split := by
      intro i
      simpa only [IM, IM₁, canonicalIntervalMeshOfAnchors,
        canonicalIntervalMesh] using T₁.kernelDoubleIntegral_split i
  }

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
