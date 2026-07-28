import Erdos390.Full.RegularMeshPrimeCutoffsEventually

/-!
# The canonical `n`-indexed endpoint family for a regular mesh

This module exposes the actual partition constructed from the explicit
cutoffs, rather than only asserting its existence.  Consequently the low
cell and every later lower endpoint can be audited definitionally.
-/

open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry
open RegularRelativeMesh
open PrimeIntervalPartitionConstructor PositiveCellTransfer

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Index of the unique moving-low cell. -/
def lowBand : Fin (M.cellCount + 1) := ⟨0, by omega⟩

/-- Embedding of a positive regular-mesh cell after the low cell. -/
def positiveBand (k : Fin M.cellCount) : Fin (M.cellCount + 1) :=
  ⟨k.1 + 1, by omega⟩

theorem W_le_first_fullCutoff
    {n W : ℕ} (S : ScaleSeparation M n W) :
    W ≤ fullCutoff M n W 1 := by
  apply Nat.le_floor
  have htwo : (W : ℝ) ≤ (2 * W : ℝ) := by
    calc
      (W : ℝ) ≤ (W : ℝ) + (W : ℝ) :=
        le_add_of_nonneg_right (Nat.cast_nonneg W)
      _ = (2 : ℝ) * W := by ring
  have hscale : (W : ℝ) ≤ scalePoint n delta := htwo.trans S.low
  simpa only [fullCutoff, M.endpoint_zero] using hscale

/-- The actual partition attached to the explicit cutoff family. -/
def canonicalPartition
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    ArithmeticBandGeometry.Partition n W (Fin (M.cellCount + 1)) :=
  PrimeIntervalPartitionConstructor.partition
    (by omega : 0 < M.cellCount + 1)
    (fullCutoff M n W)
    (fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S))
    rfl
    (fullCutoff_last M (Nat.zero_lt_of_lt hn))
    (every_fullCutoff_cell_has_prime M hW S)

/-- Its canonical interval certificate. -/
def canonicalCertificate
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    IntervalCertificate (canonicalPartition M hdelta hn hW S) :=
  PrimeIntervalPartitionConstructor.intervalCertificate
    (by omega : 0 < M.cellCount + 1)
    (fullCutoff M n W)
    (fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S))
    rfl
    (fullCutoff_last M (Nat.zero_lt_of_lt hn))
    (every_fullCutoff_cell_has_prime M hW S)

@[simp] theorem canonicalCertificate_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) :
    (canonicalCertificate M hdelta hn hW S).lower j =
      fullCutoff M n W j.1 := rfl

@[simp] theorem canonicalCertificate_upper
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) :
    (canonicalCertificate M hdelta hn hW S).upper j =
      fullCutoff M n W (j.1 + 1) := rfl

theorem canonicalCertificate_low_lower
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W) :
    (canonicalCertificate M hdelta hn hW S).lower (lowBand M) = W := by
  rfl

/-- Every non-low cell starts strictly after `W`; hence the low cell is
the unique cell with lower endpoint exactly `W`. -/
theorem canonicalCertificate_nonlow_lower_gt
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) (hj : j ≠ lowBand M) :
    W < (canonicalCertificate M hdelta hn hW S).lower j := by
  have hjpos : 0 < j.1 := by
    by_contra hnot
    have hjzero : j.1 = 0 := Nat.eq_zero_of_not_pos hnot
    apply hj
    exact Fin.ext hjzero
  let j0 : Fin (M.cellCount + 1) := lowBand M
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    every_fullCutoff_cell_has_prime M hW S j0
  have hfirst : W < fullCutoff M n W 1 := by
    exact hpLower.trans_le (by simpa [j0, lowBand] using hpUpper)
  have hmono := fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S)
  rw [canonicalCertificate_lower]
  exact hfirst.trans_le (hmono hjpos)

theorem canonicalCertificate_lower_ge_cutoff
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (j : Fin (M.cellCount + 1)) :
    W ≤ (canonicalCertificate M hdelta hn hW S).lower j := by
  rw [canonicalCertificate_lower]
  exact (fullCutoff_monotone M hdelta hn
    (W_le_first_fullCutoff M S)) (Nat.zero_le j.1)

/-- Each fixed non-low lower endpoint crosses every prescribed PNT
threshold. -/
theorem eventually_threshold_le_nonlow_fullCutoff
    (hdelta : 0 < delta) (W X : ℕ)
    (j : Fin (M.cellCount + 1)) (hj : j ≠ lowBand M) :
    ∀ᶠ n : ℕ in atTop, X ≤ fullCutoff M n W j.1 := by
  have hjpos : 0 < j.1 := by
    by_contra hnot
    apply hj
    exact Fin.ext (Nat.eq_zero_of_not_pos hnot)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjpos)
  have hklt : k < M.cellCount := by omega
  let q : Fin M.cellCount := ⟨k, hklt⟩
  have htop := tendsto_scalePoint_atTop (M.endpoint_pos hdelta k)
  have hevent := htop.eventually (eventually_ge_atTop (X : ℝ))
  filter_upwards [hevent] with n hn
  rw [hk, fullCutoff_succ]
  apply Nat.le_floor
  simpa only [q, RegularRelativeMesh.Mesh.lower] using hn

/-- Eventually the canonical family exists simultaneously with its exact
low-cell and PNT-threshold conclusions. -/
theorem eventually_canonical_endpoint_family
    (hdelta : 0 < delta) {W : ℕ} (hW : W ≠ 0) (X : ℕ)
    (hXW : X ≤ W) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 1 < n, ∃ S : ScaleSeparation M n W,
        let E := canonicalCertificate M hdelta hn hW S
        E.lower (lowBand M) = W ∧
          (∀ j, j ≠ lowBand M → W < E.lower j) ∧
          (∀ j, X ≤ E.lower j) := by
  have hsep := eventually_scaleSeparation M hdelta W
  have hthreshold : ∀ᶠ n : ℕ in atTop,
      ∀ j : Fin (M.cellCount + 1), j ≠ lowBand M →
        X ≤ fullCutoff M n W j.1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = lowBand M
    · exact Filter.Eventually.of_forall (fun n h => (h hj).elim)
    · filter_upwards [eventually_threshold_le_nonlow_fullCutoff M
        hdelta W X j hj] with n hn hnot
      exact hn
  filter_upwards [eventually_gt_atTop 1, hsep, hthreshold] with n hn hS hX
  refine ⟨hn, hS, canonicalCertificate_low_lower M hdelta hn hW hS,
    ?_, ?_⟩
  · intro j hj
    exact canonicalCertificate_nonlow_lower_gt M hdelta hn hW hS j hj
  · intro j
    by_cases hj : j = lowBand M
    · rw [hj, canonicalCertificate_low_lower M hdelta hn hW hS]
      exact hXW
    · simpa only [canonicalCertificate_lower] using hX j hj

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
