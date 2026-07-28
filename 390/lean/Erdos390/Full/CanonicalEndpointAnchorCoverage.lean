import Erdos390.Full.CanonicalEndpointIntervalMesh

/-!
# Uniform interior anchor coverage for the endpoint mesh

Flooring a power-scale endpoint changes its logarithmic coordinate by at
most `log 2 / log y` once the endpoint is at least two.  This proves that a
fixed strictly interior regular-mesh cell remains interior in the actual
endpoint mesh and retains at least half of its continuum length.
-/

open Filter Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature
open ContinuumCellGraph

theorem floor_scalePoint_coordinate_bounds
    {n : ℕ} (hn : 1 < n) {t : ℝ}
    (hxTwo : 2 ≤ scalePoint n t) :
    t - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ∧
      realLogCoordinate (y n) (⌊scalePoint n t⌋₊ : ℝ) ≤ t := by
  let x := scalePoint n t
  let m := ⌊x⌋₊
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hxpos : 0 < x := by unfold x scalePoint; positivity
  have hmUpper : (m : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hfloorLt : x < (m : ℝ) + 1 := by
    simpa only [m] using Nat.lt_floor_add_one x
  have hmLower : x / 2 ≤ (m : ℝ) := by linarith
  have hmpos : (0 : ℝ) < (m : ℝ) :=
    (div_pos hxpos (by norm_num)).trans_le hmLower
  have hlogLower : Real.log (x / 2) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (div_pos hxpos (by norm_num)) hmLower
  have hlogUpper : Real.log (m : ℝ) ≤ Real.log x :=
    Real.log_le_log hmpos hmUpper
  have hlogX : Real.log x = t * Real.log (y n) := by
    unfold x scalePoint
    rw [Real.log_exp]
  have hlogDiv : Real.log (x / 2) = Real.log x - Real.log 2 := by
    rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  constructor
  · unfold realLogCoordinate
    apply (le_div_iff₀ hylog).2
    have hscaled :
        (t - Real.log 2 / Real.log (y n)) * Real.log (y n) =
          Real.log x - Real.log 2 := by
      rw [sub_mul, div_mul_cancel₀ _ hylog.ne', hlogX]
    rw [hscaled, ← hlogDiv]
    exact hlogLower
  · unfold realLogCoordinate
    apply (div_le_iff₀ hylog).2
    rw [hlogX] at hlogUpper
    exact hlogUpper

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem canonical_positiveBand_coordinate_bounds
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (k : Fin M.cellCount)
    (hLowerTwo : 2 ≤ scalePoint n (M.lower k))
    (hUpperTwo : 2 ≤ scalePoint n (M.upper k)) :
    let E := canonicalCertificate M hdelta hn hW S
    M.lower k - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ∧
      realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ≤
        M.lower k ∧
      M.upper k - Real.log 2 / Real.log (y n) ≤
        realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ∧
      realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
        M.upper k := by
  dsimp only
  have hlower := floor_scalePoint_coordinate_bounds hn hLowerTwo
  have hupper := floor_scalePoint_coordinate_bounds hn hUpperTwo
  simpa only [canonicalCertificate_lower, canonicalCertificate_upper,
    positiveBand, fullCutoff_succ, RegularRelativeMesh.Mesh.lower,
    RegularRelativeMesh.Mesh.upper] using ⟨hlower.1, hlower.2,
      hupper.1, hupper.2⟩

/-- Quantitative anchor statement at one `n`. -/
theorem canonical_anchor_interior_and_length
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {epsilon : ℝ} (k : Fin M.cellCount)
    (hIdealUpper : M.upper k ≤ 1 - epsilon)
    (hLowerTwo : 2 ≤ scalePoint n (M.lower k))
    (hUpperTwo : 2 ≤ scalePoint n (M.upper k))
    (hLossLower : Real.log 2 / Real.log (y n) < M.lower k - epsilon)
    (hLossWidth : Real.log 2 / Real.log (y n) ≤ M.width k / 2) :
    let E := canonicalCertificate M hdelta hn hW S
    epsilon ≤ realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ∧
      realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
        1 - epsilon ∧
      M.width k / 2 ≤
        realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) -
          realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) := by
  dsimp only
  obtain ⟨hlowerLo, hlowerHi, hupperLo, hupperHi⟩ :=
    canonical_positiveBand_coordinate_bounds M hdelta hn hW S k
      hLowerTwo hUpperTwo
  constructor
  · linarith
  constructor
  · exact hupperHi.trans hIdealUpper
  · unfold RegularRelativeMesh.Mesh.width at hLossWidth ⊢
    linarith

/-- The selected anchor cell is eventually interior and has a uniform
positive anchor mass. -/
theorem eventually_canonical_anchor_coverage
    (hdelta : 0 < delta) {W : ℕ} (hW : W ≠ 0)
    {epsilon : ℝ} (k : Fin M.cellCount)
    (hIdealLower : epsilon < M.lower k)
    (hIdealUpper : M.upper k ≤ 1 - epsilon) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
        let E := canonicalCertificate M hdelta hn hW S
        epsilon ≤
            realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) ∧
          realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
            1 - epsilon ∧
          M.width k / 2 ≤
            realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) -
              realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ) := by
  have hlowerTop := tendsto_scalePoint_atTop (M.lower_pos hdelta k)
  have hupperTop := tendsto_scalePoint_atTop
    ((M.lower_pos hdelta k).trans (M.lower_lt_upper hdelta k))
  have hlogYTop : Tendsto (fun n : ℕ => Real.log (y n)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_y_atTop
  have hloss : Tendsto (fun n : ℕ => Real.log 2 / Real.log (y n))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hlogYTop
  have hmargin : 0 < M.lower k - epsilon := sub_pos.mpr hIdealLower
  have hwidthHalf : 0 < M.width k / 2 :=
    div_pos (M.width_pos hdelta k) (by norm_num)
  have hlossLower := hloss.eventually (eventually_lt_nhds hmargin)
  have hlossWidth := hloss.eventually (eventually_le_nhds hwidthHalf)
  filter_upwards [eventually_gt_atTop 1,
    hlowerTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hupperTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hlossLower, hlossWidth] with n hn hLowerTwo hUpperTwo hLossLower hLossWidth
  refine ⟨hn, ?_⟩
  intro S
  exact canonical_anchor_interior_and_length M hdelta hn hW S k
    hIdealUpper hLowerTwo hUpperTwo hLossLower hLossWidth

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
