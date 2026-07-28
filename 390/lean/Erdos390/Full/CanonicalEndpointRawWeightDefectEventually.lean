import Erdos390.Full.PaperCanonicalPrimeAnchorEventually

/-!
# Ordinary raw-weight convergence for canonical endpoint bands

The arithmetic raw gauge uses the exact finite weights `H_j alpha_j`.
The continuum gauge uses `harmonicMass_j * center_j`, which is exactly the
ordinary coordinate length of the endpoint cell.  This file compares those
two quantities without identifying either arithmetic factor separately with
its continuum analogue.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature MovingLowMomentQuadrature

/-- A mesh-independent cutoff for the first-moment quadrature used in the
raw-gauge comparison. -/
def canonicalRawWeightDefectCutoff : ℕ :=
  max 2 MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff

namespace Mesh

/-- The total raw-weight defect tends to zero for every fixed permitted
mesh.  The cutoff is selected before both mesh parameters and the mesh; only
the eventual ambient threshold may depend on them.  The conclusion is
uniform in the proof objects defining the literal canonical partition. -/
theorem canonicalRawWeightDefectCutoff_eventually
    (W : ℕ) (hWcut : canonicalRawWeightDefectCutoff ≤ W)
    {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta)
    {e : ℝ} (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
      (S : ScaleSeparation M n W),
      let P := canonicalPartition M hdelta hn hWne S
      (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤ e := by
  let Cmoment : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xmoment : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  have hXmoment : Xmoment ≤ W :=
    (le_max_right 2 Xmoment).trans hWcut
  have hMoment : ∀ A Y : ℕ, Xmoment ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
        PrimeSums.fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      2 * Cmoment / Real.log (A : ℝ) ^ 3 +
        Cmoment / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cmoment, Xmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound
        A Y hA hAY
  have hEach : ∀ j : Fin (M.cellCount + 1),
      Tendsto (fun n : ℕ ↦ endpointMomentError M Cmoment n W j)
        atTop (nhds 0) := by
    intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simpa only [lowBand] using
        tendsto_low_endpointMomentError_zero M Cmoment W
    · simpa only [positiveBand] using
        tendsto_positive_endpointMomentError_zero M hdelta Cmoment W k
  have hSumT : Tendsto (fun n : ℕ ↦
      ∑ j : Fin (M.cellCount + 1), endpointMomentError M Cmoment n W j)
      atTop (nhds 0) := by
    have hsum := tendsto_finset_sum Finset.univ (fun j _hj ↦ hEach j)
    simpa only [Finset.sum_const_zero] using hsum
  have hSumSmall := hSumT.eventually (eventually_le_nhds he)
  filter_upwards [hSumSmall] with n hnSmall
  intro hn hWne S
  let P := canonicalPartition M hdelta hn hWne S
  calc
    (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤
        ∑ j : Fin (M.cellCount + 1), endpointMomentError M Cmoment n W j := by
      apply Finset.sum_le_sum
      intro j _hj
      exact abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
        M hdelta hn hWne S hMoment hXmoment j
    _ ≤ e := hnSmall

/-- Existential compatibility wrapper with a witness fixed before the mesh. -/
theorem exists_cutoff_before_mesh_eventually_canonical_rawWeightDefect :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta), ∀ (hdelta : 0 < delta),
      ∀ e : ℝ, 0 < e →
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W),
        let P := canonicalPartition M hdelta hn hWne S
        (∑ j : Fin (M.cellCount + 1),
          |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤ e := by
  refine ⟨canonicalRawWeightDefectCutoff, ?_⟩
  intro W hW delta eta M hdelta e he
  exact canonicalRawWeightDefectCutoff_eventually W hW M hdelta he

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
