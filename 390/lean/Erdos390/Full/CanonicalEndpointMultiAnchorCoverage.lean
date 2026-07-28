import Erdos390.Full.CanonicalEndpointAnchorCoverage
import Erdos390.Full.CanonicalEndpointMultiAnchorIntervalMesh

/-!
# Eventual coverage of a fixed interior anchor block

All cells in a fixed finite ideal anchor block remain interior after the
literal floor operation.  Their total actual logarithmic length is at least
half of the total ideal length.  Unlike a singleton anchor, this lower bound
can stay positive while the mesh is refined.
-/

open Filter Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh KernelPrimeQuadrature
open ContinuumCellGraph

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem eventually_canonical_anchorBlock_coverage
    (hdelta : 0 < delta) {W : ℕ} (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    {epsilon anchorFloor : ℝ}
    (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
    (hIdealLower : ∀ k ∈ anchors, epsilon < M.lower k)
    (hIdealUpper : ∀ k ∈ anchors, M.upper k ≤ 1 - epsilon)
    (hAnchorFloor : anchorFloor ≤
      (∑ k ∈ anchors, M.width k) / 2) :
    ∀ᶠ n : ℕ in atTop,
      ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
        ∃ hInteriorLower : ∀ k ∈ anchors, epsilon ≤
          realLogCoordinate (y n)
            ((canonicalCertificate M hdelta hn hW S).lower
              (positiveBand M k) : ℝ),
        ∃ hInteriorUpper : ∀ k ∈ anchors,
          realLogCoordinate (y n)
            ((canonicalCertificate M hdelta hn hW S).upper
              (positiveBand M k) : ℝ) ≤ 1 - epsilon,
          let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW
            hWTwo S epsilon anchors hAnchors
              hInteriorLower hInteriorUpper
          anchorFloor ≤ ∑ j, IM.anchor j := by
  have hEach : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount, k ∈ anchors →
        ∃ hnk : 1 < n, ∀ S : ScaleSeparation M n W,
          let E := canonicalCertificate M hdelta hnk hW S
          epsilon ≤ realLogCoordinate (y n)
              (E.lower (positiveBand M k) : ℝ) ∧
            realLogCoordinate (y n)
              (E.upper (positiveBand M k) : ℝ) ≤ 1 - epsilon ∧
            M.width k / 2 ≤
              realLogCoordinate (y n)
                  (E.upper (positiveBand M k) : ℝ) -
                realLogCoordinate (y n)
                  (E.lower (positiveBand M k) : ℝ) := by
    rw [Filter.eventually_all]
    intro k
    by_cases hk : k ∈ anchors
    · exact (eventually_canonical_anchor_coverage M hdelta hW k
        (hIdealLower k hk) (hIdealUpper k hk)).mono (fun n hn _ ↦ hn)
    · filter_upwards with n
      exact fun hfalse ↦ (hk hfalse).elim
  filter_upwards [eventually_gt_atTop 1, hEach] with n hn hAll
  have hCell (k : Fin M.cellCount) (hk : k ∈ anchors)
      (S : ScaleSeparation M n W) :
      epsilon ≤ realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hn hW S).lower
            (positiveBand M k) : ℝ) ∧
        realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hn hW S).upper
            (positiveBand M k) : ℝ) ≤ 1 - epsilon ∧
        M.width k / 2 ≤
          realLogCoordinate (y n)
              ((canonicalCertificate M hdelta hn hW S).upper
                (positiveBand M k) : ℝ) -
            realLogCoordinate (y n)
              ((canonicalCertificate M hdelta hn hW S).lower
                (positiveBand M k) : ℝ) := by
    obtain ⟨hnk, hkAll⟩ := hAll k hk
    simpa only [Subsingleton.elim hnk hn] using hkAll S
  refine ⟨hn, ?_⟩
  intro S
  let hLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ) := fun k hk ↦ (hCell k hk S).1
  let hUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon :=
    fun k hk ↦ (hCell k hk S).2.1
  refine ⟨hLower, hUpper, ?_⟩
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hLower hUpper
  have hsum : (∑ j, IM.anchor j) =
      ∑ k ∈ anchors, IM.length (positiveBand M k) := by
    unfold ContinuumCellGraph.IntervalMesh.anchor
    rw [← Finset.sum_filter]
    calc
      (∑ x ∈ Finset.univ.filter
          (fun j ↦ j ∈ anchors.map (positiveBandEmbedding M)),
          IM.length x) =
          ∑ x ∈ anchors.map (positiveBandEmbedding M), IM.length x := by
        apply Finset.sum_congr
        · ext j
          simp
        · intro j hj
          rfl
      _ = ∑ k ∈ anchors, IM.length (positiveBand M k) := by
        rw [Finset.sum_map]
        rfl
  change anchorFloor ≤ ∑ j, IM.anchor j
  rw [hsum]
  calc
    anchorFloor ≤ (∑ k ∈ anchors, M.width k) / 2 := hAnchorFloor
    _ = ∑ k ∈ anchors, M.width k / 2 := by
      rw [Finset.sum_div]
    _ ≤ ∑ k ∈ anchors, IM.length (positiveBand M k) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [IM, canonicalIntervalMeshOfAnchors,
        ContinuumCellGraph.IntervalMesh.length] using (hCell k hk S).2.2

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
