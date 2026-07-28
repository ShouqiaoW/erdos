import Erdos390.Full.CanonicalEndpointMultiAnchorWeightedInverseEventually
import Erdos390.Full.SelectedDyadicRegularMesh

/-!
# A nonvacuous selected-mesh projected inverse

The universal continuum tolerance is chosen first.  Only then are the two
mesh parameters and an explicit regular mesh selected.  Its anchor block has
fixed ideal mass `1/4`, so the hypotheses of the multi-anchor inverse hold
literally rather than through a potentially false antecedent.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph CompressedArithmeticOperator
open MovingLowGaugeTransfer PaperWeightedInverseExport
open SelectedDyadicRegularMesh

/-- Exact selected-mesh version of the moving-low arithmetic inverse.

Quantifier order: the continuum gap and mesh tolerance come first; an
explicit `(delta, eta, mesh, anchor block)` is then exhibited; the arithmetic
cutoff comes after that fixed selection; only the ambient threshold is last.
-/
theorem exists_selectedDyadicMesh_eventually_canonical_projected_inverse :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ K N : ℕ, ∃ hK : 3 ≤ K, ∃ hN : 0 < N,
        let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
        let anchors := SelectedDyadicRegularMesh.anchors hK hN
        ∃ anchor : Fin M.cellCount, anchor ∈ anchors ∧
          delta K < meshTol ∧
          (∀ k : Fin M.cellCount, M.width k < meshTol) ∧
          ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
            ∀ W : ℕ, W₀ ≤ W →
              ∀ᶠ n : ℕ in atTop,
                ∃ hW : W ≠ 0, ∃ hWTwo : 2 ≤ W, ∃ hn : 1 < n,
                  ∃ S : ScaleSeparation M n W,
                    ∃ hInteriorLower : ∀ k ∈ anchors, (1 / 8 : ℝ) ≤
                      realLogCoordinate (y n)
                        ((canonicalCertificate M (by
                            unfold SelectedDyadicRegularMesh.delta
                            positivity) hn hW S).lower
                          (positiveBand M k) : ℝ),
                    ∃ hInteriorUpper : ∀ k ∈ anchors,
                      realLogCoordinate (y n)
                        ((canonicalCertificate M (by
                            unfold SelectedDyadicRegularMesh.delta
                            positivity) hn hW S).upper
                          (positiveBand M k) : ℝ) ≤ 1 - 1 / 8,
                    let P := canonicalPartition M (by
                      unfold SelectedDyadicRegularMesh.delta
                      positivity) hn hW S
                    let E := canonicalCertificate M (by
                      unfold SelectedDyadicRegularMesh.delta
                      positivity) hn hW S
                    let IM := canonicalIntervalMeshOfAnchors M (by
                      unfold SelectedDyadicRegularMesh.delta
                      positivity) hn hW hWTwo S (1 / 8) anchors
                        (SelectedDyadicRegularMesh.anchors_nonempty hK hN)
                        hInteriorLower hInteriorUpper
                    let Cinv :=
                      (4 / (kappa * ∑ j, IM.anchor j)) /
                        (1 - (4 / (kappa * ∑ j, IM.anchor j)) *
                          (2 * (kappa * ((1 : ℝ) / 8) / 16)))
                    ∃ actualEquiv : SharpGaugeSpace P.mass P.center ≃L[ℝ]
                        SharpGaugeSpace P.mass P.center,
                      (∀ q, actualEquiv q =
                        ArithmeticGaugeStableInverse.projectedSharpCLM
                          (arithmeticDiagonal (y n) E.lower E.upper)
                          (arithmeticKernel (y n) E.lower E.upper)
                          P.center (sharpWeight P.mass P.center)
                          (by
                            change (∑ j, P.mass j * P.center j ^ 2) ≠ 0
                            apply ne_of_gt
                            apply Finset.sum_pos
                            · intro j _hj
                              exact mul_pos (P.data.mass_pos j)
                                (sq_pos_of_pos (P.center_pos hn j))
                            · exact ⟨lowBand M, Finset.mem_univ _⟩) q) ∧
                      (∀ v, ‖actualEquiv.symm v‖ ≤ Cinv * ‖v‖) := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, hUniversal⟩ :=
    exists_meshTolerance_cutoff_eventually_multiAnchor_projected_inverse
      (epsilon := (1 / 8 : ℝ)) (anchorFloor := (1 / 8 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨K, N, hK, hN, hdeltaFine, _hratioFine, hwidthFine⟩ :=
    exists_fine_mesh meshTol hmeshTol
  let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
  let anchors := SelectedDyadicRegularMesh.anchors hK hN
  have hAnchors : anchors.Nonempty :=
    SelectedDyadicRegularMesh.anchors_nonempty hK hN
  let anchor : Fin M.cellCount := hAnchors.choose
  have hAnchor : anchor ∈ anchors := hAnchors.choose_spec
  have hdelta : 0 < delta K := by
    unfold SelectedDyadicRegularMesh.delta
    positivity
  have hIdealLower : ∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k := by
    intro k hk
    exact (SelectedDyadicRegularMesh.anchors_ideal_interior hK hN hk).1
  have hIdealUpper : ∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ) := by
    intro k hk
    exact (SelectedDyadicRegularMesh.anchors_ideal_interior hK hN hk).2
  have hIdealMass : (1 / 8 : ℝ) ≤
      (∑ k ∈ anchors, M.width k) / 2 := by
    rw [show (∑ k ∈ anchors, M.width k) = (1 / 4 : ℝ) by
      simpa only [M, anchors] using
        SelectedDyadicRegularMesh.sum_anchor_widths hK hN]
    norm_num
  obtain ⟨CRow, hCRow, W₀, hmain⟩ := hUniversal M hdelta anchors hAnchors
    anchor hAnchor hIdealLower hIdealUpper hIdealMass
      ⟨hdeltaFine, hwidthFine⟩
  exact ⟨kappa, hkappa, meshTol, hmeshTol, K, N, hK, hN, anchor,
    hAnchor, hdeltaFine, hwidthFine, CRow, hCRow, W₀, hmain⟩

end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
