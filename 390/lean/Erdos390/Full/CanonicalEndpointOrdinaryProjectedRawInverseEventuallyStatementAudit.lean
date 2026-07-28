import Erdos390.Full.CanonicalEndpointOrdinaryProjectedRawInverseEventually

/-!
# Expanded statement audit: canonical ordinary endpoint inverse

This declaration deliberately repeats the complete public type rather than
using `#check`, so Lean verifies the parameter order and the literal operator
identification independently of the theorem's declaration syntax.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open CompressedArithmeticOperator MovingLowGaugeTransfer
open PaperWeightedInverseExport

noncomputable section

theorem expanded_exists_paperFineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse :
    ∃ Cref : ℝ, 0 < Cref ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∃ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            let E := canonicalCertificate M hdelta hn hWne S
            ∀ q : RawGaugeSpace P.mass P.center,
              ‖q‖ ≤ Cref *
                ‖projectedRawLinearMap
                  (arithmeticDiagonal (y n) E.lower E.upper)
                  (arithmeticKernel (y n) E.lower E.upper)
                  P.mass P.center
                  (by
                    have hEnergyId :
                        sharpWeightTotal P.mass P.center = P.centerEnergy := by
                      unfold sharpWeightTotal sharpWeight
                      unfold ArithmeticBandGeometry.Partition.centerEnergy
                        Erdos390.Lemma84.WeightedBandData.centerEnergy
                        Erdos390.Lemma84.WeightedBandData.bandNormSq
                        Erdos390.Lemma84.WeightedBandData.bandInner
                      simp only [pow_two, mul_assoc]
                    rw [hEnergyId]
                    exact (P.centerEnergy_pos hn).ne') q‖ :=
  exists_paperFineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse

end
end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
