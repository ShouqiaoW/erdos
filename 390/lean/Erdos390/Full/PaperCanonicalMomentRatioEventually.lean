import Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually
import Erdos390.Full.PaperBridgeFit
import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# Canonical paper-scale moment-ratio bound

This file discharges the quotient first-moment ratio used by the ordinary
Schur transfer.  The numerator is the literal arithmetic first moment
`sum_j H_j * alpha_j`; the denominator is the literal sharp projection
weight `sum_j H_j * alpha_j^2`.  A canonical interior prime anchor gives a
uniform positive denominator, while the elementary prime-band estimate
bounds the numerator.

All constants are selected before `W`, the two independent mesh parameters,
and the mesh.  The public statement exposes no anchor or analytic estimate.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PaperWeightedInverseExport MovingLowGaugeTransfer
open RegularMeshPrimeCutoffs RegularRelativeMesh

namespace BridgeData

/--
Uniform first-moment/centre-energy ratio for the literal canonical
partition.  The displayed fineness condition is the paper scale
`delta + eta`; no comparison between `delta` and `eta` is assumed.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_momentRatio :
    ∃ Rproj : ℝ, 0 < Rproj ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ meshTol →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          (∃ hWne : B.sampleData.W ≠ 0,
            ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
          (∑ j : Fin (M.cellCount + 1),
              B.harmonicMass j * B.bandCenter j) ≤
            Rproj * sharpWeightTotal B.harmonicMass B.bandCenter := by
  let Rproj : ℝ := 128 * Real.log 4
  have hRproj : 0 < Rproj := by
    dsimp only [Rproj]
    positivity
  refine ⟨Rproj, hRproj,
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance,
    by norm_num [RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance],
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidable _instNonempty
  have hEnergyN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperCenterEnergyFloorCutoff_eventually
      W hW M hdelta hfine
  have hBandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hEnergyN, hBandTN] with n hEnergyAt hBandTAt
  intro B hBn hBW hpartition
  subst n
  subst W
  obtain ⟨hWne, hn, hEnergyAll⟩ := hEnergyAt
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
    hn hWne S
  have hpartitionCanonical : B.partition = P := by
    exact hpartitionUser.trans (by dsimp only [P])
  have hEnergy : (1 : ℝ) / 64 ≤ B.partition.centerEnergy := by
    rw [hpartitionCanonical]
    exact hEnergyAll S
  have hFirstMoment :
      (∑ j : Fin (M.cellCount + 1),
          B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := by
    simpa only [harmonicMass, bandCenter] using
      B.partition.sum_mass_mul_center_eq_bandTReciprocalSum
  have hSharpWeight :
      sharpWeightTotal B.harmonicMass B.bandCenter =
        B.partition.centerEnergy := by
    unfold sharpWeightTotal sharpWeight harmonicMass bandCenter
    unfold ArithmeticBandGeometry.Partition.centerEnergy
      Erdos390.Lemma84.WeightedBandData.centerEnergy
      Erdos390.Lemma84.WeightedBandData.bandNormSq
      Erdos390.Lemma84.WeightedBandData.bandInner
    simp only [pow_two, mul_assoc]
  calc
    (∑ j : Fin (M.cellCount + 1),
        B.harmonicMass j * B.bandCenter j) =
        bandTReciprocalSum B.sampleData.n B.sampleData.W := hFirstMoment
    _ ≤ 2 * Real.log 4 := hBandTAt
    _ = Rproj * ((1 : ℝ) / 64) := by
      dsimp only [Rproj]
      ring
    _ ≤ Rproj * B.partition.centerEnergy :=
      mul_le_mul_of_nonneg_left hEnergy hRproj.le
    _ = Rproj * sharpWeightTotal B.harmonicMass B.bandCenter := by
      rw [hSharpWeight]

end BridgeData

end PaperBridgeFit

end Full

end Erdos390

end
