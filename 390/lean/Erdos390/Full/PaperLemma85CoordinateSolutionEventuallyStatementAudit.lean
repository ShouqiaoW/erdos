import Erdos390.Full.PaperLemma85CoordinateSolutionEventually

/-! Expanded statement audit for the exact paper-scale Lemma 8.5 terminal. -/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
open PaperGuardCensus RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

theorem expanded_exists_paperFineMesh_cutoff_eventually_actualBandSchur_coordinate_solution
    (cMesh C : ℝ) (_hcMesh : 0 < cMesh) (hC : 0 < C) :
    ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ w₀ →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline)
              (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ))
              (b : B.RawBandGauge),
              (∀ i : Fin (M.cellCount + 1),
                |b.1 i| ≤ C * (delta + eta) * B.bandCenter i) →
              let hgamma := B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T
              let hgap := B.canonicalEffectiveNuisanceGap_on_closedBall I a
                hU hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz
              ∃ q : B.RawBandGauge,
                B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q = b ∧
                (∀ q' : B.RawBandGauge,
                  B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q' = b → q' = q) ∧
                paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q ≤
                  Csharp * (delta + eta) ∧
                ∀ i : Fin (M.cellCount + 1),
                  |q.1 i| ≤
                    Csharp * (delta + eta) * B.bandCenter i :=
  exists_paperFineMesh_cutoff_eventually_actualBandSchur_coordinate_solution
    cMesh C _hcMesh hC

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
