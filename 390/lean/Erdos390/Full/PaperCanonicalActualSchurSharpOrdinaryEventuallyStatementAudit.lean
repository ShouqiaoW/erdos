import Erdos390.Full.PaperCanonicalActualSchurSharpOrdinaryEventually

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

/-! A deliberately expanded signature audit: this repeats every public
quantifier and conclusion instead of relying on `#check` or a named alias. -/
example :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ meshTol →
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
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
              ∀ (T : BarycentricTarget B.sampleData)
                (_hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline),
                ∃ e : ∀ (z : B.EffectiveParamSpace),
                    z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                      B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                    e z hz q =
                      B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        ((e z hz).symm v) ≤
                      Csharp *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) ∧
                  ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖ := by
  exact
    exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary

end Erdos390.Full.PaperBridgeFit.BridgeData
