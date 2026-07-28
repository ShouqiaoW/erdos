import Erdos390.Full.PaperCanonicalLemma86RemainingOutputsEventually

/-!
# Expanded statement audit: canonical two-sided variance for Lemma 8.6

This declaration repeats the full public type of the variance-of-base
terminal.  It records that its constants precede the cutoff, that the two
mesh parameters are quantified independently, and that the two-sided
variance estimate is for the very same finite Schur equivalence supplied by
the relative-power terminal.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

set_option maxHeartbeats 1000000 in
theorem expanded_exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
    (cMesh Creg : ℝ) (hcMesh : 0 < cMesh) (hCreg : 0 ≤ Creg) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ Cvar : ℝ, 0 < Cvar ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
          (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
          (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
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
              (hscale : B.w = delta + eta) →
              ∀ (T : BarycentricTarget B.sampleData)
                (hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline)
                (z : B.EffectiveParamSpace)
                (hz : z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ))
                (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
                paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one)
                    (B.actualBandRegression
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e) ≤ Creg * B.w →
                (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                  |B.partition.deviation p| ≤ B.w) →
                B.partition.totalL1 ≤ 7 * B.w →
                B.w ^ 2 ≤
                  (456 / cMesh ^ 2) * B.partition.variance →
                B.partition.variance ≤ 4 * B.w ^ 2 →
                B.partition.variance ≤ B.partition.centerEnergy →
                gammaSlow * B.w ^ 2 ≤
                    B.actualTwoStageCompensatedVariance
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e ∧
                  B.actualTwoStageCompensatedVariance
                      (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) e ≤
                    Cvar * B.w ^ 2 :=
  exists_paperFineMesh_cutoff_eventually_canonical_lemma86_variance_of_base
    cMesh Creg hcMesh hCreg

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
