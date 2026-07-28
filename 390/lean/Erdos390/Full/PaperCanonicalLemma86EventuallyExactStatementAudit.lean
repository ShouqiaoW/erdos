import Erdos390.Full.PaperCanonicalLemma86RemainingOutputsEventually

/-!
# Fully expanded statement audit for paper Lemma 8.6

This declaration repeats the entire public terminal type.  In particular,
it checks the exact order of constants, cutoff, marked-row constant,
independent mesh parameters, head/physical data, tilt box, and eventual
sample size.  The repeated type also makes syntactically visible that every
quantitative conclusion uses the same finite Schur equivalence.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PrimeSums PaperWeightedInverseExport
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

set_option maxHeartbeats 4000000 in
theorem expanded_exists_paperFineMesh_cutoff_eventually_canonical_lemma86
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∃ Creg : ℝ, 0 ≤ Creg ∧
        Creg = Csharp * (2 * Crow) ∧
      ∃ Ccmp : ℝ, 0 < Ccmp ∧
      ∃ Crel : ℝ, 0 < Crel ∧
      ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ Cvar : ℝ, 0 < Cvar ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∃ CmarkedFinal : ℝ, 0 ≤ CmarkedFinal ∧
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (hPermitted : IsPermitted (cMesh := cMesh) M),
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
        ∃ epsilonRel : ℕ → ℝ,
          (∀ᶠ n : ℕ in atTop, 0 ≤ epsilonRel n) ∧
          Tendsto epsilonRel atTop (nhds 0) ∧
          Tendsto
            (fun n : ℕ ↦ epsilonRel n * Real.log (Scale.L n))
              atTop (nhds 0) ∧
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
                  B.partition =
                    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                      M hdelta B.n_gt_one hWne S) →
                (hscale : B.w = delta + eta) →
                ∀ (T : BarycentricTarget B.sampleData)
                  (hTmargin : marginFloor ≤ T.cellMassMargin)
                  (hbaseline : B.baseline = T.baseline),
                  (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.partition.deviation p| ≤ B.w) ∧
                  B.partition.totalL1 ≤ 7 * B.w ∧
                  paperLemma86VarianceFactor cMesh * B.w ^ 2 ≤
                    B.partition.variance ∧
                  B.partition.variance ≤ 4 * B.w ^ 2 ∧
                  B.partition.variance ≤ B.partition.centerEnergy ∧
                  ∃ e : ∀ (z : B.EffectiveParamSpace),
                      z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ) →
                        B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                      e z hz q =
                        B.actualBandSchurLinearMap
                          (B.effectiveParamEquiv z)
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
                    (∀ (z : B.EffectiveParamSpace)
                        (hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                      ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖) ∧
                    ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)),
                      (∀ j,
                        |B.normalizedBandCovarianceRow
                            (B.effectiveParamEquiv z)
                            (B.nuisanceResidualScore
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              B.slowScore) j| ≤
                          (Crow * B.w) * B.bandCenter j) ∧
                      B.actualBandSchurLinearMap
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) =
                        B.actualBandRegressionTarget
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) ∧
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
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤ Creg * B.w ∧
                      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                        |B.actualCompensatedCoefficient
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) p| ≤ Ccmp * B.w) ∧
                      B.partition.compensatedL1
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤ Ccmp * B.w ∧
                      B.partition.compensatedL2Sq
                          (B.actualBandRegression
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (e z hz)) ≤ Ccmp * B.w ^ 2 ∧
                      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (B.postBandPrimeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))
                          (B.postBandPrimeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz))) -
                        (B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (B.postBandSquarefreeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))
                          (B.postBandSquarefreeScore
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))| ≤
                        (Crel * (1 / (B.sampleData.W : ℝ)) +
                          epsilonRel B.sampleData.n) * B.w ^ 2 ∧
                      gammaSlow * B.w ^ 2 ≤
                        B.actualTwoStageCompensatedVariance
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) (e z hz) ∧
                      B.actualTwoStageCompensatedVariance
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) (e z hz) ≤
                        Cvar * B.w ^ 2 ∧
                      ∀ p : BandPrime B.sampleData.n B.sampleData.W,
                        |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                          (fun m ↦ valuation p.1 (B.sampleData.value m))
                          (B.actualCompensatedScore
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            (B.actualBandRegression
                              (B.effectiveParamEquiv z)
                              (B.canonicalEffectiveNuisanceGamma_pos
                                I U (3 * (a : ℝ)) T)
                              (B.canonicalEffectiveNuisanceGap_on_closedBall
                                I a hU hlowerOne hupperU
                                (by intro sigma; rw [hcanonical]; rfl)
                                (by intro sigma; rw [hcanonical]; rfl)
                                T hbaseline hBWlarge z hz)
                              (e z hz)))| ≤
                          CmarkedFinal * B.w * (1 / (p.1 : ℝ)) :=
  exists_paperFineMesh_cutoff_eventually_canonical_lemma86 cMesh hcMesh

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
