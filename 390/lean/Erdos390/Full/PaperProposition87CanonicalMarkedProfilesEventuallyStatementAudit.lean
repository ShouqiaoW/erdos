import Erdos390.Full.PaperProposition87CanonicalMarkedProfilesEventually

/-!
# Expanded statement audit for the canonical moving-prime marked row

The target `Delta` occurs *inside* the eventual quantifier.  Thus one common
ambient cutoff works for every finite-`n` rough-stage target; the statement
is not merely the weaker `forall Delta, eventually n` assertion.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperGuardCensus
open PaperWeightedInverseExport RegularMeshPrimeCutoffs

namespace BridgeData

example
    (I : PhysicalIntervals) (U : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {CinvOrd Tband targetScale gammaSlow Creg : ℝ},
      0 ≤ CinvOrd → 0 ≤ Tband → 0 ≤ targetScale →
      0 < gammaSlow → 0 ≤ Creg →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
      (∀ h, ∀ p ∈ (Phead h).primes, p ≤ W) →
      ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          (hBn : B.sampleData.n = n) →
          (hBW : B.sampleData.W = W) →
          (hBWlarge : 1 < B.sampleData.W) →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
                B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (Delta : Fin (M.cellCount + 1) → ℝ),
            ∀ (T : BarycentricTarget B.sampleData),
              (hTmargin : marginFloor ≤ T.cellMassMargin) →
              (hbaseline : B.baseline = T.baseline) →
              ∀ {gammaFull : ℝ}, 0 < gammaFull →
              (hFull : ∀ z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ),
                B.vectorFamily.HasCovarianceGap gammaFull
                  (B.effectiveParamEquiv z)) →
              ∀ (e : ∀ (z : B.EffectiveParamSpace),
                z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                  B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
              (he : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                e z hz q = B.actualBandSchurLinearMap
                  (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) q) →
              (hvariance : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                gammaSlow * B.w ^ 2 ≤ B.actualTwoStageCompensatedVariance
                  (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) (e z hz)) →
              (htarget : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                |B.compensatedNormalizedTarget (B.effectiveParamEquiv z)
                  (B.canonicalEffectiveNuisanceGamma_pos
                    I U (3 * (a : ℝ)) T)
                  (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                    hlowerOne hupperU
                    (by intro sigma; rw [hcanonical]; rfl)
                    (by intro sigma; rw [hcanonical]; rfl)
                    T hbaseline hBWlarge z hz) (e z hz) Delta| ≤
                    B.w * targetScale) →
              (hinvOrd : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                ‖(e z hz).symm v‖ ≤ CinvOrd * ‖v‖) →
              (htargetBand :
                ‖B.projectedNormalizedTargetBand Delta‖ ≤ Tband) →
              (hsharp : ∀ (z : B.EffectiveParamSpace)
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)),
                paperSharpNorm B.harmonicMass B.bandCenter
                  (B.partition.center_ne_zero B.n_gt_one)
                  (B.actualBandRegression (B.effectiveParamEquiv z)
                    (B.canonicalEffectiveNuisanceGamma_pos
                      I U (3 * (a : ℝ)) T)
                    (B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                      hlowerOne hupperU
                      (by intro sigma; rw [hcanonical]; rfl)
                      (by intro sigma; rw [hcanonical]; rfl)
                      T hbaseline hBWlarge z hz) (e z hz)) ≤ Creg * B.w) →
              ∀ (monitoredPrimes : Finset ℕ),
                (∀ p ∈ monitoredPrimes,
                  p ∈ primeBand B.sampleData.n B.sampleData.W) →
                ∀ p ∈ monitoredPrimes,
                  ∀ z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ),
                  |B.vectorFamily.scalarFamily.covariance
                    (B.markedValuation p)
                    (fun m ↦ B.vectorFamily.scalarFamily.score m
                      (B.vectorFamily.vectorField
                        (B.targetVector Delta)
                        (B.effectiveParamEquiv z)))
                    (B.effectiveParamEquiv z)| ≤ Crow / (p : ℝ) := by
  exact exists_cutoff_eventually_canonical_movingPrime_markedRow_of_schurSplice
    I U hU hlowerOne hupperU Cprom Cbank ledger

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
