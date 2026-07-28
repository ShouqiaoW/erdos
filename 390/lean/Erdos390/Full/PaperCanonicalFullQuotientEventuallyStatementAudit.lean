import Erdos390.Full.PaperCanonicalFullQuotientEventually

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel PaperGuardCensus
open RegularMeshPrimeCutoffs
open PaperLemma84StructuralCutoff

noncomputable section

/- Independently expanded terminal type.  In particular `W₀` precedes the
mesh, head patterns, and effective ball, while the conclusion is the literal
actual nuisance-Schur covariance for every arithmetic vector and `mu`. -/
example :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      ∀ (anchors : Finset (Fin M.cellCount))
        (_hAnchors : anchors.Nonempty)
        (_hIdealLower : ∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k)
        (_hIdealUpper : ∀ k ∈ anchors,
          M.upper k ≤ 1 - (1 / 8 : ℝ))
        (_hIdealMass : (1 : ℝ) / 8 ≤
          (∑ k ∈ anchors, M.width k) / 2),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ (Phead : Head → HeadPattern.Pattern)
        (_hhead : ∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W),
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
        (hupperU : ∀ sigma, I.upper sigma ≤ U),
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (a : NNReal) (marginFloor : ℝ) (_hmarginFloor : 0 < marginFloor),
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
          (_hBn : B.sampleData.n = n) (_hBW : B.sampleData.W = W)
          (hBWlarge : 1 < B.sampleData.W),
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
            B.partition = Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          ∀ (T : BarycentricTarget B.sampleData)
            (_hTmargin : marginFloor ≤ T.cellMassMargin)
            (hbaseline : B.baseline = T.baseline),
          ∀ (z : B.EffectiveParamSpace)
            (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)),
          let xi : B.ParamSpace := B.effectiveParamEquiv z
          let gamma : ℝ :=
            B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T
          let hgamma : 0 < gamma :=
            B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
          let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
              inner ℝ v (B.nuisanceCovarianceOperator xi v) := by
            intro v
            simpa only [gamma, xi] using
              B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz v
          ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
            kappa * B.partition.data.bandNormSq
                (B.partition.data.gaugePart b) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) :=
  exists_structural_cutoff_eventually_canonical_actualFullQuotient

end
end Erdos390.Full.PaperBridgeFit.BridgeData
