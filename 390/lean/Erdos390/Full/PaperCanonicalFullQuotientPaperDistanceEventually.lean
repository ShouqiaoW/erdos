import Erdos390.Full.PaperCanonicalFullQuotientFineMeshEventually
import Erdos390.Full.PaperBandBestDistance

/-!
# Literal paper-distance form of the canonical full quotient gap

The canonical arithmetic theorem is proved using the explicit weighted
gauge projection.  This paper-facing wrapper keeps the two mesh parameters
independent, uses the displayed paper scale `delta + eta`, and rewrites the
conclusion as the literal infimum over the logarithmic null direction.
-/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus RegularMeshPrimeCutoffs
open Erdos390.Lemma84

namespace BridgeData

/-- Anchor-free, paper-scale, literal-infimum quotient gap. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_actualFullQuotientDistance :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
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
          ∀ (T : BarycentricTarget B.sampleData),
            marginFloor ≤ T.cellMassMargin →
            ∀ (hbaseline : B.baseline = T.baseline),
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
            kappa *
                (⨅ lambda : ℝ, ∑ j : Fin (M.cellCount + 1),
                  B.harmonicMass j *
                    |b j - lambda * B.bandCenter j| ^ 2) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, W₀, hmain⟩ :=
    exists_fineMesh_cutoff_eventually_canonical_actualFullQuotient
  refine ⟨kappa, hkappa, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hactualFine : delta + M.ratio ≤ meshTol :=
    (add_le_add_right M.ratio_le_eta delta).trans hfine
  intro Head _instFintype _instDecidable _instNonempty Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hevent := hmain W hW M hdelta hactualFine Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hevent] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline z hz
  have hraw := hn B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition T hTmargin hbaseline z hz
  dsimp only at hraw ⊢
  intro b mu
  have hbound := hraw b mu
  have hcenter : B.partition.data.centerEnergy ≠ 0 :=
    ne_of_gt (B.partition.centerEnergy_pos B.n_gt_one)
  rw [← B.partition.data.bestBandDistance_eq_bandNormSq_gaugePart
    b hcenter] at hbound
  rw [B.partition.data.bestBandDistance_eq_iInf b] at hbound
  simpa only [BridgeData.harmonicMass, BridgeData.bandCenter,
    ArithmeticBandGeometry.Partition.mass,
    ArithmeticBandGeometry.Partition.center] using hbound

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
