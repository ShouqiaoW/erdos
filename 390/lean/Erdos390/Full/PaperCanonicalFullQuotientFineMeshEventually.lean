import Erdos390.Full.PaperCanonicalFullQuotientEventually
import Erdos390.Full.RegularRelativeMeshInteriorAnchors
import Erdos390.Full.RegularMeshMomentBounds

/-!
# Anchor-free, two-parameter full quotient gap

This file removes the explicit interior-anchor input from the canonical
full-valuation quotient theorem.  Unlike older selected-mesh wrappers, the
statement keeps the paper's two independent mesh parameters `delta` and
`eta`.  The structural cutoff is chosen before both of them.
-/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 1200000 in
/-- Paper-order, every-fine-mesh form of the literal full quotient gap.
There are no caller-supplied anchors or analytic error estimates. -/
theorem exists_fineMesh_cutoff_eventually_canonical_actualFullQuotient :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
      delta + M.ratio ≤ meshTol →
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
            kappa * B.partition.data.bandNormSq
                (B.partition.data.gaugePart b) ≤
              (B.tiltedLaw xi).covariance
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu)))
                (B.nuisanceResidualScore xi hgamma hgap
                  (B.primeValuationScore
                    (B.partition.data.residual b mu))) := by
  obtain ⟨kappa, hkappa, W₀, hmain⟩ :=
    exists_structural_cutoff_eventually_canonical_actualFullQuotient
  let meshTol : ℝ := 1 / 16
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    norm_num
  refine ⟨kappa, hkappa, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hdeltaSmall : delta < (1 / 16 : ℝ) := by
    dsimp only [meshTol] at hfine
    linarith [M.ratio_pos]
  have hratioSmall : M.ratio < (1 / 16 : ℝ) := by
    dsimp only [meshTol] at hfine
    linarith [hdelta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hLower, hUpper, hMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  intro Head _instFintype _instDecidable _instNonempty
  exact hmain W hW M hdelta anchors hAnchors hLower hUpper hMass
    (Head := Head)

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
