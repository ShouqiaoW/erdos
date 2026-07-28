import Erdos390.Full.PaperCanonicalLemma84GapNuisanceEventually
import Erdos390.Full.PaperCanonicalActualSchurSharpOrdinaryEventually

/-!
# Closed canonical form of paper Lemma 8.4

This is the umbrella statement matching the three conclusions of the paper's
moving-low-cell arithmetic quotient lemma.  It combines the literal
`q_n`-scaled quotient gap and finite nuisance coercivity with an equivalence
which is exactly the actual finite nuisance-Schur band map.  The sharp and
ordinary inverse estimates apply to that same equivalence.

No anchor, convergence rate, row estimate, perturbation smallness condition,
or abstract inverse is exposed at the call site.  Both mesh parameters remain
independent and the displayed fineness condition is `delta + eta`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 1000000 in
/-- Assumption-free, paper-order, literal finite-`n` Lemma 8.4 terminal. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma84 :
    ∃ kappa : ℝ, 0 < kappa ∧
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
                (hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline),
                ∃ e : ∀ (z : B.EffectiveParamSpace),
                    z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                      B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                  (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)),
                    let xi : B.ParamSpace := B.effectiveParamEquiv z
                    let gamma : ℝ :=
                      B.canonicalEffectiveNuisanceGamma
                        I U (3 * (a : ℝ)) T
                    let hgamma : 0 < gamma :=
                      B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T
                    let hgap : ∀ v, gamma * ‖v‖ ^ 2 ≤
                        inner ℝ v
                          (B.nuisanceCovarianceOperator xi v) := by
                      intro v
                      simpa only [gamma, xi] using
                        B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
                          hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz v
                    (0 < gamma) ∧
                    (∀ v, gamma * ‖v‖ ^ 2 ≤
                      inner ℝ v (B.nuisanceCovarianceOperator xi v)) ∧
                    ∀ (b : Fin (M.cellCount + 1) → ℝ) (mu : ℝ),
                      kappa * B.q *
                          (⨅ lambda : ℝ,
                            ∑ j : Fin (M.cellCount + 1),
                              B.harmonicMass j *
                                |b j - lambda * B.bandCenter j| ^ 2) ≤
                        B.q * (B.tiltedLaw xi).covariance
                          (B.nuisanceResidualScore xi hgamma hgap
                            (B.primeValuationScore
                              (B.partition.data.residual b mu)))
                          (B.nuisanceResidualScore xi hgamma hgap
                            (B.primeValuationScore
                              (B.partition.data.residual b mu)))) ∧
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
  obtain ⟨kappa, hkappa, gapTol, hgapTol, Wgap, hGap⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma84_gap_nuisance
  obtain ⟨inverseTol, hinverseTol, Csharp, hCsharp,
      Cordinary, hCordinary, Winverse, hInverse⟩ :=
    exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary
  let meshTol : ℝ := min gapTol inverseTol
  let W₀ : ℕ := max Wgap Winverse
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hgapTol hinverseTol
  refine ⟨kappa, hkappa, meshTol, hmeshTol,
    Csharp, hCsharp, Cordinary, hCordinary, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidable _instNonempty Phead hPhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmargin
  have hWgap : Wgap ≤ W := (le_max_left Wgap Winverse).trans hW
  have hWinverse : Winverse ≤ W := (le_max_right Wgap Winverse).trans hW
  have hGapFine : delta + eta ≤ gapTol :=
    hfine.trans (min_le_left gapTol inverseTol)
  have hInverseFine : delta + eta ≤ inverseTol :=
    hfine.trans (min_le_right gapTol inverseTol)
  have hGapN := hGap W hWgap M hdelta hGapFine
    (Head := Head) Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hInverseN := hInverse W hWinverse M hdelta hInverseFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hGapN, hInverseN] with n hGapAt hInverseAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline
  have hGapB := hGapAt B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition T hTmargin hbaseline
  obtain ⟨e, he, hsharp, hordinary⟩ :=
    hInverseAt B hBn hBW hBWlarge hsep hremaining hcanonical
      hpartition T hTmargin hbaseline
  exact ⟨e, hGapB, he, hsharp, hordinary⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
