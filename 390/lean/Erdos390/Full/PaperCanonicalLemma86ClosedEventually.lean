import Erdos390.Full.PaperCanonicalActualSlowRightRowEventually
import Erdos390.Full.PaperCanonicalLemma86Eventually

/-!
# Fixed-`delta` canonical slow-variance composition

This file records an intermediate composition of the two independently
audited eventual terminals for the literal slow right column and the
compensated slow variance.  The exported theorem no longer asks the caller
to supply a right-row estimate, but `delta` is fixed before its cutoff.
Consequently this is deliberately *not* the paper-order terminal Lemma 8.6;
the latter requires `W` to be chosen before `delta` and the mesh.  Its only
remaining analytic input is the sharp inverse furnished by Lemma 8.4 for
the same literal band-Schur map.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

/-- Fixed-`delta` intermediate with the slow right row discharged.  The
constants `gammaSlow`, `CrightRow`, and `W₀` are selected before the
particular mesh, head family, and effective ball, but after `delta`.  The
exact head condition is used only after `W` is fixed and implies the support
condition needed by the asymptotic estimates. -/
theorem exists_cutoff_eventually_canonicalLemma86_slow_of_inverse
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ (1 : ℝ) / 32)
    (Cinv : ℝ) (hCinv : 0 < Cinv) :
    ∃ gammaSlow : ℝ, 0 < gammaSlow ∧
      ∃ CrightRow : ℝ, 0 < CrightRow ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ (M : RegularRelativeMesh.Mesh delta delta),
        ∀ (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
        (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
        (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
        ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
          [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ),
        ∀ (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
          (a : NNReal) (marginFloor : ℝ),
        0 < marginFloor →
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
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining) →
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = Mesh.canonicalPartition M hdelta
                  B.n_gt_one hWne S) →
              (hscale : B.w = delta + M.ratio) →
              ∀ (T : BarycentricTarget B.sampleData),
                (hTmargin : marginFloor ≤ T.cellMassMargin) →
                (hbaseline : B.baseline = T.baseline) →
                ∀ (z : B.EffectiveParamSpace),
                  (hz : z ∈ closedBall
                    (0 : B.EffectiveParamSpace) (a : ℝ)) →
                  ∀ (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
                    (hinv : ∀ v,
                      paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one)
                          (e.symm v) ≤
                        Cinv *
                          paperSharpNorm B.harmonicMass B.bandCenter
                            (B.partition.center_ne_zero B.n_gt_one) v) →
                    gammaSlow * B.w ^ 2 ≤
                      B.actualTwoStageCompensatedVariance
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall
                          I a hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz)
                        e := by
  obtain ⟨CrightRow, hCrightRow, Wright, hright⟩ :=
    exists_cutoff_eventually_canonical_actualSlowRightRow hdelta
  obtain ⟨gammaSlow, hgammaSlow, Wslow, hslow⟩ :=
    exists_cutoff_eventually_canonicalLemma86_slow_of_schurSplice
      hdelta hdeltaSmall Cinv CrightRow hCinv hCrightRow.le
  let W₀ := max Wright Wslow
  refine ⟨gammaSlow, hgammaSlow, CrightRow, hCrightRow, W₀, ?_⟩
  intro W hW M anchors hAnchors hIdealLower hIdealUpper hIdealMass
    Head _instHead _instHeadDec _instHeadNonempty Phead hhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor
    hmarginFloor
  have hWright : Wright ≤ W := (le_max_left _ _).trans hW
  have hWslow : Wslow ≤ W := (le_max_right _ _).trans hW
  have hHeadLe : ∀ h, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hhead h p).mp hp |>.2
  have hrightEventually := hright W hWright M Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmarginFloor
  have hslowEventually := hslow W hWslow M anchors hAnchors
    hIdealLower hIdealUpper hIdealMass Phead I U hU hlowerOne hupperU
    Cprom Cbank ledger hHeadLe a marginFloor hmarginFloor
  filter_upwards [hrightEventually, hslowEventually] with
      n hrightN hslowN
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    hscale T hTmargin hbaseline z hz e hinv
  apply hslowN B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition hscale T hTmargin hbaseline z hz e hinv
  intro j
  exact hrightN B hBn hBW hBWlarge hsep hremaining hcanonical
    hpartition hscale T hTmargin hbaseline z hz j

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
