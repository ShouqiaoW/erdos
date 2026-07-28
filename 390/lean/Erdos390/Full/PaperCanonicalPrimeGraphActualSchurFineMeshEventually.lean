import Erdos390.Full.PaperCanonicalPrimeGraphActualSchurEventually
import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-!
# Anchor-free paper-scale sharp inverse for the literal Schur map

The underlying canonical theorem already proves every analytic transfer but
exposes an interior anchor block as an argument.  A sufficiently fine
regular relative mesh supplies that block canonically.  This file performs
that construction and also replaces the actual mesh scale
`delta + M.ratio` by the paper's displayed upper scale `delta + eta`.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

/-- Anchor-free, two-parameter, paper-facing sharp inverse for the exact
finite nuisance-Schur band operator.  No row, profile, convergence, or
inverse estimate is assumed at the call site. -/
theorem exists_paperFineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse :
    ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ Cschur : ℝ, 0 < Cschur ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
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
                        (by
                          intro sigma
                          rw [hcanonical]
                          rfl)
                        (by
                          intro sigma
                          rw [hcanonical]
                          rfl)
                        T hbaseline hBWlarge z hz) q) ∧
                ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      ((e z hz).symm v) ≤
                    Cschur *
                      paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) v := by
  obtain ⟨meshTol, hmeshTol, Cschur, hCschur, W₀, hmain⟩ :=
    exists_cutoff_before_mesh_eventually_actualBandSchur_primeGraph_inverse
  let w₀ : ℝ := min meshTol (1 / 16)
  have hw₀ : 0 < w₀ := by
    dsimp only [w₀]
    positivity
  refine ⟨w₀, hw₀, Cschur, hCschur, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine Head _instFintype
    _instDecidableEq _instNonempty
  have hactualFine : delta + M.ratio ≤ meshTol := by
    calc
      delta + M.ratio ≤ delta + eta :=
        add_le_add_right M.ratio_le_eta delta
      _ ≤ w₀ := hfine
      _ ≤ meshTol := min_le_left _ _
  have hdeltaSmall : delta < (1 / 16 : ℝ) := by
    have hetaPos : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
    have hsum : delta + eta ≤ (1 / 16 : ℝ) :=
      hfine.trans (min_le_right _ _)
    linarith
  have hratioSmall : M.ratio < (1 / 16 : ℝ) := by
    have hsum : delta + M.ratio ≤ (1 / 16 : ℝ) :=
      calc
        delta + M.ratio ≤ delta + eta :=
          add_le_add_right M.ratio_le_eta delta
        _ ≤ w₀ := hfine
        _ ≤ (1 / 16 : ℝ) := min_le_right _ _
    linarith
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hLower, hUpper, hMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  exact hmain W hW M hdelta hactualFine anchors hAnchors hLower hUpper
    hMass Head

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
