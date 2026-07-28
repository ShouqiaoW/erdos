import Erdos390.Full.PaperCanonicalPrimeGraphActualSchurFineMeshEventually
import Erdos390.Full.PaperCanonicalPrimeGraphActualSchurSolutionEventually
import Erdos390.Full.PaperPermittedRegularMesh

/-!
# Exact paper-scale coordinate form of Lemma 8.5

This file converts the literal sharp inverse for the actual nuisance-Schur
map into the paper's right-side/solution formulation.  Crucially, both the
hypothesis and conclusion use the displayed paper scale `delta + eta`, not
the smaller realized scale `delta + M.ratio`.
-/

open scoped BigOperators
open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
open PaperGuardCensus RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

/-- If a gauge right side is `O((delta+eta) alpha_i)`, the unique solution
of the literal actual Schur equation is uniformly
`O((delta+eta) alpha_i)`.  The solution constant is chosen before `W`, the
mesh, the effective box, and the eventual ambient threshold. -/
theorem exists_paperFineMesh_cutoff_eventually_actualBandSchur_coordinate_solution
    (cMesh C : ℝ) (_hcMesh : 0 < cMesh) (hC : 0 < C) :
    ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
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
              (hbaseline : B.baseline = T.baseline)
              (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ))
              (b : B.RawBandGauge),
              (∀ i : Fin (M.cellCount + 1),
                |b.1 i| ≤ C * (delta + eta) * B.bandCenter i) →
              let hgamma := B.canonicalEffectiveNuisanceGamma_pos
                I U (3 * (a : ℝ)) T
              let hgap := B.canonicalEffectiveNuisanceGap_on_closedBall I a
                hU hlowerOne hupperU
                (by intro sigma; rw [hcanonical]; rfl)
                (by intro sigma; rw [hcanonical]; rfl)
                T hbaseline hBWlarge z hz
              ∃ q : B.RawBandGauge,
                B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q = b ∧
                (∀ q' : B.RawBandGauge,
                  B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                    hgamma hgap q' = b → q' = q) ∧
                paperSharpNorm B.harmonicMass B.bandCenter
                    (B.partition.center_ne_zero B.n_gt_one) q ≤
                  Csharp * (delta + eta) ∧
                ∀ i : Fin (M.cellCount + 1),
                  |q.1 i| ≤
                    Csharp * (delta + eta) * B.bandCenter i := by
  obtain ⟨w₀, hw₀, Csolve, hCsolve, W₀, hmain⟩ :=
    @exists_paperFineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse
  let Csharp : ℝ := Csolve * C
  have hCsharp : 0 < Csharp := by
    dsimp only [Csharp]
    exact mul_pos hCsolve hC
  refine ⟨w₀, hw₀, Csharp, hCsharp, W₀, ?_⟩
  intro W hW delta eta M hdelta _hPermitted hfine Head _instFintype
    _instDecidableEq _instNonempty Phead hhead I U hU hlowerOne hupperU
    Cprom Cbank ledger a marginFloor hmargin
  have hevent := hmain W hW M hdelta hfine Head Phead hhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  filter_upwards [hevent] with n hn
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition T
    hTmargin hbaseline z hz b hb
  obtain ⟨e, he, hinv⟩ := hn B hBn hBW hBWlarge hsep hremaining
    hcanonical hpartition T hTmargin hbaseline
  dsimp only
  let hgamma := B.canonicalEffectiveNuisanceGamma_pos
    I U (3 * (a : ℝ)) T
  let hgap := B.canonicalEffectiveNuisanceGap_on_closedBall I a
    hU hlowerOne hupperU
    (by intro sigma; rw [hcanonical]; rfl)
    (by intro sigma; rw [hcanonical]; rfl)
    T hbaseline hBWlarge z hz
  have hsolution := B.exists_unique_actualBandSchur_sharp_solution_of_equiv
    (B.effectiveParamEquiv z) hgamma hgap (e z hz)
      (he z hz) (hinv z hz) b
  obtain ⟨q, hsolve, hunique, hqBase, _hcoordinateBase⟩ := hsolution
  have hw : 0 ≤ delta + eta := by
    have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
    positivity
  have hbSharp :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) b ≤
        C * (delta + eta) := by
    apply (B.paperSharpNorm_le_iff_abs_coordinate_le
      (mul_nonneg hC.le hw) b).2
    exact hb
  have hqSharp :
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ≤
        Csharp * (delta + eta) := by
    calc
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ≤
          Csolve * paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) b := hqBase
      _ ≤ Csolve * (C * (delta + eta)) :=
        mul_le_mul_of_nonneg_left hbSharp hCsolve.le
      _ = Csharp * (delta + eta) := by
        dsimp only [Csharp]
        ring
  refine ⟨q, hsolve, hunique, hqSharp, ?_⟩
  intro i
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) q i
  have hcenter : 0 ≤ B.bandCenter i := (B.bandCenter_pos i).le
  calc
    |q.1 i| ≤ |B.bandCenter i| *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q := hcoord
    _ ≤ B.bandCenter i * (Csharp * (delta + eta)) := by
      rw [abs_of_nonneg hcenter]
      exact mul_le_mul_of_nonneg_left hqSharp hcenter
    _ = Csharp * (delta + eta) * B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
