import Erdos390.Full.PaperCanonicalPrimeGraphActualSchurSolutionEventually

/-!
# Expanded statement audit for the paper-literal Lemma 8.5 solution

This restatement checks independent mesh parameters `delta, eta`, the actual
scale `delta + M.ratio`, the exact Schur equation and uniqueness, and the
row-relative input/output estimates.  In particular `Csharp` precedes `W`,
the mesh, the head family, and the effective ball.
-/

open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit.BridgeData

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
open PaperGuardCensus RegularMeshPrimeCutoffs

example (C : ℝ) (hC : 0 < C) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
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
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline)
              (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall
                (0 : B.EffectiveParamSpace) (a : ℝ))
              (b : B.RawBandGauge),
              (∀ i : Fin (M.cellCount + 1),
                |b.1 i| ≤ C * (delta + M.ratio) * B.bandCenter i) →
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
                  Csharp * (delta + M.ratio) ∧
                ∀ i : Fin (M.cellCount + 1),
                  |q.1 i| ≤
                    Csharp * (delta + M.ratio) * B.bandCenter i :=
  exists_fineMesh_cutoff_eventually_actualBandSchur_coordinate_solution C hC

#check paperSharpNorm_le_iff_abs_coordinate_le
#check exists_unique_actualBandSchur_sharp_solution_of_equiv
#check exists_fineMesh_cutoff_eventually_unique_actualBandSchur_sharp_solution

end


end Erdos390.Full.PaperBridgeFit.BridgeData
