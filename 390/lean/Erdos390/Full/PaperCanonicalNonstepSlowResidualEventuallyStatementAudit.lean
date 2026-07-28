import Erdos390.Full.PaperCanonicalNonstepSlowResidualEventually

/-!
Expanded statement audit for the fully discharged canonical Schur-projected
non-step slow row.  In particular, the retained row constant is universal;
the marked-row and moving-low rates occur only inside the proof and not in
this public interface.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit.BridgeData

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs

example : ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
    ∃ W₀ : ℕ, ∃ hW₀two : 2 ≤ W₀,
      ∀ W : ℕ, (hW : W₀ ≤ W) →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U),
        (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma) →
        (hupperU : ∀ sigma, I.upper sigma ≤ U) →
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank)
        (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            (hBn : B.sampleData.n = n) → (hBW : B.sampleData.W = W) →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining) →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData),
              (hTmargin : marginFloor ≤ T.cellMassMargin) →
              (hbaseline : B.baseline = T.baseline) →
              ∀ (z : B.EffectiveParamSpace),
                (hz : z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ)) →
                ∀ i : Fin (M.cellCount + 1),
                  |B.normalizedBandCovarianceRow
                      (B.effectiveParamEquiv z)
                      (B.nuisanceResidualScore
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall
                          I a hU hlowerOne hupperU
                          (by
                            intro sigma
                            rw [hcanonical]
                            rfl)
                          (by
                            intro sigma
                            rw [hcanonical]
                            rfl)
                          T hbaseline
                          (by rw [hBW]; omega) z hz)
                        B.slowScore) i| ≤
                    ((2 + CF + 7 * Cprod) * B.w) *
                      B.bandCenter i := by
  exact exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le

end

end Erdos390.Full.PaperBridgeFit.BridgeData

#print Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le
