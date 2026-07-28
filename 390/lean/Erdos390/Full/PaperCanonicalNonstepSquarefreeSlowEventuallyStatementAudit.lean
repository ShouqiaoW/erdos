import Erdos390.Full.PaperCanonicalNonstepSquarefreeSlowEventually

/-!
Expanded interface audit for the canonical squarefree/reference slow-row
terminal.  In particular, the structural cutoff precedes `delta`, `eta`,
the mesh, head data, the tilt box, and the requested relative error, while
the displayed paper scale is exactly `delta + eta`.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs

noncomputable section

example :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
        (Phead : Head → HeadPattern.Pattern),
        (∀ h : Head, ∀ p : ℕ,
          p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ (I : PhysicalIntervals) (Cmax : ℝ),
        (∀ sigma, 1 ≤ I.lower sigma) →
        (∀ sigma, I.upper sigma ≤ Cmax) →
      ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
      ∀ (Acoef Aphys : ℝ), 0 ≤ Acoef → 0 ≤ Aphys →
      ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I
                  (ledger B.sampleData.n) hsep hremaining →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ (xi : B.ParamSpace),
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∀ i : Fin (M.cellCount + 1),
                |B.normalizedSquarefreeBandCovarianceRow
                    xi B.slowSquarefreeScore i - B.referenceSlowRow i| ≤
                  r * B.w * B.bandCenter i := by
  exact exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference

end


end Erdos390.Full.PaperBridgeFit.BridgeData

#print Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_squarefreeSlowRow_sub_reference
