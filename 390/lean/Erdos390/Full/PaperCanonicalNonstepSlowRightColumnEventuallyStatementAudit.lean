import Erdos390.Full.PaperCanonicalNonstepSlowRightColumnEventually

/-!
Expanded statement audit for the universal literal full-valuation slow
right column.  The coefficient is independent of `delta`, `eta`, the mesh,
head data, and the effective box.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit.BridgeData

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs

example : ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
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
            B.partition = Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          B.w = delta + eta →
          ∀ (xi : B.ParamSpace),
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            |xi MomentCoord.physical| ≤ Aphys →
            ∀ i : Fin (M.cellCount + 1),
              |B.normalizedBandCovarianceRow xi B.slowScore i| ≤
                (1 + CF + 7 * Cprod) *
                  B.w * B.bandCenter i := by
  exact exists_global_cutoff_eventually_canonical_nonstepSlowRightColumn_le

end

end Erdos390.Full.PaperBridgeFit.BridgeData

#print Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_nonstepSlowRightColumn_le
