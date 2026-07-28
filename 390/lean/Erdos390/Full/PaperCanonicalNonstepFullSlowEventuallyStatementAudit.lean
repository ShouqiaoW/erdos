import Erdos390.Full.PaperCanonicalNonstepFullSlowEventually

/-!
Expanded statement audit for the final full-valuation non-step slow-row
terminal.  The source restatement exposes the paper scale and the complete
outer parameter order rather than relying on a theorem-name alias.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs

noncomputable section

example : ∀ r : ℝ, 0 < r →
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
              |B.normalizedBandCovarianceRow xi B.slowScore i -
                  B.referenceSlowRow i| ≤
                r * B.w * B.bandCenter i := by
  exact forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference

end

end Erdos390.Full.PaperBridgeFit.BridgeData

#print Erdos390.Full.PaperBridgeFit.BridgeData.forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference
