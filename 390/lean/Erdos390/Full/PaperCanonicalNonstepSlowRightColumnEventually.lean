import Erdos390.Full.PaperCanonicalNonstepFullSlowEventually
import Erdos390.Full.PaperCanonicalReferenceSlowEventually

/-!
# Literal canonical slow right column

The preceding relative full/reference approximation is combined with the
direct Dickman reference-row bound.  The result is the literal full
valuation slow column at paper scale, with no step-function replacement and
no profile, transfer, row-rate, or moving-low assumptions at the interface.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus RegularMeshPrimeCutoffs

namespace BridgeData

/-- Fully discharged `O(w * alpha_i)` bound for the literal full-valuation
slow right column.  The cutoff is selected before `delta`, `eta`, the mesh,
head data, and the tilt box. -/
theorem exists_global_cutoff_eventually_canonical_nonstepSlowRightColumn_le :
    ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
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
  obtain ⟨CF, Cprod, hCF, hCprod, Wreference, hReferenceMain⟩ :=
    exists_global_cutoff_eventually_canonical_referenceSlowRow_le
  obtain ⟨Wfull, hFullMain⟩ :=
    forall_accuracy_exists_cutoff_eventually_canonical_fullSlowRow_sub_reference
      (1 : ℝ) (by norm_num)
  let W₀ : ℕ := max Wreference Wfull
  refine ⟨CF, Cprod, hCF, hCprod, W₀, ?_⟩
  intro W hW delta eta hdelta M Head _instFintype _instDecidable
    _instNonempty Phead hhead I Cmax hlowerOne hupperMax
    Cprom Cbank ledger Acoef Aphys hAcoef hAphys
  have hWreference : Wreference ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWfull : Wfull ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hReference := hReferenceMain W hWreference hdelta M
  have hFull := hFullMain W hWfull hdelta M Phead hhead I Cmax
    hlowerOne hupperMax Cprom Cbank ledger Acoef Aphys hAcoef hAphys
  filter_upwards [hReference, hFull] with n hReferenceN hFullN
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    xi heta hphys i
  have href := hReferenceN B hBn hBW hpartition hscale i
  have hfull := hFullN B hBn hBW hsep hremaining hcanonical
    hpartition hscale xi heta hphys i
  calc
    |B.normalizedBandCovarianceRow xi B.slowScore i| =
        |(B.normalizedBandCovarianceRow xi B.slowScore i -
            B.referenceSlowRow i) + B.referenceSlowRow i| := by
      congr 1
      ring
    _ ≤ |B.normalizedBandCovarianceRow xi B.slowScore i -
            B.referenceSlowRow i| + |B.referenceSlowRow i| :=
      abs_add_le _ _
    _ ≤ (1 : ℝ) * B.w * B.bandCenter i +
        (CF + 7 * Cprod) *
          B.w * B.bandCenter i := add_le_add hfull href
    _ = (1 + CF + 7 * Cprod) *
          B.w * B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
