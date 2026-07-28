import Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal
import Erdos390.WholePaper.BankPaperCanonicalActualMomentReadyEventually

/-!
# Canonical Section 9 parameter synchronization

The Section 9 clean-list width has to dominate the finite anchor prefix,
whereas the tangent-compatible exceptional exponent depends on that width.
The depth-first combined-charge terminal removes this apparent cycle:
first choose the capacity depth from `c`, then choose one width above the
named cutoffs collected by this connector, and only then specialize the
tangent parameter.

This connector uses the paper-range value `r0 = 5 / 4`.  It also records
the eventual scale inequalities consumed by the absorbed Section 9
terminal.  No identification with the independently selected
`bankPaperCapacitySelectedDepth` is asserted.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-- Choose the combined-charge capacity depth first, then synchronize one
canonical Section 9 width and the explicit paper-range tangent ratio
`r0 = 5 / 4`.

The width dominates the anchor prefix, the verified reciprocal-sum cutoff,
the canonical Mertens base, and the actual three-moment cutoff.  The final
eventual package contains the central-anchor threshold and the elementary
scale comparisons required by the absorbed Section 9 continuation. -/
theorem exists_bankPaperCanonicalSectionNineParameterSynchronization
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∃ W : ℕ,
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        tangentSelbergMertensBase ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        ∃ r0 : ℝ,
          1 < r0 ∧
          r0 < 3 / 2 ∧
          r0 < 2 ∧
          IsPaperCombinedTangentDeltaStar c W r0
              (paperCombinedTangentDeltaStar c W r0) ∧
            BankPaperCombinedChargeTerminalAtDepth c
                (paperCombinedTangentDeltaStar c W r0) depth ∧
              ∀ᶠ n : ℕ in atTop,
                centralAnchorCutoffThreshold depth ≤ n ∧
                  W ≤ yNat n ∧
                  yNat n < centralAnchorCutoff depth n ∧
                  0 < n ∧
                  (yNat n : ℝ) ≤ (n : ℝ) ∧
                  (yNat n : ℝ) ^ 2 ≤ (n : ℝ) := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice hc
  let W : ℕ :=
    max (2 * depth + 1)
      (max tangentSelbergMertensBase canonicalActualMomentCutoff)
  have hprefix : 2 * depth + 1 ≤ W := by
    dsimp only [W]
    exact le_max_left _ _
  have hMertensBase : tangentSelbergMertensBase ≤ W := by
    dsimp only [W]
    exact
      (le_max_left tangentSelbergMertensBase
        canonicalActualMomentCutoff).trans (le_max_right _ _)
  have hMoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W]
    exact
      (le_max_right tangentSelbergMertensBase
        canonicalActualMomentCutoff).trans (le_max_right _ _)
  have htwo : 2 ≤ W :=
    tangentSelbergMertensBase_ge_two.trans hMertensBase
  have hReciprocal : fullReciprocalSumUniformCutoff ≤ W :=
    tangentSelbergMertensBase_ge_cutoff.trans hMertensBase
  let r0 : ℝ := 5 / 4
  have hr0one : 1 < r0 := by
    norm_num [r0]
  have hr0three : r0 < 3 / 2 := by
    norm_num [r0]
  have hr0two : r0 < 2 := by
    norm_num [r0]
  have hterminal := huniform W r0 hr0two
  have hscale :
      ∀ᶠ n : ℕ in atTop,
        centralAnchorCutoffThreshold depth ≤ n ∧
          W ≤ yNat n ∧
          yNat n < centralAnchorCutoff depth n ∧
          0 < n ∧
          (yNat n : ℝ) ≤ (n : ℝ) ∧
          (yNat n : ℝ) ^ 2 ≤ (n : ℝ) := by
    filter_upwards [
        eventually_ge_atTop (centralAnchorCutoffThreshold depth),
        eventually_bankAnchor_fixed_le_yNat W,
        eventually_yNat_lt_centralAnchorCutoff depth,
        eventually_ge_atTop 1]
        with n hnCutoff hWy hyCutoff hn
    have hnPos : 0 < n := by omega
    have hyOne : 1 ≤ yNat n := by
      exact (by omega : 1 ≤ W).trans hWy
    have hySqNat : yNat n * yNat n ≤ n :=
      bankAnchor_yNat_mul_self_le_self hn
    have hyLeNat : yNat n ≤ n := by
      calc
        yNat n = yNat n * 1 := (Nat.mul_one _).symm
        _ ≤ yNat n * yNat n := Nat.mul_le_mul_left _ hyOne
        _ ≤ n := hySqNat
    have hyLe : (yNat n : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hyLeNat
    have hySqCast :
        ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hySqNat
    have hySq : (yNat n : ℝ) ^ 2 ≤ (n : ℝ) := by
      simpa only [Nat.cast_mul, pow_two] using hySqCast
    exact ⟨hnCutoff, hWy, hyCutoff, hnPos, hyLe, hySq⟩
  exact
    ⟨depth, hdepth, W, htwo, hprefix, hReciprocal, hMertensBase,
      hMoment, r0, hr0one, hr0three, hr0two, hterminal.1,
      hterminal.2, hscale⟩

end

end Erdos390.WholePaper
