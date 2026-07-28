import Erdos390.Full.PaperRawTiltedPrefixRow

/-!
# Independent statement-shape audit: closed raw tilted prefix row

This restatement makes visible that density, Taylor smallness, the un-tilted
row, and the third-cumulant row are conclusions used internally, not
hypotheses of the terminal theorem.
-/

open Filter Topology

namespace Erdos390.Full.PaperRawTiltedPrefixRowStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination
open PaperRawTiltedPrefixRow

noncomputable section

example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hboxW : 2 * B ≤ Real.log (W : ℝ)) :
    ∃ epsilon : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → physicalBound A n < k →
        k ≤ physicalBound C n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) :=
  exists_uniform_rawCell_tilted_valuation_prefix_rate
    H hA hAC hC B W hB hW hHeadLe hboxW

/-- The exported terminal form is genuinely uniform over every prefix and
also makes nonnegativity of the common rate explicit. -/
example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hboxW : 2 * B ≤ Real.log (W : ℝ)) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) :=
  exists_uniform_rawCell_tilted_valuation_all_prefix_rate
    H hA hAC hC B W hB hW hHeadLe hboxW

end

end Erdos390.Full.PaperRawTiltedPrefixRowStatementAudit
