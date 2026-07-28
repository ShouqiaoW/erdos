import Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows

/-! # Independent statement-shape audit: fixed-finite raw prefix row -/

open Filter Topology

namespace Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRowsStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination
open PaperRawTiltedPrefixRow PaperFixedFiniteRawTiltedPrefixRows

noncomputable section

variable {Cell : Type*} [Fintype Cell]

example
    (H : Cell → Pattern) (A C : Cell → ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c)
    (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ q ∈ (H c).primes, q ≤ W)
    (hboxW : 2 * B ≤ Real.log (W : ℝ)) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ (c : Cell) {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) :=
  exists_uniform_fixedFinite_rawCell_tilted_valuation_all_prefix_rate
    H A C hA hAC hC B W hB hW hHeadLe hboxW

end

end Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRowsStatementAudit
