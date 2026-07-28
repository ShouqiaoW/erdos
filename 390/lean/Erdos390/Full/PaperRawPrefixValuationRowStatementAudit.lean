import Erdos390.Full.PaperRawPrefixValuationRow

/-!
# Independent statement-shape audit: raw valuation moving-prefix row

The examples below restate the exported conclusions without using any
abbreviation for their hypotheses.  In particular, the terminal row has no
assumed covariance estimate: its only structural inputs are the fixed head
pattern, the physical interval, and the lower cutoff separating the head
from the moving prime band.
-/

open Filter Topology

namespace Erdos390.Full.PaperRawPrefixValuationRowStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells FiniteProbability
open ValuationCutoff PaperPrimePowerTailLedger
open PaperRawPrefixValuationRow

noncomputable section

example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k p : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      p ∈ primeBand n W →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covariance
            (fun m : S ↦ valuation p (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
          (2 * K / L n) * (1 / (p : ℝ)) +
            (4 * G * (cutoffScale W * L n) ^ 2) /
              ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) :=
  exists_uniform_rawCell_valuation_prefix_bound
    H hA hAC hC W hW hHeadLe

example (K G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (p : ℝ) *
          ((2 * K / L n) * (1 / (p : ℝ)) +
            (4 * G * (cutoffScale W * L n) ^ 2) /
              ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
        rawValuationPrefixRateMajorant K G W n :=
  eventually_rawValuationPrefix_rowCoefficient_le K G W hG hW

example (K G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      rawValuationPrefixRateMajorant K G W n * Real.log (L n))
      atTop (nhds 0) :=
  tendsto_rawValuationPrefixRateMajorant_mul_logL_zero K G W hG hW

end

end Erdos390.Full.PaperRawPrefixValuationRowStatementAudit
