import Erdos390.Full.PaperRawTiltedValuationMeanRows

/-! # Statement-shape audit: raw full-valuation component means

The terminal theorem has an arbitrary fixed coefficient box after `W`, no
box-size condition on `W`, a reciprocal-prime row bound, and a rate which is
`o(1 / log L)`.
-/

open Filter Topology

namespace Erdos390.Full.PaperRawTiltedValuationMeanRowsStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination
open PaperRawTiltedValuationMeanRows

noncomputable section

variable {Cell : Type*} [Fintype Cell]

example
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hC_le : ∀ c, C c ≤ Cmax)
    (W : ℕ) (hW : 1 < W) (hHW : ∀ c, (H c).modulus ≤ W)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := fun c ↦ structuredCell (H c)
          (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
        ∀ hS : ∀ c, (S c).Nonempty, ∀ c c' : Cell,
          |((uniformOnFinset (S c) (hS c)).exponentialTilt
                (fun m : S c ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
              (fun m ↦ valuation p (m : ℕ)) -
            ((uniformOnFinset (S c') (hS c')).exponentialTilt
                (fun m : S c' ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).expect
              (fun m ↦ valuation p (m : ℕ))| ≤
            epsilon n / (p : ℝ) :=
  exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate
    H A C Cmax hA hAC hC hC_le W hW hHW B hB

end

end Erdos390.Full.PaperRawTiltedValuationMeanRowsStatementAudit
