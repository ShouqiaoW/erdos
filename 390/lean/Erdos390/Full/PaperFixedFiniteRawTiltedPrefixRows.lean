import Erdos390.Full.PaperRawTiltedPrefixRow
import Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted

/-!
# A common raw tilted prefix rate for a fixed finite family of cells

The canonical bridge has finitely many head/physical cells.  This file takes
the finite sum of the independently proved cell rates, producing one
nonnegative rate and one threshold that work simultaneously in every cell.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination
open PaperRawTiltedPrefixRow
open PaperRawTiltedPrefixRowUnrestricted

noncomputable section

variable {Cell : Type*} [Fintype Cell]

theorem exists_uniform_fixedFinite_rawCell_tilted_valuation_all_prefix_rate
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
            epsilon n / (p : ℝ) := by
  have hexists : ∀ c : Cell, ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
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
            epsilon n / (p : ℝ) := by
    intro c
    exact exists_uniform_rawCell_tilted_valuation_all_prefix_rate
      (H c) (hA c) (hAC c) (hC c) B W hB hW (hHeadLe c) hboxW
  choose epsilonCell hepsilonCell0 hepsilonCellRate Ncell hcell using hexists
  let epsilon : ℕ → ℝ := fun n ↦ ∑ c : Cell, epsilonCell c n
  let N₀ : ℕ := ∑ c : Cell, Ncell c
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact Finset.sum_nonneg fun c hc ↦ hepsilonCell0 c n
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hepsilonCellRate c)
    have hsum' : Tendsto (fun n : ℕ ↦
        ∑ c : Cell, epsilonCell c n * Real.log (L n))
        atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum'.congr'
    filter_upwards with n
    dsimp only [epsilon]
    rw [Finset.sum_mul]
  refine ⟨epsilon, hepsilon0, hepsilonRate, N₀, ?_⟩
  intro c n k p eta hN hpBand heta
  have hNc : Ncell c ≤ N₀ := by
    dsimp only [N₀]
    exact Finset.single_le_sum
      (fun d hd ↦ Nat.zero_le (Ncell d)) (Finset.mem_univ c)
  have hNcell : Ncell c ≤ n := hNc.trans hN
  let S := structuredCell (H c) (physicalBound (A c) n)
    (physicalBound (C c) n) (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  have hraw := hcell c (n := n) (k := k) (p := p)
    eta hNcell hpBand heta hS
  have hcellLe : epsilonCell c n ≤ epsilon n := by
    dsimp only [epsilon]
    exact Finset.single_le_sum
      (fun d hd ↦ hepsilonCell0 d n) (Finset.mem_univ c)
  have hpR : (0 : ℝ) ≤ p := by positivity
  simpa only [S] using
    hraw.trans (div_le_div_of_nonneg_right hcellLe hpR)

/-- Fixed-finite aggregation of the parameter-order-safe unrestricted raw
row. -/
theorem exists_uniform_fixedFinite_rawCell_tilted_valuation_all_prefix_rate_unrestricted
    (H : Cell → Pattern) (A C : Cell → ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c)
    (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ c, ∀ q ∈ (H c).primes, q ≤ W) :
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
            epsilon n / (p : ℝ) := by
  have hexists : ∀ c : Cell, ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
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
            epsilon n / (p : ℝ) := by
    intro c
    exact exists_uniform_rawCell_tilted_valuation_all_prefix_rate_unrestricted
      (H c) (hA c) (hAC c) (hC c) B W hB hW (hHeadLe c)
  choose epsilonCell hepsilonCell0 hepsilonCellRate Ncell hcell using hexists
  let epsilon : ℕ → ℝ := fun n ↦ ∑ c : Cell, epsilonCell c n
  let N₀ : ℕ := ∑ c : Cell, Ncell c
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    dsimp only [epsilon]
    exact Finset.sum_nonneg fun c hc ↦ hepsilonCell0 c n
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hepsilonCellRate c)
    have hsum' : Tendsto (fun n : ℕ ↦
        ∑ c : Cell, epsilonCell c n * Real.log (L n))
        atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum'.congr'
    filter_upwards with n
    dsimp only [epsilon]
    rw [Finset.sum_mul]
  refine ⟨epsilon, hepsilon0, hepsilonRate, N₀, ?_⟩
  intro c n k p eta hN hpBand heta
  have hNc : Ncell c ≤ N₀ := by
    dsimp only [N₀]
    exact Finset.single_le_sum
      (fun d hd ↦ Nat.zero_le (Ncell d)) (Finset.mem_univ c)
  let S := structuredCell (H c) (physicalBound (A c) n)
    (physicalBound (C c) n) (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  have hraw := hcell c (n := n) (k := k) (p := p)
    eta (hNc.trans hN) hpBand heta hS
  have hcellLe : epsilonCell c n ≤ epsilon n := by
    dsimp only [epsilon]
    exact Finset.single_le_sum
      (fun d hd ↦ hepsilonCell0 d n) (Finset.mem_univ c)
  have hpR : (0 : ℝ) ≤ p := by positivity
  simpa only [S] using
    hraw.trans (div_le_div_of_nonneg_right hcellLe hpR)

end

end Erdos390.Full.PaperFixedFiniteRawTiltedPrefixRows
