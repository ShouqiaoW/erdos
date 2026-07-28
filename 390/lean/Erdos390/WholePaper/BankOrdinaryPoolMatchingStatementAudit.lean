import Erdos390.WholePaper.BankOrdinaryPoolMatching

/-! # Expanded statement audit for actual ordinary pool assignment -/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryAvailablePairs n M pool ⊆
      bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1) :=
  bankOrdinaryAvailablePairs_subset_eligible n M pool

/-- Each of the two literal orientation pools retains at least the rounded-down
half of the available marker count. -/
example (n M : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankEligibleMarkerCount
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale pool.1)) / 2 ≤
      (bankOrdinaryAvailablePairs n M pool).card := by
  simpa only [bankOrdinaryPoolCapacity] using
    bankOrdinaryPoolCapacity_ge_half_markerCount n M pool

/-- The orientation tag is not decorative: downward requests use the first
half and upward requests use the complementary half. -/
example (n M j : ℕ) :
    bankOrdinaryAvailablePairs n M (j, .downward) =
        bankOrientationPoolFirst
          (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j)) ∧
      bankOrdinaryAvailablePairs n M (j, .upward) =
        bankOrientationPoolSecond
          (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j)) := by
  exact ⟨rfl, rfl⟩

example {n M : ℕ} {pool pool' : BankOrdinaryOrientationPool}
    (hpools : pool ≠ pool') :
    Disjoint (bankOrdinaryAvailablePairs n M pool)
      (bankOrdinaryAvailablePairs n M pool') :=
  bankOrdinaryAvailablePairs_disjoint hpools

example {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    matching.matchedPair request ∈
      bankOrdinaryAvailablePairs n M
        (bankOrdinaryPaperRequestPool n request.1) :=
  matching.matchedPair_mem_available request

example {n M j : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (hpool : bankOrdinaryPaperRequestPool n request.1 = (j, .downward)) :
    matching.matchedPair request ∈
      bankOrientationPoolFirst
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j)) := by
  have havailable := matching.matchedPair_mem_available request
  rw [hpool] at havailable
  simpa only [bankOrdinaryAvailablePairs] using havailable

example {n M j : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n))
    (hpool : bankOrdinaryPaperRequestPool n request.1 = (j, .upward)) :
    matching.matchedPair request ∈
      bankOrientationPoolSecond
        (bankOrdinaryEligibleRelation n M (bankOrdinaryScale j)) := by
  have havailable := matching.matchedPair_mem_available request
  rw [hpool] at havailable
  simpa only [bankOrdinaryAvailablePairs] using havailable

/-- Literal expansion of eligibility for the numerical pair assigned to a
request.  In particular the marker is prime, the two exact scale windows and
smoothness condition hold, and the product is an actual tail occurrence. -/
example {n M : ℕ} (matching : BankOrdinaryPoolMatching n M)
    (request : ↑(bankOrdinaryPaperRequests n)) :
    0 < bankOrdinaryScale
        (bankOrdinaryPaperRequestPool n request.1).1 ∧
      (matching.matchedPair request).1.Prime ∧
      0 < (matching.matchedPair request).2 ∧
      InOrdinaryBankMarkerInterval n
        (bankOrdinaryScale
          (bankOrdinaryPaperRequestPool n request.1).1)
        (matching.matchedPair request).1 ∧
      InOrdinaryBankDonorWindow
        (bankOrdinaryScale
          (bankOrdinaryPaperRequestPool n request.1).1)
        (matching.matchedPair request).2 ∧
      (matching.matchedPair request).2 ∈
        Nat.smoothNumbers (yNat n + 1) ∧
      2 * n <
        (matching.matchedPair request).1 *
          (matching.matchedPair request).2 ∧
      (matching.matchedPair request).1 *
          (matching.matchedPair request).2 ≤ M := by
  simpa only [IsOrdinaryBankEligiblePair] using
    (mem_bankOrdinaryEligibleRelation.mp
      (matching.matchedPair_eligible request))

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ pool : BankOrdinaryOrientationPool,
      bankOrdinaryPoolDemand n pool ≤
        bankOrdinaryPoolCapacity n
          (upperEndpoint n (upperTailLength c n)) pool :=
  eventually_bankOrdinary_allPoolDemands_le_capacity hc

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankOrdinaryPoolMatching n
          (upperEndpoint n (upperTailLength c n)),
        Function.Injective matching.matchedPair ∧
          ∀ request : ↑(bankOrdinaryPaperRequests n),
            matching.matchedPair request ∈
              bankOrdinaryEligibleRelation n
                (upperEndpoint n (upperTailLength c n))
                (bankOrdinaryScale
                  (bankOrdinaryPaperRequestPool n request.1).1) :=
  eventually_exists_bankOrdinaryPaper_injective_assignment hc

/-- Fully expanded terminal audit: the global assignment is injective, lies in
the exact orientation half selected by each request, and consists of literal
eligible prime--smooth-donor tail occurrences. -/
example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankOrdinaryPoolMatching n
          (upperEndpoint n (upperTailLength c n)),
        Function.Injective matching.matchedPair ∧
          (∀ request : ↑(bankOrdinaryPaperRequests n),
            matching.matchedPair request ∈
              bankOrdinaryAvailablePairs n
                (upperEndpoint n (upperTailLength c n))
                (bankOrdinaryPaperRequestPool n request.1)) ∧
          ∀ request : ↑(bankOrdinaryPaperRequests n),
            0 < bankOrdinaryScale
                (bankOrdinaryPaperRequestPool n request.1).1 ∧
              (matching.matchedPair request).1.Prime ∧
              0 < (matching.matchedPair request).2 ∧
              InOrdinaryBankMarkerInterval n
                (bankOrdinaryScale
                  (bankOrdinaryPaperRequestPool n request.1).1)
                (matching.matchedPair request).1 ∧
              InOrdinaryBankDonorWindow
                (bankOrdinaryScale
                  (bankOrdinaryPaperRequestPool n request.1).1)
                (matching.matchedPair request).2 ∧
              (matching.matchedPair request).2 ∈
                Nat.smoothNumbers (yNat n + 1) ∧
              2 * n <
                (matching.matchedPair request).1 *
                  (matching.matchedPair request).2 ∧
              (matching.matchedPair request).1 *
                  (matching.matchedPair request).2 ≤
                upperEndpoint n (upperTailLength c n) := by
  filter_upwards [eventually_exists_bankOrdinaryPaper_injective_assignment hc]
      with n hmatching
  rcases hmatching with ⟨matching, hinjective, heligible⟩
  refine ⟨matching, hinjective, ?_, ?_⟩
  · exact matching.matchedPair_mem_available
  · intro request
    simpa only [IsOrdinaryBankEligiblePair] using
      (mem_bankOrdinaryEligibleRelation.mp (heligible request))

end

end Erdos390.WholePaper
