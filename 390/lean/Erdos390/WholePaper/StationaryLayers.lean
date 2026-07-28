import Erdos390.WholePaper.Constants
import Erdos390.WholePaper.PrimeLayerCounts

/-!
# Stationary prime layers

For a fixed row `r`, Section 3 uses the prime interval
`n / (r + 1) < p ≤ 2n / (2r + 1)`.  The definition below records the
endpoints by cross-multiplied natural-number inequalities, so there is no
rounding ambiguity.  Its cardinality is then identified with the exact
prime-counting difference to which the fixed-interval PNT applies.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The stationary prime layer in row `r`, with open lower endpoint and
closed upper endpoint.  Both endpoint conditions are recorded as exact
integer inequalities. -/
def stationaryPrimeLayer (n r : ℕ) : Finset ℕ :=
  (Finset.range (2 * n + 1)).filter fun p ↦
    p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n

@[simp]
theorem mem_stationaryPrimeLayer {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n := by
  simp only [stationaryPrimeLayer, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact fun hp ↦ hp.2
  · intro hp
    have hpLe : p ≤ 2 * n :=
      (Nat.le_mul_of_pos_right p (by omega : 0 < 2 * r + 1)).trans hp.2.2
    exact ⟨by omega, hp⟩

/-- The cross-multiplied definition is exactly the paper's real interval
`n / (r + 1) < p ≤ 2n / (2r + 1)`. -/
theorem mem_stationaryPrimeLayer_iff_real {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧
        (n : ℝ) / ((r : ℝ) + 1) < (p : ℝ) ∧
        (p : ℝ) ≤ (2 * (n : ℝ)) / (2 * (r : ℝ) + 1) := by
  rw [mem_stationaryPrimeLayer]
  constructor
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨hpPrime, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      exact_mod_cast hpLower
    · rw [le_div_iff₀ (by positivity)]
      exact_mod_cast hpUpper
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨hpPrime, ?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)] at hpLower
      exact_mod_cast hpLower
    · rw [le_div_iff₀ (by positivity)] at hpUpper
      exact_mod_cast hpUpper

private theorem stationaryPrimeLayer_eq_filter_Ioc (n r : ℕ) :
    stationaryPrimeLayer n r =
      (Finset.Ioc (n / (r + 1)) ((2 * n) / (2 * r + 1))).filter Nat.Prime := by
  ext p
  simp only [mem_stationaryPrimeLayer, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    exact ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).2 hpLower,
      (Nat.le_div_iff_mul_le (by omega)).2 hpUpper⟩, hpPrime⟩
  · rintro ⟨⟨hpLower, hpUpper⟩, hpPrime⟩
    exact ⟨hpPrime, (Nat.div_lt_iff_lt_mul (by omega)).1 hpLower,
      (Nat.le_div_iff_mul_le (by omega)).1 hpUpper⟩

private theorem card_filter_prime_Ioc {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  have hdiff :
      (Finset.Ioc a b).filter Nat.Prime =
        (Finset.range (b + 1)).filter Nat.Prime \
          (Finset.range (a + 1)).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Finset.mem_range, hp, and_true]
      omega
    · simp [hp]
  have hsubset :
      (Finset.range (a + 1)).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.add_le_add_right hab 1), hp.2⟩
  rw [hdiff, Finset.card_sdiff_of_subset hsubset]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

private theorem stationary_lower_natFloor (n r : ℕ) :
    ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ = n / (r + 1) := by
  have harg :
      ((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ) =
        (n : ℝ) / ((r + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [harg]
  exact Nat.floor_div_eq_div n (r + 1)

private theorem stationary_upper_natFloor (n r : ℕ) :
    ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ =
      (2 * n) / (2 * r + 1) := by
  have harg :
      ((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ) =
        ((2 * n : ℕ) : ℝ) / ((2 * r + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [harg]
  exact Nat.floor_div_eq_div (2 * n) (2 * r + 1)

private theorem stationary_endpoint_le (r : ℕ) :
    (1 : ℝ) / ((r : ℝ) + 1) ≤
      2 / (2 * (r : ℝ) + 1) := by
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

/-- Exact cardinality of a stationary layer as a difference of prime-counting
functions at the two floored endpoints. -/
theorem stationaryPrimeLayer_card (n r : ℕ) :
    (stationaryPrimeLayer n r).card =
      Nat.primeCounting
          ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ -
        Nat.primeCounting
          ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ := by
  have hfloor :
      ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ ≤
        ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ :=
    Nat.floor_mono
      (mul_le_mul_of_nonneg_right (stationary_endpoint_le r) (Nat.cast_nonneg n))
  rw [stationaryPrimeLayer_eq_filter_Ioc]
  rw [stationary_lower_natFloor, stationary_upper_natFloor] at hfloor ⊢
  exact card_filter_prime_Ioc hfloor

/-- For every fixed paper row `r ≥ 1`, the stationary layer has asymptotic
mass `alpha r` after normalization by `n / log n`. -/
theorem stationaryPrimeLayer_card_normalized_tendsto (r : ℕ) (_hr : 1 ≤ r) :
    Tendsto
      (fun n : ℕ ↦
        ((stationaryPrimeLayer n r).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (alpha r : ℝ)) := by
  have ha : 0 < (1 : ℝ) / ((r : ℝ) + 1) := by positivity
  have hinterval :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : ℝ) / ((r : ℝ) + 1))
      (b := (2 : ℝ) / (2 * (r : ℝ) + 1))
      ha (stationary_endpoint_le r)
  have halpha :
      (2 : ℝ) / (2 * (r : ℝ) + 1) -
          1 / ((r : ℝ) + 1) =
        (alpha r : ℝ) := by
    simpa using
      congrArg (fun q : ℚ ↦ (q : ℝ)) (two_div_sub_one_div_eq_alpha r)
  simpa only [stationaryPrimeLayer_card, halpha] using hinterval

end

end Erdos390.WholePaper
