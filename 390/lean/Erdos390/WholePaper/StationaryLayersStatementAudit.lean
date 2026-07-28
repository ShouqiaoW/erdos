import Erdos390.WholePaper.StationaryLayers

/-!
# Expanded statement audit for stationary layers

These examples expose the endpoint conventions, finite set, prime-counting
difference, normalization, and rational row mass used by the terminal
stationary-layer theorem.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

example {n r p : ℕ} :
    p ∈ stationaryPrimeLayer n r ↔
      p.Prime ∧
        (n : ℝ) / ((r : ℝ) + 1) < (p : ℝ) ∧
        (p : ℝ) ≤ (2 * (n : ℝ)) / (2 * (r : ℝ) + 1) :=
  mem_stationaryPrimeLayer_iff_real

example (n r : ℕ) :
    ((Finset.range (2 * n + 1)).filter fun p ↦
        p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n).card =
      Nat.primeCounting
          ⌊((2 : ℝ) / (2 * (r : ℝ) + 1)) * (n : ℝ)⌋₊ -
        Nat.primeCounting
          ⌊((1 : ℝ) / ((r : ℝ) + 1)) * (n : ℝ)⌋₊ := by
  simpa only [stationaryPrimeLayer] using stationaryPrimeLayer_card n r

example (r : ℕ) (hr : 1 ≤ r) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.range (2 * n + 1)).filter fun p ↦
            p.Prime ∧ n < p * (r + 1) ∧
              p * (2 * r + 1) ≤ 2 * n).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop
      (nhds
        (((1 : ℚ) /
          (((r : ℚ) + 1) * (2 * (r : ℚ) + 1)) : ℚ) : ℝ)) := by
  simpa only [stationaryPrimeLayer, alpha] using
    stationaryPrimeLayer_card_normalized_tendsto r hr

end

end Erdos390.WholePaper
