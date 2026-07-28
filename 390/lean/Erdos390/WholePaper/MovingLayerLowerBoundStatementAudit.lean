import Erdos390.WholePaper.MovingLayerLowerBound

/-!
# Expanded statement audit for moving-layer lower-bound inputs

This exposes the literal four moving endpoint inequalities, the explicit
`n / log n` normalization, the exact thirteen-row constant, and the final
factorial valuation-difference forced by admissibility.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {h : ℕ → ℕ}
    (hh : Tendsto (fun n : ℕ ↦ (h n : ℝ) / (n : ℝ)) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦
        ((((Finset.Icc 1 13).biUnion (fun r ↦
          (Finset.range (2 * n + h n + 1)).filter (fun p ↦
            p.Prime ∧
              2 * n + h n < (2 * r + 2) * p ∧
              (2 * r + 1) * p ≤ 2 * n + h n ∧
              n < (r + 1) * p ∧ r * p ≤ n))).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))))
      atTop (nhds ((2014819799 : ℝ) / 5736673800)) := by
  have hlimit := movingPrimeUnion13_card_normalized_tendsto hh
  have hmass : (A13 : ℝ) = (2014819799 : ℝ) / 5736673800 := by
    rw [A13_eq]
    norm_num
  rw [hmass] at hlimit
  simpa only [movingPrimeUnion13, movingPrimeLayer] using hlimit

example {n h : ℕ} (hn : 392 ≤ n)
    (hAdmissible :
      ∃ factors : Finset ℕ,
        factors ⊆ Finset.Ioc n (2 * n + h) ∧
          factors.prod id = n.factorial) :
    ((Finset.Icc 1 13).biUnion (fun r ↦
      (Finset.range (2 * n + h + 1)).filter (fun p ↦
        p.Prime ∧
          2 * n + h < (2 * r + 2) * p ∧
          (2 * r + 1) * p ≤ 2 * n + h ∧
          n < (r + 1) * p ∧ r * p ≤ n))).card ≤
      ∑ ℓ ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) := by
  have hAdmissible' : IsAdmissibleEndpoint n (2 * n + h) := by
    simpa only [IsAdmissibleEndpoint, factorInterval] using hAdmissible
  have hforced :=
    movingPrimeUnion13_card_le_factorialValuationSub_of_admissible
      hn hAdmissible'
  simpa only [movingPrimeUnion13, movingPrimeLayer, smallPrimes] using hforced

end

end Erdos390.WholePaper
