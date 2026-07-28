import Erdos390.WholePaper.NoAdmissibleBelowTwoN

/-!
# Expanded statement audit for the endpoint exclusion below `2n`

The examples below expose the literal stationary inequalities, finite
thirteen-layer union, nine-prime valuation sum, incidence inequality, and
the final eventual quantifier over every endpoint `M ≤ 2n`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {n r p : ℕ} (hn : 392 ≤ n) (hr : 1 ≤ r ∧ r ≤ 13)
    (hp : p.Prime ∧ n < p * (r + 1) ∧ p * (2 * r + 1) ≤ 2 * n) :
    n / p = r ∧ (2 * n) / p = 2 * r + 1 ∧
      (Nat.choose (2 * n) n).factorization p = 1 := by
  have hpLayer : p ∈ stationaryPrimeLayer n r :=
    mem_stationaryPrimeLayer.mpr hp
  exact ⟨div_eq_row_of_mem_stationaryPrimeLayer hpLayer,
    two_mul_div_eq_two_mul_row_add_one_of_mem_stationaryPrimeLayer hpLayer,
    centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer
      hn hr.2 hpLayer⟩

example :
    Tendsto
      (fun n : ℕ ↦
        ((((Finset.Icc 1 13).biUnion (fun r ↦
          (Finset.range (2 * n + 1)).filter (fun p ↦
            p.Prime ∧ n < p * (r + 1) ∧
              p * (2 * r + 1) ≤ 2 * n))).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))))
      atTop (nhds ((2014819799 : ℝ) / 5736673800)) := by
  have h := stationaryPrimeUnion13_card_normalized_tendsto
  have hmass : (A13 : ℝ) = (2014819799 : ℝ) / 5736673800 := by
    rw [A13_eq]
    norm_num
  rw [hmass] at h
  simpa only [stationaryPrimeUnion13, stationaryPrimeLayer] using h

example :
    Tendsto
      (fun n : ℕ ↦
        ((∑ ℓ ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
            (Nat.choose (2 * n) n).factorization ℓ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  simpa only [centralSmallPrimeValuationSum, smallPrimes] using
    centralSmallPrimeValuationSum_normalized_tendsto

example {n : ℕ} (hn : 392 ≤ n) {selected : Finset ℕ}
    (hselected : selected ⊆ Finset.Ioc n (2 * n))
    (hprod : selected.prod id = Nat.choose (2 * n) n) :
    ((Finset.Icc 1 13).biUnion (fun r ↦
        (Finset.range (2 * n + 1)).filter (fun p ↦
          p.Prime ∧ n < p * (r + 1) ∧
            p * (2 * r + 1) ≤ 2 * n))).card ≤
      ∑ ℓ ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
        (Nat.choose (2 * n) n).factorization ℓ := by
  have h := stationaryPrimeUnion13_card_le_centralSmallPrimeValuationSum
    hn (by simpa only [factorInterval] using hselected) hprod
  simpa only [stationaryPrimeUnion13, stationaryPrimeLayer,
    centralSmallPrimeValuationSum, smallPrimes] using h

example :
    ∀ᶠ n : ℕ in atTop,
      ∀ M ≤ 2 * n,
        ¬ ∃ factors : Finset ℕ,
          factors ⊆ Finset.Ioc n M ∧
            factors.prod id = n.factorial := by
  simpa only [IsAdmissibleEndpoint, factorInterval] using
    eventually_no_admissibleEndpoint_le_two_mul

end

end Erdos390.WholePaper
