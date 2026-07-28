import Erdos390.WholePaper.StationaryPrefixValuationAsymptotic

/-! # Expanded statement audit for the actual prefix-product valuation -/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

example (R ell : ℕ)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    Tendsto
      (fun n : ℕ ↦
        ((((∏ r : {r // r ∈ Finset.Icc 1 R},
            stationaryPrefixCofactorProduct r.1
              (parts n r)).factorization ell : ℕ) : ℝ) /
          secondOrderScale n))
      atTop (nhds (prefixAllocationPrimeLoad R ell : ℝ)) := by
  simpa only [stationaryPrefixCofactorProductUpTo] using
    stationaryPrefixCofactorProductUpTo_factorization_normalized_tendsto
      R ell parts hparts

example (R : ℕ) {ell : ℕ} (hellPrime : ell.Prime)
    {slack : ℝ} (hslack : 0 < slack)
    (parts :
      ℕ → {r // r ∈ Finset.Icc 1 R} → ℕ → Finset ℕ)
    (hparts :
      ∀ r : {r // r ∈ Finset.Icc 1 R},
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ((((∏ r : {r // r ∈ Finset.Icc 1 R},
          stationaryPrefixCofactorProduct r.1
            (parts n r)).factorization ell : ℕ) : ℝ) ≤
        ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
          secondOrderScale n) ∧
      ((∏ r : {r // r ∈ Finset.Icc 1 R},
          stationaryPrefixCofactorProduct r.1
            (parts n r)).factorization ell ≤
        ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
          secondOrderScale n⌋₊) := by
  filter_upwards [
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_real
      R hellPrime hslack parts hparts,
    eventually_stationaryPrefixCofactorProductUpTo_factorization_le_nat
      R hellPrime hslack parts hparts] with n hreal hnat
  simpa only [stationaryPrefixCofactorProductUpTo] using
    And.intro hreal hnat

end

end Erdos390.WholePaper
