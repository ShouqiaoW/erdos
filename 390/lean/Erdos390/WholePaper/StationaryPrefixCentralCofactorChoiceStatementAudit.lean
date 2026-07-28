import Erdos390.WholePaper.StationaryPrefixCentralCofactorChoice

/-! # Expanded statement audit for the actual fixed-prefix cofactor choice -/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    ∀ p ∈ largeCentralPrimes n (centralAnchorCutoff R n),
      IsRoutedCentralCofactor n p
        (stationaryPrefixCofactorChoice R n parts p) := by
  exact stationaryPrefixCofactorChoice_isLargeCentralCofactorChoice
    hn hparts

example {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    (largeCentralPrimes n (centralAnchorCutoff R n)).prod
        (stationaryPrefixCofactorChoice R n parts) =
      ∏ r : StationaryPrefixRow R,
        ((infiniteAllocationPositiveSupport r.1).sigma
          (parts r)).prod (fun x ↦ x.1) := by
  simpa only [largeCentralCofactorProduct,
    stationaryPrefixCofactorProductUpTo,
    stationaryPrefixCofactorProduct, stationaryPrefixMarkedPairs] using
    largeCentralCofactorProduct_stationaryPrefixCofactorChoice
      hn hparts

example {R n : ℕ}
    (hn : centralAnchorCutoffThreshold R ≤ n)
    {parts : StationaryPrefixRow R → ℕ → Finset ℕ}
    (hparts : IsStationaryPrefixPartFamily R n parts) :
    (fullCentralAnchors n (n / (R + 1))
        (stationaryPrefixCofactorChoice R n parts)).prod id =
      Nat.choose (2 * n) n *
        (2 ^ residualPromotionCost n (n / (R + 1)) *
          stationaryPrefixCofactorProductUpTo R parts) := by
  simpa only [centralAnchorCutoff] using
    fullCentralAnchors_prod_stationaryPrefixCofactorChoice hn hparts

example {n X ell : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    ((largeCentralPrimes n X).prod q).factorization ell =
      ∑ p ∈ largeCentralPrimes n X, (q p).factorization ell := by
  simpa only [largeCentralCofactorProduct] using
    largeCentralCofactorProduct_factorization_eq_sum
      (ell := ell) hq

example (R : ℕ) (distinguished : ℕ → ℕ)
    {slack : ℝ} (hslack : 0 < slack)
    (parts : ℕ → StationaryPrefixRow R → ℕ → Finset ℕ)
    (hactual :
      ∀ᶠ n : ℕ in atTop,
        ∀ r : StationaryPrefixRow R,
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            parts n r q ⊆ stationaryPrimeLayer n r.1) ∧
          (∀ q ∈ infiniteAllocationPositiveSupport r.1,
            (parts n r q).card =
              stationaryPrefixCount n r.1 (distinguished r.1) q) ∧
          (infiniteAllocationPositiveSupport r.1 :
            Set ℕ).PairwiseDisjoint (parts n r) ∧
          (infiniteAllocationPositiveSupport r.1).biUnion
              (parts n r) = stationaryPrimeLayer n r.1)
    (hparts :
      ∀ r : StationaryPrefixRow R,
        ∀ q ∈ infiniteAllocationPositiveSupport r.1,
          Tendsto
            (fun n : ℕ ↦
              ((parts n r q).card : ℝ) / secondOrderScale n)
            atTop (nhds (infiniteAllocation r.1 q : ℝ))) :
    ∀ᶠ n : ℕ in atTop,
      ∀ ell ∈ primesUpTo (2 * R + 1),
        ((((largeCentralCofactorProduct n (n / (R + 1))
          (stationaryPrefixCofactorChoice R n
            (parts n))).factorization ell : ℕ) : ℝ) ≤
            ((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
              secondOrderScale n) ∧
          ((largeCentralCofactorProduct n (n / (R + 1))
            (stationaryPrefixCofactorChoice R n
              (parts n))).factorization ell ≤
                ⌊((C0 + slack) / (((ell - 1 : ℕ) : ℝ))) *
                  secondOrderScale n⌋₊) := by
  simpa only [centralAnchorCutoff] using
    eventually_stationaryPrefixCofactorChoice_factorization_le_on_primesUpTo
      R distinguished hslack parts hactual hparts

end

end Erdos390.WholePaper
