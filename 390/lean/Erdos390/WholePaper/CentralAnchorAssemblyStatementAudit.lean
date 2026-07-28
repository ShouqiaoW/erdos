import Erdos390.WholePaper.CentralAnchorAssembly

/-! # Expanded statement audit for central-anchor endpoint recovery -/

namespace Erdos390.WholePaper

example {n X h : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : ∀ p ∈
      (Nat.choose (2 * n) n).primeFactors.filter (fun P ↦ X < P),
      IsRoutedCentralCofactor n p (q p))
    {tail : Finset ℕ}
    (htailSubset : tail ⊆ Finset.Ioc (2 * n) (2 * n + h))
    (htailProd : tail.prod id *
        (2 ^ residualPromotionCost n X *
          (((Nat.choose (2 * n) n).primeFactors.filter
            (fun P ↦ X < P)).prod q)) =
      (Finset.Ioc (2 * n) (2 * n + h)).prod id) :
    ∃ factors : Finset ℕ,
      factors ⊆ Finset.Ioc n (2 * n + h) ∧
        factors.prod id = n.factorial := by
  simpa only [IsAdmissibleEndpoint, factorInterval, centralTailProduct,
    centralAnchorDivisor, largeCentralCofactorProduct, largeCentralPrimes,
    IsLargeCentralCofactorChoice] using
      isAdmissibleEndpoint_of_fullCentralAnchors hn hXTwo hXsq hq
        htailSubset htailProd

end Erdos390.WholePaper
