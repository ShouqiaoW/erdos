import Erdos390.WholePaper.UpperProductAssembly

/-! # Expanded statement audit for exact upper product assembly -/

open scoped BigOperators

namespace Erdos390.WholePaper

example {n h D : ℕ} (hn : 0 < n) {central tail : Finset ℕ}
    (hcentralSubset : central ⊆ Finset.Ioc n (2 * n))
    (htailSubset : tail ⊆ Finset.Ioc (2 * n) (2 * n + h))
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (htailProd : tail.prod id * D =
      (Finset.Ioc (2 * n) (2 * n + h)).prod id) :
    ∃ factors : Finset ℕ,
      factors ⊆ Finset.Ioc n (2 * n + h) ∧
        factors.prod id = n.factorial := by
  simpa only [IsAdmissibleEndpoint, factorInterval, centralTailProduct] using
    isAdmissibleEndpoint_of_central_tail_assembly hn
      hcentralSubset htailSubset hcentralProd htailProd

end Erdos390.WholePaper
