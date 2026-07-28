import Erdos390.WholePaper.CentralAnchorProduct
import Erdos390.WholePaper.UpperProductAssembly

/-!
# Specializing final assembly to the actual central-anchor set

This module connects the exact three-family central-anchor construction to
the division-free final product assembly.  Once a residual tail set realizes
the literal remaining tail product, no further valuation or divisibility
argument is needed to recover an admissible endpoint.
-/

namespace Erdos390.WholePaper

noncomputable section

theorem hasComplementProduct_of_fullCentralAnchors
    {n X h : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q)
    {tail : Finset ℕ}
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (htailProd : tail.prod id * centralAnchorDivisor n X q =
      centralTailProduct n h) :
    HasComplementProduct n (2 * n + h) := by
  exact hasComplementProduct_of_central_tail_assembly hn
    (fullCentralAnchors_subset_centralInterval hn hq)
    htailSubset
    (fullCentralAnchors_prod hn hXTwo hXsq hq)
    htailProd

/-- Exact endpoint recovery using the actual promoted and routed central
anchors. -/
theorem isAdmissibleEndpoint_of_fullCentralAnchors
    {n X h : ℕ} {q : ℕ → ℕ} (hn : 0 < n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q)
    {tail : Finset ℕ}
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (htailProd : tail.prod id * centralAnchorDivisor n X q =
      centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) := by
  exact isAdmissibleEndpoint_of_central_tail_assembly hn
    (fullCentralAnchors_subset_centralInterval hn hq)
    htailSubset
    (fullCentralAnchors_prod hn hXTwo hXsq hq)
    htailProd

end

end Erdos390.WholePaper
