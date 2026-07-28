import Erdos390.WholePaper.CentralAnchorGuardedCertificate
import Erdos390.WholePaper.UpperProductAssembly

/-!
# Final product assembly with lower residual factors

The paper's residual selection is not confined to `(2n,M]`: flexible
coordinates and bank states may lie anywhere in `(n,M]`.  The earlier
`central_union_tail` lemma used interval separation to get disjointness for
free and therefore cannot be the literal final assembly.  Here disjointness
is an explicit proved input, and both sets may occupy the full factor
interval.  The two natural-number product identities then give the exact
complement product without any division.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Division-free product identity when the residual factors may also lie
below `2n`. -/
theorem guardedCentral_union_residual_prod
    {n h D : ℕ} {central residual : Finset ℕ}
    (hdisjoint : Disjoint central residual)
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (hresidualProd : residual.prod id * D = centralTailProduct n h) :
    (central ∪ residual).prod id =
      Nat.choose (2 * n) n * centralTailProduct n h := by
  rw [Finset.prod_union hdisjoint, hcentralProd]
  calc
    (Nat.choose (2 * n) n * D) * residual.prod id =
        Nat.choose (2 * n) n * (residual.prod id * D) := by ac_rfl
    _ = Nat.choose (2 * n) n * centralTailProduct n h := by
      rw [hresidualProd]

/-- Exact complement representation from two disjoint full-interval
families. -/
theorem hasComplementProduct_of_guardedCentral_residual
    {n h D : ℕ} (_hn : 0 < n) {central residual : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n + h))
    (hresidualSubset : residual ⊆ factorInterval n (2 * n + h))
    (hdisjoint : Disjoint central residual)
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (hresidualProd : residual.prod id * D = centralTailProduct n h) :
    HasComplementProduct n (2 * n + h) := by
  refine ⟨central ∪ residual, Finset.union_subset hcentralSubset
    hresidualSubset, ?_⟩
  rw [guardedCentral_union_residual_prod hdisjoint hcentralProd
    hresidualProd]
  exact centralChoose_mul_centralTailProduct_eq_complementQuotient n h

/-- Exact admissible endpoint recovered without requiring the residual set
to be an upper-tail subset. -/
theorem isAdmissibleEndpoint_of_guardedCentral_residual
    {n h D : ℕ} (hn : 0 < n) {central residual : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n + h))
    (hresidualSubset : residual ⊆ factorInterval n (2 * n + h))
    (hdisjoint : Disjoint central residual)
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (hresidualProd : residual.prod id * D = centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) := by
  apply (complement_formulation (by omega)).mpr
  exact hasComplementProduct_of_guardedCentral_residual hn
    hcentralSubset hresidualSubset hdisjoint hcentralProd hresidualProd

/-- Specialization to the literal modified central-anchor certificate. -/
theorem GuardedCentralAnchorCertificate.isAdmissibleEndpoint_of_residual
    {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hn : 0 < n) {residual : Finset ℕ}
    (hresidualSubset : residual ⊆ factorInterval n (2 * n + h))
    (hdisjoint : Disjoint certificate.anchors residual)
    (hresidualProd : residual.prod id *
        centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
      centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) := by
  have hcentralSubset : certificate.anchors ⊆
      factorInterval n (2 * n + h) := by
    intro a ha
    have hcentral := Finset.mem_Ioc.mp (certificate.anchors_subset ha)
    exact Finset.mem_Ioc.mpr ⟨hcentral.1, hcentral.2.trans (by omega)⟩
  exact isAdmissibleEndpoint_of_guardedCentral_residual hn
    hcentralSubset hresidualSubset hdisjoint certificate.anchors_prod
      hresidualProd

end

end Erdos390.WholePaper
