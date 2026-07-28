import Erdos390.WholePaper.GuardedUpperProductAssembly

/-! # Expanded statement audit for the final guarded product assembly -/

namespace Erdos390.WholePaper

noncomputable section

example {n h D : ℕ} {central residual : Finset ℕ}
    (hdisjoint : Disjoint central residual)
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (hresidualProd : residual.prod id * D = centralTailProduct n h) :
    (central ∪ residual).prod id =
      Nat.choose (2 * n) n * centralTailProduct n h :=
  guardedCentral_union_residual_prod hdisjoint hcentralProd hresidualProd

example {n h D : ℕ} (hn : 0 < n) {central residual : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n + h))
    (hresidualSubset : residual ⊆ factorInterval n (2 * n + h))
    (hdisjoint : Disjoint central residual)
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (hresidualProd : residual.prod id * D = centralTailProduct n h) :
    HasComplementProduct n (2 * n + h) :=
  hasComplementProduct_of_guardedCentral_residual hn hcentralSubset
    hresidualSubset hdisjoint hcentralProd hresidualProd

example {n h D : ℕ} (hn : 0 < n) {central residual : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n + h))
    (hresidualSubset : residual ⊆ factorInterval n (2 * n + h))
    (hdisjoint : Disjoint central residual)
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (hresidualProd : residual.prod id * D = centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) :=
  isAdmissibleEndpoint_of_guardedCentral_residual hn hcentralSubset
    hresidualSubset hdisjoint hcentralProd hresidualProd

example {c : ℝ} {depth n h : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hn : 0 < n) {residual : Finset ℕ}
    (hresidualSubset : residual ⊆ factorInterval n (2 * n + h))
    (hdisjoint : Disjoint certificate.anchors residual)
    (hresidualProd : residual.prod id *
        centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q =
      centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) :=
  certificate.isAdmissibleEndpoint_of_residual hn hresidualSubset
    hdisjoint hresidualProd

end

end Erdos390.WholePaper
