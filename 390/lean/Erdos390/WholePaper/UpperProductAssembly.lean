import Erdos390.WholePaper.Complement
import Erdos390.WholePaper.CentralExtension

/-!
# Exact upper-bound product assembly

This is the division-free algebra at the end of the paper.  A central anchor
set removes the central binomial coefficient together with a divisor `D` of
the tail.  A disjoint residual tail set removes the complementary tail
product.  Their union is therefore an exact complement representation, and
the complement lemma recovers a factorization of `n!`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The literal product of all integers in `(2n,2n+h]`. -/
def centralTailProduct (n h : ℕ) : ℕ :=
  (factorInterval (2 * n) (2 * n + h)).prod id

theorem centralTailProduct_mul_centralFactorial (n h : ℕ) :
    centralTailProduct n h * (2 * n).factorial =
      (2 * n + h).factorial := by
  exact factorInterval_prod_mul_factorial (by omega)

/-- The exact central/tail split of the complement quotient. -/
theorem centralChoose_mul_centralTailProduct_eq_complementQuotient
    (n h : ℕ) :
    ((Nat.choose (2 * n) n * centralTailProduct n h : ℕ) : ℚ) =
      complementQuotient n (2 * n + h) := by
  apply prod_eq_complementQuotient_iff.mpr
  calc
    (Nat.choose (2 * n) n * centralTailProduct n h) *
        n.factorial ^ 2 =
      centralTailProduct n h *
        (Nat.choose (2 * n) n * n.factorial ^ 2) := by ac_rfl
    _ = centralTailProduct n h * (2 * n).factorial := by
      rw [centralChoose_mul_factorial_sq]
    _ = (2 * n + h).factorial :=
      centralTailProduct_mul_centralFactorial n h

theorem centralFactors_disjoint_tailFactors
    {n h : ℕ} {central tail : Finset ℕ}
    (hcentral : central ⊆ factorInterval n (2 * n))
    (htail : tail ⊆ factorInterval (2 * n) (2 * n + h)) :
    Disjoint central tail := by
  rw [Finset.disjoint_left]
  intro a haCentral haTail
  have hc := Finset.mem_Ioc.mp (hcentral haCentral)
  have ht := Finset.mem_Ioc.mp (htail haTail)
  omega

theorem central_union_tail_subset_factorInterval
    {n h : ℕ} (hn : 0 < n) {central tail : Finset ℕ}
    (hcentral : central ⊆ factorInterval n (2 * n))
    (htail : tail ⊆ factorInterval (2 * n) (2 * n + h)) :
    central ∪ tail ⊆ factorInterval n (2 * n + h) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haCentral | haTail
  · have hc := Finset.mem_Ioc.mp (hcentral haCentral)
    exact Finset.mem_Ioc.mpr ⟨hc.1, by omega⟩
  · have ht := Finset.mem_Ioc.mp (htail haTail)
    exact Finset.mem_Ioc.mpr ⟨by omega, ht.2⟩

/-- Division-free product assembly.  The two identities contain every
valuation assertion needed by this final algebraic step. -/
theorem central_union_tail_prod
    {n h D : ℕ} {central tail : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n))
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (htailProd : tail.prod id * D = centralTailProduct n h) :
    (central ∪ tail).prod id =
      Nat.choose (2 * n) n * centralTailProduct n h := by
  rw [Finset.prod_union
    (centralFactors_disjoint_tailFactors hcentralSubset htailSubset),
    hcentralProd]
  calc
    (Nat.choose (2 * n) n * D) * tail.prod id =
      Nat.choose (2 * n) n * (tail.prod id * D) := by ac_rfl
    _ = Nat.choose (2 * n) n * centralTailProduct n h := by
      rw [htailProd]

theorem hasComplementProduct_of_central_tail_assembly
    {n h D : ℕ} (hn : 0 < n) {central tail : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n))
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (htailProd : tail.prod id * D = centralTailProduct n h) :
    HasComplementProduct n (2 * n + h) := by
  refine ⟨central ∪ tail,
    central_union_tail_subset_factorInterval hn hcentralSubset htailSubset,
    ?_⟩
  rw [central_union_tail_prod hcentralSubset htailSubset
    hcentralProd htailProd]
  exact centralChoose_mul_centralTailProduct_eq_complementQuotient n h

/-- Exact recovery of an admissible endpoint from the central anchors and
the residual tail set. -/
theorem isAdmissibleEndpoint_of_central_tail_assembly
    {n h D : ℕ} (hn : 0 < n) {central tail : Finset ℕ}
    (hcentralSubset : central ⊆ factorInterval n (2 * n))
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (hcentralProd : central.prod id = Nat.choose (2 * n) n * D)
    (htailProd : tail.prod id * D = centralTailProduct n h) :
    IsAdmissibleEndpoint n (2 * n + h) := by
  apply (complement_formulation (by omega)).mpr
  exact hasComplementProduct_of_central_tail_assembly hn
    hcentralSubset htailSubset hcentralProd htailProd

end

end Erdos390.WholePaper
