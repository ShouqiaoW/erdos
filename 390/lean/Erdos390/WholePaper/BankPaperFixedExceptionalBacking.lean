import Erdos390.WholePaper.BankPaperSelectorTailTarget
import Erdos390.WholePaper.RoughHeadCompatibleFinitePoint

/-!
# The literal fixed exceptional factors and their high-prime backing

The paper fixes every upper-tail factor whose complete rough row has real
scale `2n / R_y(a) < n ^ deltaStar`, except for the actual donor occurrences
already withheld for the precharged bank.  This file makes that set literal.

The definition deliberately uses the displayed real quotient and real power.
It is not the larger integral test obtained by flooring the rough scale and
ceiling the exceptional cutoff.

At every prime above the rough cutoff, replacing the donor set by the bank's
base state preserves factorization coordinatewise.  The fixed exceptional
factors and donors are disjoint subsets of the literal tail, so their union
is an unconditional backing product for the complete selector charge in
all such coordinates.  No small-prime charge estimate is asserted here.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- The paper's literal exceptional part of `E = (2n,2n+h]`:
`X_{R_y(a)} = 2n / R_y(a) < n ^ deltaStar`, with the comparison made in
the reals exactly as displayed in the paper. -/
def paperExceptionalUpperFactors
    (n h : ℕ) (deltaStar : ℝ) : Finset ℕ :=
  (roughUpperBlock n h).filter fun a ↦
    2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
      (n : ℝ) ^ deltaStar

@[simp]
theorem mem_paperExceptionalUpperFactors
    {n h a : ℕ} {deltaStar : ℝ} :
    a ∈ paperExceptionalUpperFactors n h deltaStar ↔
      a ∈ roughUpperBlock n h ∧
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar := by
  simp only [paperExceptionalUpperFactors, Finset.mem_filter]

theorem paperExceptionalUpperFactors_subset_upperBlock
    (n h : ℕ) (deltaStar : ℝ) :
    paperExceptionalUpperFactors n h deltaStar ⊆
      roughUpperBlock n h :=
  Finset.filter_subset _ _

namespace BankPaperRealization

/-- The paper's exhaustive fixed residual class
`G_fix = E_exc \ E_donor`, using the actual globally injective donor set of
the realized bank. -/
def paperFixedExceptionalFactors
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) : Finset ℕ :=
  paperExceptionalUpperFactors n h deltaStar \ R.prechargeDonorSet

@[simp]
theorem mem_paperFixedExceptionalFactors
    {n h a : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} :
    a ∈ R.paperFixedExceptionalFactors deltaStar ↔
      a ∈ roughUpperBlock n h ∧
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar ∧
        a ∉ R.prechargeDonorSet := by
  simp only [paperFixedExceptionalFactors, Finset.mem_sdiff,
    mem_paperExceptionalUpperFactors, and_assoc]

theorem paperFixedExceptionalFactors_subset_upperBlock
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆ roughUpperBlock n h := by
  intro a ha
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at ha
  exact (mem_paperExceptionalUpperFactors.mp ha.1).1

/-- Every fixed exceptional factor is a literal upper-tail occurrence. -/
theorem paperFixedExceptionalFactors_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  simpa only [roughUpperBlock, upperEndpoint] using
    R.paperFixedExceptionalFactors_subset_upperBlock deltaStar

/-- The set difference in the definition makes the fixed factors and all
designated donors literally disjoint. -/
theorem paperFixedExceptionalFactors_disjoint_prechargeDonorSet
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      R.prechargeDonorSet := by
  rw [Finset.disjoint_left]
  intro a haFixed haDonor
  rw [paperFixedExceptionalFactors, Finset.mem_sdiff] at haFixed
  exact haFixed.2 haDonor

/-- Fixed exceptional factors together with their complementary donor
occurrences remain a subset of the literal upper tail. -/
theorem paperFixedExceptionalBacking_subset_tail
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) := by
  intro a ha
  rcases Finset.mem_union.mp ha with haFixed | haDonor
  · exact R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
  · exact R.prechargeDonorSet_subset_tail haDonor

/-- The backing union is an actual subset-product of the factorial tail. -/
theorem paperFixedExceptionalBacking_prod_dvd_centralTailProduct
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id ∣
      centralTailProduct n h := by
  change (R.paperFixedExceptionalFactors deltaStar ∪
      R.prechargeDonorSet).prod id ∣
    (Finset.Ioc (2 * n) (2 * n + h)).prod id
  exact Finset.prod_dvd_prod_of_subset
    (R.paperFixedExceptionalFactors deltaStar ∪ R.prechargeDonorSet)
    (Finset.Ioc (2 * n) (2 * n + h)) id
    (by
      simpa only [upperEndpoint] using
        R.paperFixedExceptionalBacking_subset_tail deltaStar)

/-- Product form of the disjoint fixed-factor/donor ownership ledger. -/
theorem paperFixedExceptionalFactors_prod_mul_prechargeDonorSet_prod
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    (R.paperFixedExceptionalFactors deltaStar).prod id *
        R.prechargeDonorSet.prod id =
      (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id := by
  rw [Finset.prod_union
    (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet deltaStar)]

private theorem paperFixedExceptionalFactors_prod_pos
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    0 < (R.paperFixedExceptionalFactors deltaStar).prod id := by
  apply Finset.prod_pos
  intro factor hfactor
  have htail := R.paperFixedExceptionalFactors_subset_tail deltaStar hfactor
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1

private theorem prechargeBaseStateProduct_pos
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    0 < R.prechargeBaseStateProduct := by
  rw [prechargeBaseStateProduct]
  apply Finset.prod_pos
  intro factor hfactor
  have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1

private theorem prechargeDonorSet_prod_pos
    {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    0 < R.prechargeDonorSet.prod id := by
  apply Finset.prod_pos
  intro factor hfactor
  have htail := R.prechargeDonorSet_subset_tail hfactor
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1

/-- Strong high-prime backing identity.  In every coordinate above `y`, the
complete selector charge has exactly the valuation of the disjoint union of
the retained exceptional tail factors and the actual donors they complement.
-/
theorem paperFixedExceptional_selectorTailCharge_factorization_eq_backing
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (hp : yNat n < p) :
    (R.selectorTailCharge
        (R.paperFixedExceptionalFactors deltaStar)).factorization p =
      ((R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id).factorization p := by
  have hfixedNe :
      (R.paperFixedExceptionalFactors deltaStar).prod id ≠ 0 :=
    (paperFixedExceptionalFactors_prod_pos R deltaStar).ne'
  have hbaseNe : R.prechargeBaseStateProduct ≠ 0 :=
    (prechargeBaseStateProduct_pos R).ne'
  have hdonorNe : R.prechargeDonorSet.prod id ≠ 0 :=
    (prechargeDonorSet_prod_pos R).ne'
  rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
    ← R.paperFixedExceptionalFactors_prod_mul_prechargeDonorSet_prod
      deltaStar,
    Nat.factorization_mul hfixedNe hbaseNe,
    Nat.factorization_mul hfixedNe hdonorNe,
    Finsupp.add_apply, Finsupp.add_apply,
    R.prechargeBaseStateProduct_factorization_eq_donorSet_prod hp]

/-- Unconditional high-prime half of the paper's combined-charge argument.
The missing low-prime exceptional-charge estimate is neither assumed nor
hidden in this statement. -/
theorem paperFixedExceptional_selectorTailCharge_factorization_le
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (hp : yNat n < p) :
    (R.selectorTailCharge
        (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
      (centralTailProduct n h).factorization p := by
  rw [R.paperFixedExceptional_selectorTailCharge_factorization_eq_backing
    deltaStar hp]
  have hbackingPos :
      0 < (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id := by
    apply Finset.prod_pos
    intro factor hfactor
    have htail := R.paperFixedExceptionalBacking_subset_tail deltaStar hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  exact (Nat.factorization_le_iff_dvd hbackingPos.ne'
    (centralTailProduct_pos n h).ne').mpr
      (R.paperFixedExceptionalBacking_prod_dvd_centralTailProduct
        deltaStar) p

end BankPaperRealization

end

end Erdos390.WholePaper
