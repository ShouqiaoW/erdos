import Erdos390.WholePaper.BankPaperFixedExceptionalBacking

/-!
# Expanded statement audit for the literal fixed exceptional backing

The first two examples keep the paper's real cutoff and the exhaustive set
difference visible.  The remaining examples expand the high-prime backing
into the concrete precharge product used by the selector.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example (n h : ℕ) (deltaStar : ℝ) :
    paperExceptionalUpperFactors n h deltaStar =
      (roughUpperBlock n h).filter (fun a ↦
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar) :=
  rfl

example {n h a : ℕ} {deltaStar : ℝ} :
    a ∈ paperExceptionalUpperFactors n h deltaStar ↔
      a ∈ roughUpperBlock n h ∧
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar :=
  mem_paperExceptionalUpperFactors

example (n h : ℕ) (deltaStar : ℝ) :
    paperExceptionalUpperFactors n h deltaStar ⊆
      roughUpperBlock n h :=
  paperExceptionalUpperFactors_subset_upperBlock n h deltaStar

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar =
      ((roughUpperBlock n h).filter (fun a ↦
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar)) \ R.prechargeDonorSet :=
  rfl

example {n h a : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : ℝ} :
    a ∈ R.paperFixedExceptionalFactors deltaStar ↔
      a ∈ Finset.Ioc (2 * n) (2 * n + h) ∧
        2 * (n : ℝ) / (completeRoughLabel (yNat n) a : ℝ) <
          (n : ℝ) ^ deltaStar ∧
        a ∉ R.prechargeDonorSet := by
  simpa only [roughUpperBlock] using
    R.mem_paperFixedExceptionalFactors (a := a)

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
      roughUpperBlock n h :=
  R.paperFixedExceptionalFactors_subset_upperBlock deltaStar

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ⊆
        Finset.Ioc (2 * n) (upperEndpoint n h) ∧
      Disjoint (R.paperFixedExceptionalFactors deltaStar)
        R.prechargeDonorSet ∧
      (R.paperFixedExceptionalFactors deltaStar ∪
          R.prechargeDonorSet).prod id ∣ centralTailProduct n h :=
  ⟨R.paperFixedExceptionalFactors_subset_tail deltaStar,
    R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet deltaStar,
    R.paperFixedExceptionalBacking_prod_dvd_centralTailProduct deltaStar⟩

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet ⊆
      Finset.Ioc (2 * n) (upperEndpoint n h) :=
  R.paperFixedExceptionalBacking_subset_tail deltaStar

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) :
    (R.paperFixedExceptionalFactors deltaStar).prod id *
        R.prechargeDonorSet.prod id =
      (R.paperFixedExceptionalFactors deltaStar ∪
        R.prechargeDonorSet).prod id :=
  R.paperFixedExceptionalFactors_prod_mul_prechargeDonorSet_prod deltaStar

example {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : ℝ) (hp : yNat n < p) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id *
          R.prechargeBaseStateProduct).factorization p =
        ((R.paperFixedExceptionalFactors deltaStar ∪
          R.prechargeDonorSet).prod id).factorization p ∧
      ((R.paperFixedExceptionalFactors deltaStar).prod id *
          R.prechargeBaseStateProduct).factorization p ≤
        (centralTailProduct n h).factorization p := by
  have heq :=
    R.paperFixedExceptional_selectorTailCharge_factorization_eq_backing
      deltaStar hp
  have hle :=
    R.paperFixedExceptional_selectorTailCharge_factorization_le
      deltaStar hp
  rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct] at heq hle
  exact ⟨heq, hle⟩

end

end Erdos390.WholePaper
