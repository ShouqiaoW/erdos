import Erdos390.WholePaper.CompleteRoughRowPartition

/-! # Statement audit for the complete rough-row partition -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (y : ℕ) (A : Finset ℕ) :
    completeRoughLabelSet y A = A.image (completeRoughLabel y) := rfl

example (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    completeRoughRowFiber y A label =
      A.filter (fun a ↦ completeRoughLabel y a = label) := rfl

example {y label : ℕ} {A : Finset ℕ} :
    label ∈ completeRoughLabelSet y A ↔
      (completeRoughRowFiber y A label).Nonempty :=
  mem_completeRoughLabelSet_iff_rowFiber_nonempty

example (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    completeRoughRowFiber y A label ⊆ A :=
  completeRoughRowFiber_subset y A label

example {y label a : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label) :
    completeRoughLabel y a = label ∧
      completeRoughSignature y a = label.factorization :=
  ⟨completeRoughLabel_eq_of_mem_rowFiber ha,
    completeRoughSignature_eq_label_factorization_of_mem_rowFiber ha⟩

example (y : ℕ) (A : Finset ℕ) :
    ((completeRoughLabelSet y A : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (completeRoughRowFiber y A) :=
  completeRoughRowFibers_pairwiseDisjoint y A

example (y : ℕ) (A : Finset ℕ) :
    (completeRoughLabelSet y A).biUnion
        (completeRoughRowFiber y A) = A :=
  completeRoughLabelSet_biUnion_rowFibers y A

example {M : Type*} [AddCommMonoid M]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → M) :
    ∑ a ∈ A, weight a =
      ∑ label ∈ completeRoughLabelSet y A,
        ∑ a ∈ completeRoughRowFiber y A label, weight a :=
  sum_eq_sum_completeRoughRowFibers y A weight

example (y p : ℕ) (A : Finset ℕ) :
    ∑ a ∈ A, a.factorization p =
      ∑ label ∈ completeRoughLabelSet y A,
        ∑ a ∈ completeRoughRowFiber y A label,
          a.factorization p :=
  sum_factorization_eq_sum_completeRoughRowFibers y p A

example (y p : ℕ) (A : Finset ℕ) (hp : y < p) :
    ∑ a ∈ A, a.factorization p =
      ∑ label ∈ completeRoughLabelSet y A,
        (completeRoughRowFiber y A label).card *
          label.factorization p :=
  sum_factorization_eq_sum_rowCard_mul_labelFactorization y p A hp

end

end Erdos390.WholePaper
