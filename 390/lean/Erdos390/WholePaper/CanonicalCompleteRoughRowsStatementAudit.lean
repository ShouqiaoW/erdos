import Erdos390.WholePaper.CanonicalCompleteRoughRows

/-! # Statement audit for canonical complete rough rows -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example (A : Finset ℕ) :
    CompleteRoughCandidate A = ↥A := rfl

example (y : ℕ) (A : Finset ℕ) :
    CanonicalCompleteRoughRow y A =
      ↥(completeRoughLabelSet y A) := rfl

example (y : ℕ) (A : Finset ℕ)
    (a : CompleteRoughCandidate A) :
    (canonicalCompleteRoughRow y A a).1 =
      completeRoughLabel y a.1 := rfl

example (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    canonicalCompleteRoughRowSignature y A row =
      row.1.factorization := rfl

example (A : Finset ℕ) (a : CompleteRoughCandidate A) :
    canonicalCompleteRoughCandidateValue A a = a.1 := rfl

example (y : ℕ) (A : Finset ℕ) :
    Function.Surjective (canonicalCompleteRoughRow y A) :=
  canonicalCompleteRoughRow_surjective y A

example (y : ℕ) (A : Finset ℕ) :
    Function.Injective (canonicalCompleteRoughRowSignature y A) :=
  canonicalCompleteRoughRowSignature_injective y A

example (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    0 < row.1 :=
  canonicalCompleteRoughRow_label_pos y A row

example (y : ℕ) (A : Finset ℕ)
    (a : CompleteRoughCandidate A) :
    completeRoughSignature y
        (canonicalCompleteRoughCandidateValue A a) =
      canonicalCompleteRoughRowSignature y A
        (canonicalCompleteRoughRow y A a) :=
  completeRoughSignature_eq_canonicalCompleteRoughRowSignature y A a

example (A : Finset ℕ) :
    Function.Injective (canonicalCompleteRoughCandidateValue A) :=
  canonicalCompleteRoughCandidateValue_injective A

example {n M : ℕ} {A : Finset ℕ}
    (hA : A ⊆ factorInterval n M)
    (a : CompleteRoughCandidate A) :
    canonicalCompleteRoughCandidateValue A a ∈ factorInterval n M :=
  canonicalCompleteRoughCandidateValue_mem_factorInterval hA a

example {y : ℕ} {A : Finset ℕ}
    {row : CanonicalCompleteRoughRow y A}
    {a : CompleteRoughCandidate A} :
    a ∈ rowSet (canonicalCompleteRoughRow y A) row ↔
      canonicalCompleteRoughCandidateValue A a ∈
        completeRoughRowFiber y A row.1 :=
  mem_canonicalCompleteRoughRowSet_iff

example {y label : ℕ} {A : Finset ℕ}
    {a : CompleteRoughCandidate A} :
    a ∈ completeRoughSubtypeRowFiber y A label ↔
      canonicalCompleteRoughCandidateValue A a ∈
        completeRoughRowFiber y A label :=
  mem_completeRoughSubtypeRowFiber_iff_value_mem

example (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    rowSet (canonicalCompleteRoughRow y A) row =
      completeRoughSubtypeRowFiber y A row.1 :=
  canonicalCompleteRough_rowSet_eq_subtypeRowFiber y A row

example {W : Type*} [AddCommMonoid W]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → W)
    (row : CanonicalCompleteRoughRow y A) :
    ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
        weight (canonicalCompleteRoughCandidateValue A a) =
      ∑ value ∈ completeRoughRowFiber y A row.1,
        weight value :=
  sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
    y A weight row

example (y : ℕ) (A : Finset ℕ)
    (x : CompleteRoughCandidate A → ℝ) :
    (∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          x a = (k : ℝ)) ↔
      (∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
        ∑ a ∈ completeRoughSubtypeRowFiber y A label,
            x a = (k : ℝ)) :=
  canonicalCompleteRough_rowSums_integer_iff_subtypeFiberSums_integer y A x

example (y : ℕ) (A : Finset ℕ)
    (x : CompleteRoughCandidate A → ℝ)
    (hfiber : ∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
      ∑ a ∈ completeRoughSubtypeRowFiber y A label,
          x a = (k : ℝ)) :
    ∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          x a = (k : ℝ) :=
  canonicalCompleteRough_rowSums_integer_of_subtypeFiberSums_integer
    y A x hfiber

example (y : ℕ) (A : Finset ℕ) (weight : ℕ → ℝ) :
    (∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          weight (canonicalCompleteRoughCandidateValue A a) = (k : ℝ)) ↔
      (∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
        ∑ value ∈ completeRoughRowFiber y A label,
            weight value = (k : ℝ)) :=
  canonicalCompleteRough_rowSums_integer_iff_rowFiberSums_integer y A weight

example (y : ℕ) (A : Finset ℕ) (weight : ℕ → ℝ)
    (hfiber : ∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
      ∑ value ∈ completeRoughRowFiber y A label,
          weight value = (k : ℝ)) :
    ∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          weight (canonicalCompleteRoughCandidateValue A a) = (k : ℝ) :=
  canonicalCompleteRough_rowSums_integer_of_rowFiberSums_integer
    y A weight hfiber

end

end Erdos390.WholePaper
