import Erdos390.WholePaper.BankRoughSignatures

/-!
# The finite partition into complete rough rows

For a finite set `A`, its complete rough labels are precisely the labels
actually attained on `A`.  Filtering `A` at one such label gives the
corresponding row.  These rows form a literal finite partition of `A`:
they are nonempty, lie in `A`, have constant complete signature, are
pairwise disjoint, and have union exactly `A`.

The final results transport arbitrary additive weights across this
partition, including the factorization-coordinate weights used later in
the paper.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Labels and row fibers -/

/-- The finite set of complete rough labels attained by elements of `A`. -/
def completeRoughLabelSet (y : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (completeRoughLabel y)

/-- The fiber in `A` carrying one specified complete rough label. -/
def completeRoughRowFiber
    (y : ℕ) (A : Finset ℕ) (label : ℕ) : Finset ℕ :=
  A.filter (fun a ↦ completeRoughLabel y a = label)

@[simp]
theorem mem_completeRoughLabelSet
    {y label : ℕ} {A : Finset ℕ} :
    label ∈ completeRoughLabelSet y A ↔
      ∃ a ∈ A, completeRoughLabel y a = label := by
  simp [completeRoughLabelSet]

@[simp]
theorem mem_completeRoughRowFiber
    {y label a : ℕ} {A : Finset ℕ} :
    a ∈ completeRoughRowFiber y A label ↔
      a ∈ A ∧ completeRoughLabel y a = label := by
  simp [completeRoughRowFiber]

/-- A label is attained on `A` exactly when its row fiber is nonempty. -/
theorem mem_completeRoughLabelSet_iff_rowFiber_nonempty
    {y label : ℕ} {A : Finset ℕ} :
    label ∈ completeRoughLabelSet y A ↔
      (completeRoughRowFiber y A label).Nonempty := by
  constructor
  · rw [mem_completeRoughLabelSet]
    rintro ⟨a, ha, hlabel⟩
    exact ⟨a, mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩⟩
  · rintro ⟨a, ha⟩
    have haData := mem_completeRoughRowFiber.mp ha
    exact mem_completeRoughLabelSet.mpr
      ⟨a, haData.1, haData.2⟩

/-! ## Row support and constancy -/

/-- Every complete rough row is a subset of the original finite set. -/
theorem completeRoughRowFiber_subset
    (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    completeRoughRowFiber y A label ⊆ A := by
  intro a ha
  exact (mem_completeRoughRowFiber.mp ha).1

/-- The integer rough label is constant throughout its row fiber. -/
theorem completeRoughLabel_eq_of_mem_rowFiber
    {y label a : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label) :
    completeRoughLabel y a = label :=
  (mem_completeRoughRowFiber.mp ha).2

/-- The full vector signature throughout a row is the factorization of
that row's integer label. -/
theorem completeRoughSignature_eq_label_factorization_of_mem_rowFiber
    {y label a : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label) :
    completeRoughSignature y a = label.factorization := by
  calc
    completeRoughSignature y a =
        (completeRoughLabel y a).factorization :=
      (completeRoughLabel_factorization y a).symm
    _ = label.factorization :=
      congrArg Nat.factorization
        (completeRoughLabel_eq_of_mem_rowFiber ha)

/-- Any two elements of the same row have identical complete signatures. -/
theorem completeRoughSignature_eq_of_mem_same_rowFiber
    {y label a b : ℕ} {A : Finset ℕ}
    (ha : a ∈ completeRoughRowFiber y A label)
    (hb : b ∈ completeRoughRowFiber y A label) :
    completeRoughSignature y a = completeRoughSignature y b := by
  calc
    completeRoughSignature y a = label.factorization :=
      completeRoughSignature_eq_label_factorization_of_mem_rowFiber ha
    _ = completeRoughSignature y b :=
      (completeRoughSignature_eq_label_factorization_of_mem_rowFiber hb).symm

/-! ## Exact finite partition -/

/-- Distinct attained labels have disjoint row fibers. -/
theorem completeRoughRowFibers_pairwiseDisjoint
    (y : ℕ) (A : Finset ℕ) :
    ((completeRoughLabelSet y A : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (completeRoughRowFiber y A) := by
  intro label _hlabel other _hother hne
  change Disjoint (completeRoughRowFiber y A label)
    (completeRoughRowFiber y A other)
  rw [Finset.disjoint_left]
  intro a haLabel haOther
  have hlabelEq : completeRoughLabel y a = label :=
    completeRoughLabel_eq_of_mem_rowFiber haLabel
  have hotherEq : completeRoughLabel y a = other :=
    completeRoughLabel_eq_of_mem_rowFiber haOther
  exact hne (hlabelEq.symm.trans hotherEq)

/-- The union of all attained-label row fibers is exactly `A`. -/
theorem completeRoughLabelSet_biUnion_rowFibers
    (y : ℕ) (A : Finset ℕ) :
    (completeRoughLabelSet y A).biUnion
        (completeRoughRowFiber y A) = A := by
  ext a
  constructor
  · intro ha
    rw [Finset.mem_biUnion] at ha
    obtain ⟨label, _hlabel, haRow⟩ := ha
    exact (completeRoughRowFiber_subset y A label) haRow
  · intro ha
    rw [Finset.mem_biUnion]
    refine ⟨completeRoughLabel y a, ?_, ?_⟩
    · exact mem_completeRoughLabelSet.mpr ⟨a, ha, rfl⟩
    · exact mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩

/-! ## Additive partition identities -/

/-- Every additive weight on `A` is the sum of its weights row by row. -/
theorem sum_eq_sum_completeRoughRowFibers
    {M : Type*} [AddCommMonoid M]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → M) :
    ∑ a ∈ A, weight a =
      ∑ label ∈ completeRoughLabelSet y A,
        ∑ a ∈ completeRoughRowFiber y A label, weight a := by
  classical
  calc
    ∑ a ∈ A, weight a =
        ∑ a ∈ (completeRoughLabelSet y A).biUnion
          (completeRoughRowFiber y A), weight a := by
      rw [completeRoughLabelSet_biUnion_rowFibers]
    _ = ∑ label ∈ completeRoughLabelSet y A,
          ∑ a ∈ completeRoughRowFiber y A label, weight a := by
      exact Finset.sum_biUnion
        (completeRoughRowFibers_pairwiseDisjoint y A)

/-- The generic partition identity specialized to one natural
factorization coordinate. -/
theorem sum_factorization_eq_sum_completeRoughRowFibers
    (y p : ℕ) (A : Finset ℕ) :
    ∑ a ∈ A, a.factorization p =
      ∑ label ∈ completeRoughLabelSet y A,
        ∑ a ∈ completeRoughRowFiber y A label,
          a.factorization p :=
  sum_eq_sum_completeRoughRowFibers y A
    (fun a ↦ a.factorization p)

/-- Above the cutoff, a factorization coordinate is visibly constant on
each complete rough row. -/
theorem factorization_eq_label_factorization_of_mem_rowFiber
    {y p label a : ℕ} {A : Finset ℕ}
    (hp : y < p)
    (ha : a ∈ completeRoughRowFiber y A label) :
    a.factorization p = label.factorization p := by
  simpa only [completeRoughSignature_apply, if_pos hp] using
    congrArg (fun signature : ℕ →₀ ℕ ↦ signature p)
      (completeRoughSignature_eq_label_factorization_of_mem_rowFiber ha)

/-- Hence a high-prime factorization sum is the row cardinality times the
coordinate of the row label, summed over all attained labels. -/
theorem sum_factorization_eq_sum_rowCard_mul_labelFactorization
    (y p : ℕ) (A : Finset ℕ) (hp : y < p) :
    ∑ a ∈ A, a.factorization p =
      ∑ label ∈ completeRoughLabelSet y A,
        (completeRoughRowFiber y A label).card *
          label.factorization p := by
  calc
    ∑ a ∈ A, a.factorization p =
        ∑ label ∈ completeRoughLabelSet y A,
          ∑ a ∈ completeRoughRowFiber y A label,
            a.factorization p :=
      sum_factorization_eq_sum_completeRoughRowFibers y p A
    _ = ∑ label ∈ completeRoughLabelSet y A,
          (completeRoughRowFiber y A label).card *
            label.factorization p := by
      apply Finset.sum_congr rfl
      intro label _hlabel
      calc
        ∑ a ∈ completeRoughRowFiber y A label,
            a.factorization p =
            ∑ _a ∈ completeRoughRowFiber y A label,
              label.factorization p := by
          apply Finset.sum_congr rfl
          intro a ha
          exact factorization_eq_label_factorization_of_mem_rowFiber hp ha
        _ = (completeRoughRowFiber y A label).card *
              label.factorization p := by simp

end

end Erdos390.WholePaper
