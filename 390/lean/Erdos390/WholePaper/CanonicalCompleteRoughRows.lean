import Erdos390.WholePaper.CompleteRoughRowPartition
import Erdos390.WholePaper.FloatingRoundingRows

/-!
# Canonical complete rough rows for exactification

A finite candidate set itself supplies the coordinate type used by floating
rounding.  Its attained complete rough labels supply a canonical finite row
type.  The row signature is simply factorization of the label; positivity
of attained labels and uniqueness of factorization make this signature map
injective.

This file also identifies `rowSet` with the literal complete-rough fiber and
provides the value, interval, summation, and row-integrality bridges required
by the exactification interface.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Canonical finite types and maps -/

/-- The canonical candidate type associated with the finite set `A`. -/
abbrev CompleteRoughCandidate (A : Finset ℕ) := ↥A

/-- The canonical finite row type: precisely the complete rough labels
attained on `A`. -/
abbrev CanonicalCompleteRoughRow (y : ℕ) (A : Finset ℕ) :=
  ↥(completeRoughLabelSet y A)

/-- Send a candidate to the row indexed by its complete rough label. -/
def canonicalCompleteRoughRow
    (y : ℕ) (A : Finset ℕ) :
    CompleteRoughCandidate A → CanonicalCompleteRoughRow y A :=
  fun a ↦ ⟨completeRoughLabel y a.1,
    mem_completeRoughLabelSet.mpr ⟨a.1, a.2, rfl⟩⟩

/-- The signature attached to a canonical row is the factorization of its
integer label. -/
def canonicalCompleteRoughRowSignature
    (y : ℕ) (A : Finset ℕ) :
    CanonicalCompleteRoughRow y A → ℕ →₀ ℕ :=
  fun row ↦ row.1.factorization

/-- The candidate value passed to exactification is its underlying natural
number. -/
def canonicalCompleteRoughCandidateValue
    (A : Finset ℕ) : CompleteRoughCandidate A → ℕ :=
  fun a ↦ a.1

@[simp]
theorem canonicalCompleteRoughRow_val
    (y : ℕ) (A : Finset ℕ) (a : CompleteRoughCandidate A) :
    (canonicalCompleteRoughRow y A a).1 =
      completeRoughLabel y a.1 := rfl

@[simp]
theorem canonicalCompleteRoughRowSignature_apply
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    canonicalCompleteRoughRowSignature y A row =
      row.1.factorization := rfl

@[simp]
theorem canonicalCompleteRoughCandidateValue_apply
    (A : Finset ℕ) (a : CompleteRoughCandidate A) :
    canonicalCompleteRoughCandidateValue A a = a.1 := rfl

/-- Every attained row label has a candidate preimage. -/
theorem canonicalCompleteRoughRow_surjective
    (y : ℕ) (A : Finset ℕ) :
    Function.Surjective (canonicalCompleteRoughRow y A) := by
  intro row
  obtain ⟨a, ha, hlabel⟩ :=
    mem_completeRoughLabelSet.mp row.property
  let candidate : CompleteRoughCandidate A := ⟨a, ha⟩
  refine ⟨candidate, ?_⟩
  apply Subtype.ext
  simpa only [candidate, canonicalCompleteRoughRow] using hlabel

/-! ## Signature and value interfaces -/

/-- An attained complete rough label is positive. -/
theorem canonicalCompleteRoughRow_label_pos
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    0 < row.1 := by
  obtain ⟨a, _ha, hlabel⟩ :=
    mem_completeRoughLabelSet.mp row.property
  rw [← hlabel, completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

/-- Uniqueness of positive natural-number factorization makes the canonical
row-signature map injective. -/
theorem canonicalCompleteRoughRowSignature_injective
    (y : ℕ) (A : Finset ℕ) :
    Function.Injective (canonicalCompleteRoughRowSignature y A) := by
  intro row other hsignature
  apply Subtype.ext
  exact Nat.eq_of_factorization_eq'
    (canonicalCompleteRoughRow_label_pos y A row).ne'
    (canonicalCompleteRoughRow_label_pos y A other).ne'
    (by simpa only [canonicalCompleteRoughRowSignature] using hsignature)

/-- The complete signature of every candidate is exactly the signature of
its canonical row. -/
theorem completeRoughSignature_eq_canonicalCompleteRoughRowSignature
    (y : ℕ) (A : Finset ℕ) (a : CompleteRoughCandidate A) :
    completeRoughSignature y
        (canonicalCompleteRoughCandidateValue A a) =
      canonicalCompleteRoughRowSignature y A
        (canonicalCompleteRoughRow y A a) := by
  change completeRoughSignature y a.1 =
    (completeRoughLabel y a.1).factorization
  exact (completeRoughLabel_factorization y a.1).symm

/-- The underlying-value map on the candidate subtype is injective. -/
theorem canonicalCompleteRoughCandidateValue_injective
    (A : Finset ℕ) :
    Function.Injective (canonicalCompleteRoughCandidateValue A) := by
  intro a b hab
  apply Subtype.ext
  exact hab

/-- If all candidates lie in a factor interval, so does every canonical
candidate value. -/
theorem canonicalCompleteRoughCandidateValue_mem_factorInterval
    {n M : ℕ} {A : Finset ℕ}
    (hA : A ⊆ factorInterval n M)
    (a : CompleteRoughCandidate A) :
    canonicalCompleteRoughCandidateValue A a ∈ factorInterval n M :=
  hA a.property

/-! ## Literal subtype fibers and `rowSet` -/

/-- The complete rough row fiber expressed inside the candidate subtype. -/
def completeRoughSubtypeRowFiber
    (y : ℕ) (A : Finset ℕ) (label : ℕ) :
    Finset (CompleteRoughCandidate A) := by
  classical
  exact Finset.univ.filter
    (fun a ↦ completeRoughLabel y a.1 = label)

@[simp]
theorem mem_completeRoughSubtypeRowFiber
    {y label : ℕ} {A : Finset ℕ}
    {a : CompleteRoughCandidate A} :
    a ∈ completeRoughSubtypeRowFiber y A label ↔
      completeRoughLabel y a.1 = label := by
  classical
  simp [completeRoughSubtypeRowFiber]

/-- Membership in the subtype fiber is the same as membership of the
underlying value in the ambient natural-number fiber. -/
theorem mem_completeRoughSubtypeRowFiber_iff_value_mem
    {y label : ℕ} {A : Finset ℕ}
    {a : CompleteRoughCandidate A} :
    a ∈ completeRoughSubtypeRowFiber y A label ↔
      canonicalCompleteRoughCandidateValue A a ∈
        completeRoughRowFiber y A label := by
  rw [mem_completeRoughSubtypeRowFiber, mem_completeRoughRowFiber]
  simp only [canonicalCompleteRoughCandidateValue, a.property, true_and]

/-- Membership in the floating-rounding `rowSet` is exactly ambient row
fiber membership of the candidate value. -/
theorem mem_canonicalCompleteRoughRowSet_iff
    {y : ℕ} {A : Finset ℕ}
    {row : CanonicalCompleteRoughRow y A}
    {a : CompleteRoughCandidate A} :
    a ∈ rowSet (canonicalCompleteRoughRow y A) row ↔
      canonicalCompleteRoughCandidateValue A a ∈
        completeRoughRowFiber y A row.1 := by
  rw [mem_rowSet, mem_completeRoughRowFiber]
  constructor
  · intro hrow
    refine ⟨a.property, ?_⟩
    have hval := congrArg Subtype.val hrow
    simpa only [canonicalCompleteRoughRow,
      canonicalCompleteRoughCandidateValue] using hval
  · rintro ⟨_ha, hlabel⟩
    apply Subtype.ext
    simpa only [canonicalCompleteRoughRow,
      canonicalCompleteRoughCandidateValue] using hlabel

/-- The abstract floating-rounding row set is literally the subtype version
of the corresponding complete rough row fiber. -/
theorem canonicalCompleteRough_rowSet_eq_subtypeRowFiber
    (y : ℕ) (A : Finset ℕ)
    (row : CanonicalCompleteRoughRow y A) :
    rowSet (canonicalCompleteRoughRow y A) row =
      completeRoughSubtypeRowFiber y A row.1 := by
  ext a
  rw [mem_canonicalCompleteRoughRowSet_iff,
    mem_completeRoughSubtypeRowFiber,
    mem_completeRoughRowFiber]
  simp only [canonicalCompleteRoughCandidateValue,
    a.property, true_and]

/-! ## Summation and integrality bridges -/

/-- Reindexing a canonical `rowSet` by underlying candidate values gives
the sum over the literal ambient complete rough fiber. -/
theorem sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber
    {W : Type*} [AddCommMonoid W]
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → W)
    (row : CanonicalCompleteRoughRow y A) :
    ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
        weight (canonicalCompleteRoughCandidateValue A a) =
      ∑ value ∈ completeRoughRowFiber y A row.1,
        weight value := by
  classical
  apply Finset.sum_bij
    (fun a _ha ↦ canonicalCompleteRoughCandidateValue A a)
  · intro a ha
    exact mem_canonicalCompleteRoughRowSet_iff.mp ha
  · intro a₁ _ha₁ a₂ _ha₂ hvalue
    exact canonicalCompleteRoughCandidateValue_injective A hvalue
  · intro value hvalue
    let a : CompleteRoughCandidate A :=
      ⟨value, (mem_completeRoughRowFiber.mp hvalue).1⟩
    refine ⟨a, ?_, ?_⟩
    · apply mem_canonicalCompleteRoughRowSet_iff.mpr
      simpa only [a, canonicalCompleteRoughCandidateValue] using hvalue
    · simp only [a, canonicalCompleteRoughCandidateValue]
  · intro a _ha
    rfl

/-- Row-integrality for an arbitrary function on the candidate subtype is
equivalent to integrality on every attained-label subtype fiber. -/
theorem canonicalCompleteRough_rowSums_integer_iff_subtypeFiberSums_integer
    (y : ℕ) (A : Finset ℕ)
    (x : CompleteRoughCandidate A → ℝ) :
    (∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          x a = (k : ℝ)) ↔
      (∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
        ∑ a ∈ completeRoughSubtypeRowFiber y A label,
            x a = (k : ℝ)) := by
  constructor
  · intro hrow label hlabel
    let row : CanonicalCompleteRoughRow y A := ⟨label, hlabel⟩
    obtain ⟨k, hk⟩ := hrow row
    refine ⟨k, ?_⟩
    rw [canonicalCompleteRough_rowSet_eq_subtypeRowFiber] at hk
    simpa only [row] using hk
  · intro hfiber row
    obtain ⟨k, hk⟩ := hfiber row.1 row.2
    refine ⟨k, ?_⟩
    rw [canonicalCompleteRough_rowSet_eq_subtypeRowFiber]
    exact hk

/-- Direct subtype-fiber-to-row form of the preceding equivalence.  Its
conclusion is the `hrowInt` shape consumed by floating rounding and guarded
exactification. -/
theorem canonicalCompleteRough_rowSums_integer_of_subtypeFiberSums_integer
    (y : ℕ) (A : Finset ℕ)
    (x : CompleteRoughCandidate A → ℝ)
    (hfiber : ∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
      ∑ a ∈ completeRoughSubtypeRowFiber y A label,
          x a = (k : ℝ)) :
    ∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          x a = (k : ℝ) :=
  (canonicalCompleteRough_rowSums_integer_iff_subtypeFiberSums_integer
    y A x).mpr hfiber

/-- Ambient form of the row-integrality bridge.  This is directly shaped
like the `hrowInt` input of the post-tangent exactification theorem. -/
theorem canonicalCompleteRough_rowSums_integer_iff_rowFiberSums_integer
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → ℝ) :
    (∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          weight (canonicalCompleteRoughCandidateValue A a) = (k : ℝ)) ↔
      (∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
        ∑ value ∈ completeRoughRowFiber y A label,
            weight value = (k : ℝ)) := by
  constructor
  · intro hrow label hlabel
    let row : CanonicalCompleteRoughRow y A := ⟨label, hlabel⟩
    obtain ⟨k, hk⟩ := hrow row
    refine ⟨k, ?_⟩
    rw [sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber]
      at hk
    simpa only [row] using hk
  · intro hfiber row
    obtain ⟨k, hk⟩ := hfiber row.1 row.2
    refine ⟨k, ?_⟩
    rw [sum_canonicalCompleteRoughRowSet_eq_sum_completeRoughRowFiber]
    exact hk

/-- Direct ambient-fiber-to-row form.  In particular, with
`x a = weight (canonicalCompleteRoughCandidateValue A a)`, this is a literal
`hrowInt` argument for
`bankPaper_isAdmissibleEndpoint_of_postTangentCertificate`. -/
theorem canonicalCompleteRough_rowSums_integer_of_rowFiberSums_integer
    (y : ℕ) (A : Finset ℕ) (weight : ℕ → ℝ)
    (hfiber : ∀ label ∈ completeRoughLabelSet y A, ∃ k : ℤ,
      ∑ value ∈ completeRoughRowFiber y A label,
          weight value = (k : ℝ)) :
    ∀ row : CanonicalCompleteRoughRow y A, ∃ k : ℤ,
      ∑ a ∈ rowSet (canonicalCompleteRoughRow y A) row,
          weight (canonicalCompleteRoughCandidateValue A a) = (k : ℝ) :=
  (canonicalCompleteRough_rowSums_integer_iff_rowFiberSums_integer
    y A weight).mpr hfiber

end

end Erdos390.WholePaper
