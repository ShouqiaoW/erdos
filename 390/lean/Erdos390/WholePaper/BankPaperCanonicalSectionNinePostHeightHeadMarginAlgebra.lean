import Erdos390.Full.PaperCanonicalHeadPhysicalTarget

/-!
# Finite head-margin algebra for the post-height target

This file isolates the elementary finite-dimensional argument behind the
head-simplex margins.  It contains no realization, certificate, source-state,
or placement hypothesis.

For fixed positive coordinate scales `a p` and nonnegative upper scales
`b p`, suppose a target coordinate lies between `a p * N` and `b p * N`,
while its active mass lies between `cLower * N` and `cUpper * N`.  A finite
minimum of the `a p` gives a common positive vertex reserve.  If the exponent
is large enough that

`2 * sum_p b p <= E * cLower`,

then the zero vertex has reserve at least `1 / 2`.  The minimum of these two
reserves works simultaneously for any two target/mass pairs satisfying the
same envelopes, in particular for the frozen source mass and the fresh
post-height mass.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Fixed finite coordinate and simplex margins -/

/-- A positive common lower scale for a finite family.  Inserting `1` makes
the definition useful without a nonemptiness assumption on `P`; when `P` is
empty only the zero head vertex remains. -/
noncomputable def
    bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
    {P : Finset Nat} (a : {p : Nat // p ∈ P} → Real) : Real :=
  (insert 1
      ((Finset.univ : Finset {p : Nat // p ∈ P}).image a)).min'
    (Finset.insert_nonempty 1 _)

/-- The finite coordinate floor is positive when every displayed coordinate
scale is positive. -/
theorem bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos
    {P : Finset Nat} (a : {p : Nat // p ∈ P} → Real)
    (ha : ∀ p, 0 < a p) :
    0 < bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a := by
  classical
  unfold bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
  have hmem :=
    Finset.min'_mem
      (insert 1
        ((Finset.univ : Finset {p : Nat // p ∈ P}).image a))
      (Finset.insert_nonempty 1 _)
  rcases Finset.mem_insert.mp hmem with hOne | hcoordinate
  · rw [hOne]
    norm_num
  · obtain ⟨p, _hp, hp⟩ := Finset.mem_image.mp hcoordinate
    rw [← hp]
    exact ha p

/-- The finite coordinate floor lies below every coordinate scale. -/
theorem bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_le
    {P : Finset Nat} (a : {p : Nat // p ∈ P} → Real)
    (p : {p : Nat // p ∈ P}) :
    bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a ≤ a p := by
  classical
  unfold bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
  exact
    Finset.min'_le _ _
      (Finset.mem_insert.mpr
        (Or.inr (Finset.mem_image.mpr
          ⟨p, Finset.mem_univ p, rfl⟩)))

/-- A common head-simplex margin: one half for the zero vertex, intersected
with the lower bound for every nonzero vertex. -/
def bankPaperCanonicalSectionNinePostHeightHeadMargin
    {P : Finset Nat} (E : Nat)
    (a : {p : Nat // p ∈ P} → Real) (cUpper : Real) : Real :=
  min (1 / 2)
    (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a /
      ((E : Real) * cUpper))

/-- The common head-simplex margin is strictly positive. -/
theorem bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
    {P : Finset Nat} (E : Nat)
    (a : {p : Nat // p ∈ P} → Real) (cUpper : Real)
    (hE : 0 < E) (ha : ∀ p, 0 < a p) (hcUpper : 0 < cUpper) :
    0 < bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper := by
  unfold bankPaperCanonicalSectionNinePostHeightHeadMargin
  apply lt_min
  · norm_num
  · exact div_pos
      (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos a ha)
      (mul_pos (by exact_mod_cast hE) hcUpper)

/-! ## Choosing a sufficiently large exponent -/

/-- Every finite nonnegative upper envelope admits a positive integer
exponent satisfying the explicit zero-vertex condition. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_headExponent_large
    {P : Finset Nat} (b : {p : Nat // p ∈ P} → Real)
    (cLower : Real) (hcLower : 0 < cLower) :
    ∃ E : Nat, 0 < E ∧
      2 * (∑ p : {p : Nat // p ∈ P}, b p) ≤
        (E : Real) * cLower := by
  obtain ⟨E0, hE0⟩ :=
    exists_nat_gt
      (2 * (∑ p : {p : Nat // p ∈ P}, b p) / cLower)
  refine ⟨E0 + 1, by omega, ?_⟩
  have hratio :
      2 * (∑ p : {p : Nat // p ∈ P}, b p) / cLower ≤
        (((E0 + 1 : Nat) : Real)) := by
    calc
      2 * (∑ p : {p : Nat // p ∈ P}, b p) / cLower ≤
          (E0 : Real) :=
        hE0.le
      _ ≤ (((E0 + 1 : Nat) : Real)) := by
        norm_num
  exact (div_le_iff₀ hcLower).mp hratio

/-! ## One target/mass pair -/

/-- Linear coordinate and mass envelopes imply uniform positive vertex and
zero-vertex margins for one head target.

The exponent condition is completely explicit.  The resulting margin depends
only on the fixed finite lower envelope, `E`, and `cUpper`, not on `N`, the
target, or the active mass. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
    {P : Finset Nat}
    (E : Nat) (hE : 0 < E)
    (a b : {p : Nat // p ∈ P} → Real)
    (cLower cUpper N q : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (ha : ∀ p, 0 < a p)
    (hb : ∀ p, 0 ≤ b p)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hN : 0 < N) (hq : 0 < q)
    (htargetLower : ∀ p, a p * N ≤ target p)
    (htargetUpper : ∀ p, target p ≤ b p * N)
    (hqLower : cLower * N ≤ q)
    (hqUpper : q ≤ cUpper * N)
    (hElarge :
      2 * (∑ p : {p : Nat // p ∈ P}, b p) ≤
        (E : Real) * cLower) :
    let margin :=
      bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper
    0 < margin ∧
      (∀ p, margin ≤ target p / ((E : Real) * q)) ∧
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * q) := by
  dsimp only
  have hEReal : 0 < (E : Real) := by
    exact_mod_cast hE
  have hEq : 0 < (E : Real) * q :=
    mul_pos hEReal hq
  have hEcLower : 0 < (E : Real) * cLower :=
    mul_pos hEReal hcLower
  have hEcUpper : 0 < (E : Real) * cUpper :=
    mul_pos hEReal hcUpper
  have hmarginPos :
      0 <
        bankPaperCanonicalSectionNinePostHeightHeadMargin
          E a cUpper :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
      E a cUpper hE ha hcUpper
  refine ⟨hmarginPos, ?_, ?_⟩
  · intro p
    apply le_trans (min_le_right _ _)
    apply (div_le_div_iff₀ hEcUpper hEq).2
    have hfloorTarget :
        bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a * N ≤
          target p := by
      exact
        (mul_le_mul_of_nonneg_right
          (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_le a p)
          hN.le).trans (htargetLower p)
    calc
      bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a *
            ((E : Real) * q) =
          ((E : Real) *
              bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a) *
            q := by
        ring
      _ ≤
          ((E : Real) *
              bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a) *
            (cUpper * N) := by
        apply mul_le_mul_of_nonneg_left hqUpper
        exact
          mul_nonneg hEReal.le
            (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos
              a ha).le
      _ =
          (bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor a * N) *
            ((E : Real) * cUpper) := by
        ring
      _ ≤ target p * ((E : Real) * cUpper) :=
        mul_le_mul_of_nonneg_right hfloorTarget hEcUpper.le
  · have htermUpper : ∀ p : {p : Nat // p ∈ P},
        target p / ((E : Real) * q) ≤
          b p / ((E : Real) * cLower) := by
      intro p
      apply (div_le_div_iff₀ hEq hEcLower).2
      calc
        target p * ((E : Real) * cLower) ≤
            (b p * N) * ((E : Real) * cLower) :=
          mul_le_mul_of_nonneg_right (htargetUpper p) hEcLower.le
        _ = ((E : Real) * b p) * (cLower * N) := by
          ring
        _ ≤ ((E : Real) * b p) * q := by
          exact
            mul_le_mul_of_nonneg_left hqLower
              (mul_nonneg hEReal.le (hb p))
        _ = b p * ((E : Real) * q) := by
          ring
    have hsumUpper :
        (∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * q)) ≤
          ∑ p : {p : Nat // p ∈ P},
            b p / ((E : Real) * cLower) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact htermUpper p
    have hbRatio :
        (∑ p : {p : Nat // p ∈ P}, b p) /
              ((E : Real) * cLower) ≤
          1 / 2 := by
      apply (div_le_iff₀ hEcLower).2
      nlinarith [hElarge]
    have hsumHalf :
        (∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * q)) ≤
          1 / 2 := by
      calc
        (∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * q)) ≤
            ∑ p : {p : Nat // p ∈ P},
              b p / ((E : Real) * cLower) :=
          hsumUpper
        _ =
            (∑ p : {p : Nat // p ∈ P}, b p) /
              ((E : Real) * cLower) := by
          rw [Finset.sum_div]
        _ ≤ 1 / 2 := hbRatio
    apply le_trans (min_le_left _ _)
    linarith

/-! ## Simultaneous source and post-height margins -/

/-- The same fixed positive margin works for a frozen source target/mass and
for a fresh post-height target/mass whenever both pairs obey the same fixed
linear envelopes.

This is only finite real algebra.  In particular, neither target is tied to a
certificate or to a source-state predicate. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourceAndPostHeadMargins_of_linearBounds
    {P : Finset Nat}
    (E : Nat) (hE : 0 < E)
    (a b : {p : Nat // p ∈ P} → Real)
    (cLower cUpper N qTilde qn : Real)
    (sourceTarget postTarget : {p : Nat // p ∈ P} → Real)
    (ha : ∀ p, 0 < a p)
    (hb : ∀ p, 0 ≤ b p)
    (hcLower : 0 < cLower) (hcUpper : 0 < cUpper)
    (hN : 0 < N) (hqTilde : 0 < qTilde) (hqn : 0 < qn)
    (hsourceLower : ∀ p, a p * N ≤ sourceTarget p)
    (hsourceUpper : ∀ p, sourceTarget p ≤ b p * N)
    (hpostLower : ∀ p, a p * N ≤ postTarget p)
    (hpostUpper : ∀ p, postTarget p ≤ b p * N)
    (hqTildeLower : cLower * N ≤ qTilde)
    (hqTildeUpper : qTilde ≤ cUpper * N)
    (hqnLower : cLower * N ≤ qn)
    (hqnUpper : qn ≤ cUpper * N)
    (hElarge :
      2 * (∑ p : {p : Nat // p ∈ P}, b p) ≤
        (E : Real) * cLower) :
    let margin :=
      bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper
    0 < margin ∧
      ((∀ p, margin ≤ sourceTarget p / ((E : Real) * qTilde)) ∧
        margin ≤
          1 - ∑ p : {p : Nat // p ∈ P},
            sourceTarget p / ((E : Real) * qTilde)) ∧
      ((∀ p, margin ≤ postTarget p / ((E : Real) * qn)) ∧
        margin ≤
          1 - ∑ p : {p : Nat // p ∈ P},
            postTarget p / ((E : Real) * qn)) := by
  have hsource :=
    bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
      E hE a b cLower cUpper N qTilde sourceTarget
        ha hb hcLower hcUpper hN hqTilde
        hsourceLower hsourceUpper hqTildeLower hqTildeUpper hElarge
  have hpost :=
    bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
      E hE a b cLower cUpper N qn postTarget
        ha hb hcLower hcUpper hN hqn
        hpostLower hpostUpper hqnLower hqnUpper hElarge
  dsimp only at hsource hpost ⊢
  exact ⟨hsource.1, hsource.2, hpost.2⟩

end

end Erdos390.WholePaper
