import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightHeadMarginAlgebra

/-!
# Statement audit: finite post-height head-margin algebra

The expanded example below records the intended boundary: two arbitrary
finite coordinate targets and two positive masses, with only linear real
bounds and one explicit exponent inequality.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

#check bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor
#check bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_pos
#check bankPaperCanonicalSectionNinePostHeightHeadCoordinateFloor_le
#check bankPaperCanonicalSectionNinePostHeightHeadMargin
#check bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
#check exists_bankPaperCanonicalSectionNinePostHeight_headExponent_large
#check bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
#check
  bankPaperCanonicalSectionNinePostHeight_sourceAndPostHeadMargins_of_linearBounds

example
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
  exact
    bankPaperCanonicalSectionNinePostHeight_sourceAndPostHeadMargins_of_linearBounds
      E hE a b cLower cUpper N qTilde qn sourceTarget postTarget
        ha hb hcLower hcUpper hN hqTilde hqn
        hsourceLower hsourceUpper hpostLower hpostUpper
        hqTildeLower hqTildeUpper hqnLower hqnUpper hElarge

end

end Erdos390.WholePaper
