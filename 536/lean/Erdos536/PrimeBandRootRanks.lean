import Erdos536.PrimeBandProfileEndpoint
import Erdos536.PrimeBandRootRankOneGeometry
import Mathlib.Data.Prod.Lex

/-!
# Canonical depth ranks on represented supports

Support points are ordered lexicographically by normalized depth and
then by their underlying natural value.  The natural tie-breaker makes
the key injective while retaining the depth-prefix comparison needed by
the delayed profile.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-- Injective lexicographic key: shallower normalized depth comes first,
with the underlying natural value breaking ties. -/
noncomputable def supportDepthKey
    {R : Finset ℕ} (T : ℝ) (p : ↥R) :
    ℝ ×ₗ ℕ :=
  toLex (normalizedLogDepth T p.1, p.1)

theorem supportDepthKey_injective
    {R : Finset ℕ} (T : ℝ) :
    Function.Injective
      (supportDepthKey (R := R) T) := by
  intro p q hpq
  have hval :
      p.1 = q.1 :=
    congrArg (fun z : ℝ ×ₗ ℕ => (ofLex z).2) hpq
  exact Subtype.ext hval

/-- Zero-indexed position of `p` in the depth-lexicographic order on
`S`.  The definition is meaningful for all ambient points; canonical
pivots additionally carry a proof that `p ∈ S`. -/
noncomputable def supportDepthRank
    {R : Finset ℕ} (T : ℝ)
    (S : Finset ↥R) (p : ↥R) : ℕ :=
  (S.filter fun q =>
    supportDepthKey T q < supportDepthKey T p).card

/-- `p` is the first nonzero mark in depth order. -/
def IsFirstNonzeroSupportPivot
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (p : ↥S) : Prop :=
  m p ≠ zeroNineMark ∧
    ∀ q : ↥S,
      supportDepthKey T q.1 < supportDepthKey T p.1 →
        m q = zeroNineMark

/-- After the first pivot `p`, `q` is the first mark outside its line. -/
def IsFirstNoncollinearSupportPivot
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (p q : ↥S) : Prop :=
  supportDepthKey T p.1 < supportDepthKey T q.1 ∧
    ¬NineMarkCollinear (m p) (m q) ∧
    ∀ r : ↥S,
      supportDepthKey T p.1 < supportDepthKey T r.1 →
      supportDepthKey T r.1 < supportDepthKey T q.1 →
        NineMarkCollinear (m p) (m r)

/-- Canonical rank-two data with the numerical positions exposed. -/
def CanonicalSupportMarkRankTwo
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (i j : ℕ) : Prop :=
  ∃ p q : ↥S,
    supportDepthRank T S p.1 = i ∧
    supportDepthRank T S q.1 = j ∧
    IsFirstNonzeroSupportPivot T m p ∧
    IsFirstNoncollinearSupportPivot T m p q

/-- Canonical rank-one data: after the first nonzero mark, every later
mark remains on its line. -/
def CanonicalSupportMarkRankOne
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (i : ℕ) : Prop :=
  ∃ p : ↥S,
    supportDepthRank T S p.1 = i ∧
    IsFirstNonzeroSupportPivot T m p ∧
    ∀ q : ↥S,
      supportDepthKey T p.1 < supportDepthKey T q.1 →
        NineMarkCollinear (m p) (m q)

theorem fiveStateDepthPrefix_supportMarkRootFirst
    {R : Finset ℕ} (T d : ℝ) (s : Fin 3)
    (S : Finset ↥R) (m : SupportNineMarking S) :
    fiveStateDepthPrefix R T s
        (supportMarkRootFirst s S m) d =
      S.filter fun p =>
        normalizedLogDepth T p.1 ≤ d := by
  ext p
  by_cases hp : p ∈ S
  · simp [fiveStateDepthPrefix, supportMarkRootFirst,
      hp]
  · simp [fiveStateDepthPrefix, supportMarkRootFirst,
      hp]

theorem primeBandRootGood_supportMark_prefixCard
    {R : Finset ℕ} {T w d : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {S : Finset ↥R}
    {m : SupportNineMarking S}
    (hgood :
      PrimeBandRootGood R T w depths threshold s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m))
    (hd : d ∈ depths) :
    3 * threshold d ≤ eligibleSupportCard T d S := by
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(representedActiveLabels s) :
          Set ActiveFiveLabel)
        (fun l =>
          fiveLabelDepthPrefix R T
            (supportMarkRootFirst s S m) l d) := by
    intro l _hl q _hq hlq
    exact fiveLabelDepthPrefix_disjoint hlq
  have hsum :
      (∑ l ∈ representedActiveLabels s,
          threshold d) ≤
        ∑ l ∈ representedActiveLabels s,
          (fiveLabelDepthPrefix R T
            (supportMarkRootFirst s S m) l d).card := by
    apply Finset.sum_le_sum
    intro l hl
    exact hgood.1 ⟨l, hl⟩ ⟨d, hd⟩
  rw [← Finset.card_biUnion hdisjoint,
    ← fiveStateDepthPrefix_eq_biUnion,
    fiveStateDepthPrefix_supportMarkRootFirst] at hsum
  simpa [eligibleSupportCard,
    card_representedActiveLabels, mul_comm] using hsum

theorem depth_le_of_supportDepthRank_lt_prefixCard
    {R : Finset ℕ} {T d : ℝ}
    {S : Finset ↥R} {p : ↥R}
    (hrank :
      supportDepthRank T S p <
        eligibleSupportCard T d S) :
    normalizedLogDepth T p.1 ≤ d := by
  by_cases hpDepth :
      normalizedLogDepth T p.1 ≤ d
  · exact hpDepth
  · have hdepth :
        d < normalizedLogDepth T p.1 :=
      lt_of_not_ge hpDepth
    have hsubset :
        S.filter (fun q =>
            normalizedLogDepth T q.1 ≤ d) ⊆
          S.filter (fun q =>
            supportDepthKey T q <
              supportDepthKey T p) := by
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      apply Finset.mem_filter.mpr
      refine ⟨hqData.1, ?_⟩
      apply Prod.Lex.toLex_lt_toLex.mpr
      exact Or.inl (hqData.2.trans_lt hdepth)
    have hcard :=
      Finset.card_le_card hsubset
    exfalso
    exact (Nat.not_lt_of_ge hcard) hrank

theorem normalizedLogWeight_lower_of_supportDepthRank
    {R : Finset ℕ} {T d : ℝ}
    {S : Finset ↥R} {p : ↥R}
    (hweight : 0 < normalizedLogWeight T p.1)
    (hrank :
      supportDepthRank T S p <
        eligibleSupportCard T d S) :
    Real.exp (-d) ≤ normalizedLogWeight T p.1 := by
  exact normalizedLogWeight_lower_of_depth_le hweight
    (depth_le_of_supportDepthRank_lt_prefixCard
      hrank)

end Erdos536
