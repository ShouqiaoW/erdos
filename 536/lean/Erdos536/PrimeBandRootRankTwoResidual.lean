import Erdos536.PrimeBandRootRankTwo
import Erdos536.PrimeBandRootTruncatedMarkCounts
import Erdos536.PrimeBandRootRankMass

/-!
# Residual marking after deleting two canonical pivots

This module translates canonical rank-two data on a marking obtained by
inserting two pivots into the exact zero/line/tail background type used by
the truncated marking counts.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-- The marking obtained by inserting two pivots restricts to the original
background marking. -/
@[simp]
theorem insertTwoSupportMarking_background_apply
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A)
    (r : ↥A)
    (hr :
      r.1 ∈ insert p (insert q A)) :
    insertTwoSupportMarking hpq hpA hqA v z m
        ⟨r.1, hr⟩ = m r := by
  let hpInsert : p ∉ insert q A := by
    simp [hpq, hpA]
  let mq : SupportNineMarking (insert q A) :=
    (supportMarkingInsertEquiv hqA).symm (z, m)
  have hrq : r.1 ∈ insert q A :=
    Finset.mem_insert_of_mem r.2
  have houter :
      (supportMarkingInsertEquiv hpInsert).symm
          (v, mq) ⟨r.1, hr⟩ =
        mq ⟨r.1, hrq⟩ := by
    exact supportMarkingInsertEquiv_symm_tail
      hpInsert v mq ⟨r.1, hrq⟩
  have hinner :
      mq ⟨r.1, hrq⟩ = m r := by
    exact supportMarkingInsertEquiv_symm_tail
      hqA z m r
  exact houter.trans hinner

/-- The first inserted pivot has the advertised mark, independently of
the proof used to witness its membership in the enlarged support. -/
@[simp]
theorem insertTwoSupportMarking_first_apply
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A)
    (hp :
      p ∈ insert p (insert q A)) :
    insertTwoSupportMarking hpq hpA hqA v z m
        ⟨p, hp⟩ = v := by
  have hAt :=
    supportMarkAt_insertTwoSupportMarking_first
      hpq hpA hqA v z m
  unfold supportMarkAt at hAt
  rw [dif_pos hp] at hAt
  exact hAt

/-- The second inserted pivot has the advertised mark, independently of
the proof used to witness its membership in the enlarged support. -/
@[simp]
theorem insertTwoSupportMarking_second_apply
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A)
    (hq :
      q ∈ insert p (insert q A)) :
    insertTwoSupportMarking hpq hpA hqA v z m
        ⟨q, hq⟩ = z := by
  have hAt :=
    supportMarkAt_insertTwoSupportMarking_second
      hpq hpA hqA v z m
  unfold supportMarkAt at hAt
  rw [dif_pos hq] at hAt
  exact hAt

/-- If an ambient point is outside a finite background, then a strict
comparison with its background rank forces the corresponding strict
depth-key comparison. -/
theorem supportDepthKey_lt_of_background_rank_lt
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {p r : ↥R} (hpA : p ∉ A) (hrA : r ∈ A)
    (hrank :
      supportDepthRank T A r <
        supportDepthRank T A p) :
    supportDepthKey T r < supportDepthKey T p := by
  rcases lt_trichotomy
      (supportDepthKey T r)
      (supportDepthKey T p) with hrp | heq | hpr
  · exact hrp
  · have hrpPoint : r = p :=
      supportDepthKey_injective T heq
    subst r
    exact False.elim (hpA hrA)
  · have hle :
        supportDepthRank T A p ≤
          supportDepthRank T A r :=
      supportDepthRank_le_of_key_le hpr.le
    exact False.elim ((not_lt_of_ge hle) hrank)

/-- Explicit canonical-pivot data on a two-point insertion leaves exactly
the zero/line/tail residual marking counted by
`TruncatedTwoPivotResidualMarking`.  The two background ranks are included
because they are the identities needed by the factorial-insertion sum. -/
theorem canonicalInsertedRankTwo_background
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    {i j : ℕ} (v z : NineMark) (m : SupportNineMarking A)
    {hp : p ∈ insert p (insert q A)}
    {hq : q ∈ insert p (insert q A)}
    (hpRank :
      supportDepthRank T (insert p (insert q A)) p = i)
    (hqRank :
      supportDepthRank T (insert p (insert q A)) q = j)
    (hpFirst :
      IsFirstNonzeroSupportPivot T
        (insertTwoSupportMarking hpq hpA hqA v z m)
        ⟨p, hp⟩)
    (hqFirst :
      IsFirstNoncollinearSupportPivot T
        (insertTwoSupportMarking hpq hpA hqA v z m)
        ⟨p, hp⟩ ⟨q, hq⟩) :
    v ≠ zeroNineMark ∧
      ¬NineMarkCollinear v z ∧
      supportDepthRank T A p = i ∧
      supportDepthRank T A q = j - 1 ∧
      (∀ r ∈ supportRankPrefix T A i,
        m r = zeroNineMark) ∧
      ∀ r ∈ supportRankPrefix T A (j - 1),
        NineMarkCollinear v (m r) := by
  let inserted :=
    insertTwoSupportMarking hpq hpA hqA v z m
  have hpMark : inserted ⟨p, hp⟩ = v := by
    exact insertTwoSupportMarking_first_apply
      hpq hpA hqA v z m hp
  have hqMark : inserted ⟨q, hq⟩ = z := by
    exact insertTwoSupportMarking_second_apply
      hpq hpA hqA v z m hq
  have hv : v ≠ zeroNineMark := by
    intro hvZero
    apply hpFirst.1
    change inserted ⟨p, hp⟩ = zeroNineMark
    exact hpMark.trans hvZero
  have hvz : ¬NineMarkCollinear v z := by
    intro hvz
    apply hqFirst.2.1
    change NineMarkCollinear
      (inserted ⟨p, hp⟩) (inserted ⟨q, hq⟩)
    rw [hpMark, hqMark]
    exact hvz
  have hpqKey :
      supportDepthKey T p <
        supportDepthKey T q :=
    hqFirst.1
  have hbackgroundRanks :=
    (supportDepthRank_insert_two_eq_iff
      hpA hpqKey i j).mp ⟨hpRank, hqRank⟩
  have hpRankA :
      supportDepthRank T A p = i := by
    exact hbackgroundRanks.1
  have hqRankA :
      supportDepthRank T A q = j - 1 := by
    exact hbackgroundRanks.2.1
  refine ⟨hv, hvz, hpRankA, hqRankA, ?_, ?_⟩
  · intro r hrPrefix
    have hrank :
        supportDepthRank T A r.1 < i :=
      mem_supportRankPrefix.mp hrPrefix
    have hrpKey :
        supportDepthKey T r.1 <
          supportDepthKey T p :=
      supportDepthKey_lt_of_background_rank_lt
        hpA r.2 (by simpa only [hpRankA] using hrank)
    let rInserted : ↥(insert p (insert q A)) :=
      ⟨r.1, by simp [r.2]⟩
    have hrZero :
        inserted rInserted = zeroNineMark :=
      hpFirst.2 rInserted hrpKey
    have hrBackground :
        inserted rInserted = m r := by
      exact insertTwoSupportMarking_background_apply
        hpq hpA hqA v z m r rInserted.2
    exact hrBackground.symm.trans hrZero
  · intro r hrPrefix
    have hrank :
        supportDepthRank T A r.1 < j - 1 :=
      mem_supportRankPrefix.mp hrPrefix
    have hrqKey :
        supportDepthKey T r.1 <
          supportDepthKey T q :=
      supportDepthKey_lt_of_background_rank_lt
        hqA r.2 (by simpa only [hqRankA] using hrank)
    rcases lt_trichotomy
        (supportDepthKey T r.1)
        (supportDepthKey T p) with hrp | heq | hpr
    · let rInserted : ↥(insert p (insert q A)) :=
        ⟨r.1, by simp [r.2]⟩
      have hrZero :
          inserted rInserted = zeroNineMark :=
        hpFirst.2 rInserted hrp
      have hrBackground :
          inserted rInserted = m r := by
        exact insertTwoSupportMarking_background_apply
          hpq hpA hqA v z m r rInserted.2
      rw [← hrBackground, hrZero]
      exact nineMark_collinear_zero v
    · have hrpPoint : r.1 = p :=
        supportDepthKey_injective T heq
      exact False.elim (hpA (hrpPoint ▸ r.2))
    · let rInserted : ↥(insert p (insert q A)) :=
        ⟨r.1, by simp [r.2]⟩
      have hrLine :
          NineMarkCollinear
            (inserted ⟨p, hp⟩)
            (inserted rInserted) :=
        hqFirst.2.2 rInserted hpr hrqKey
      have hrBackground :
          inserted rInserted = m r := by
        exact insertTwoSupportMarking_background_apply
          hpq hpA hqA v z m r rInserted.2
      rw [hpMark, hrBackground] at hrLine
      exact hrLine

/-- Subtype-valued form of `canonicalInsertedRankTwo_background`, ready
for direct use with the exact residual-cardinality theorem. -/
def canonicalInsertedRankTwo_residualMarking
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    {i j : ℕ} (v z : NineMark) (m : SupportNineMarking A)
    {hp : p ∈ insert p (insert q A)}
    {hq : q ∈ insert p (insert q A)}
    (hpRank :
      supportDepthRank T (insert p (insert q A)) p = i)
    (hqRank :
      supportDepthRank T (insert p (insert q A)) q = j)
    (hpFirst :
      IsFirstNonzeroSupportPivot T
        (insertTwoSupportMarking hpq hpA hqA v z m)
        ⟨p, hp⟩)
    (hqFirst :
      IsFirstNoncollinearSupportPivot T
        (insertTwoSupportMarking hpq hpA hqA v z m)
        ⟨p, hp⟩ ⟨q, hq⟩) :
    TruncatedTwoPivotResidualMarking T A i j v :=
  ⟨m,
    (canonicalInsertedRankTwo_background
      hpq hpA hqA v z m hpRank hqRank hpFirst hqFirst).2.2.2.2.1,
    (canonicalInsertedRankTwo_background
      hpq hpA hqA v z m hpRank hqRank hpFirst hqFirst).2.2.2.2.2⟩

/-- Collision-facing wrapper: an ambient canonical-pair event on the
two-point insertion implies all residual facts needed after factorial
deletion. -/
theorem canonicalSupportMarkRankTwoPair_insert_background
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    {i j : ℕ} (v z : NineMark) (m : SupportNineMarking A)
    (hcanonical :
      CanonicalSupportMarkRankTwoPair T
        (insertTwoSupportMarking hpq hpA hqA v z m)
        i j p q) :
    v ≠ zeroNineMark ∧
      ¬NineMarkCollinear v z ∧
      supportDepthRank T A p = i ∧
      supportDepthRank T A q = j - 1 ∧
      (∀ r ∈ supportRankPrefix T A i,
        m r = zeroNineMark) ∧
      ∀ r ∈ supportRankPrefix T A (j - 1),
        NineMarkCollinear v (m r) := by
  obtain ⟨hp, hq, hpRank, hqRank,
    hpFirst, hqFirst⟩ := hcanonical
  exact canonicalInsertedRankTwo_background
    hpq hpA hqA v z m hpRank hqRank hpFirst hqFirst

/-- The direct ambient-pair wrapper, packaged as an inhabitant of the
residual marking type used by the exact cardinality computation. -/
def canonicalSupportMarkRankTwoPair_residualMarking
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    {i j : ℕ} (v z : NineMark) (m : SupportNineMarking A)
    (hcanonical :
      CanonicalSupportMarkRankTwoPair T
        (insertTwoSupportMarking hpq hpA hqA v z m)
        i j p q) :
    TruncatedTwoPivotResidualMarking T A i j v :=
  ⟨m,
    (canonicalSupportMarkRankTwoPair_insert_background
      hpq hpA hqA v z m hcanonical).2.2.2.2.1,
    (canonicalSupportMarkRankTwoPair_insert_background
      hpq hpA hqA v z m hcanonical).2.2.2.2.2⟩

end Erdos536
