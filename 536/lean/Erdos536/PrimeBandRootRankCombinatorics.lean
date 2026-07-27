import Erdos536.PrimeBandRootProfileRank

/-!
# Finite combinatorics of canonical support ranks

The depth-lexicographic rank is a genuine enumeration of a finite
support.  This file records that fact and uses it to choose the first
nonzero and first noncollinear marks canonically.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-- Rank is strictly increasing with the injective depth key, on the
represented support. -/
theorem supportDepthRank_lt_of_key_lt
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {p q : ↥R} (hp : p ∈ S)
    (hpq : supportDepthKey T p < supportDepthKey T q) :
    supportDepthRank T S p < supportDepthRank T S q := by
  unfold supportDepthRank
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro r hr
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hr).1,
        (Finset.mem_filter.mp hr).2.trans hpq⟩
  · intro heq
    have hpRight :
        p ∈ S.filter fun r =>
          supportDepthKey T r < supportDepthKey T q :=
      Finset.mem_filter.mpr ⟨hp, hpq⟩
    rw [← heq] at hpRight
    exact (lt_irrefl (supportDepthKey T p))
      (Finset.mem_filter.mp hpRight).2

/-- On the support, numerical rank and the injective depth key induce
the same strict order. -/
theorem supportDepthKey_lt_of_rank_lt
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {p q : ↥R} (_hp : p ∈ S) (hq : q ∈ S)
    (hpq :
      supportDepthRank T S p <
        supportDepthRank T S q) :
    supportDepthKey T p < supportDepthKey T q := by
  rcases lt_trichotomy
      (supportDepthKey T p)
      (supportDepthKey T q) with hlt | heq | hgt
  · exact hlt
  · have hpqPoint : p = q :=
      supportDepthKey_injective T heq
    subst q
    exact False.elim ((lt_irrefl _) hpq)
  · have hqpRank :=
      supportDepthRank_lt_of_key_lt hq hgt
    exact False.elim ((not_lt_of_ge hpq.le) hqpRank)

/-- Every support point has rank below the support cardinality. -/
theorem supportDepthRank_lt_card
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {p : ↥R} (hp : p ∈ S) :
    supportDepthRank T S p < S.card := by
  unfold supportDepthRank
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.filter_subset _ _, ?_⟩
  intro heq
  have hpFilter : p ∈ S.filter fun q =>
      supportDepthKey T q < supportDepthKey T p := by
    rw [heq]
    exact hp
  exact (lt_irrefl (supportDepthKey T p))
    (Finset.mem_filter.mp hpFilter).2

/-- Distinct represented support points have distinct numerical ranks. -/
theorem supportDepthRank_ne_of_ne
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {p q : ↥R} (hp : p ∈ S) (hq : q ∈ S)
    (hpq : p ≠ q) :
    supportDepthRank T S p ≠ supportDepthRank T S q := by
  have hkey :
      supportDepthKey T p ≠ supportDepthKey T q :=
    fun h => hpq (supportDepthKey_injective T h)
  rcases lt_or_gt_of_ne hkey with hpqKey | hqpKey
  · exact ne_of_lt (supportDepthRank_lt_of_key_lt hp hpqKey)
  · exact ne_of_gt (supportDepthRank_lt_of_key_lt hq hqpKey)

/-- The rank, bundled with its sharp finite bound. -/
noncomputable def supportDepthRankFin
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R) :
    ↥S → Fin S.card :=
  fun p => ⟨supportDepthRank T S p.1,
    supportDepthRank_lt_card p.2⟩

theorem supportDepthRankFin_injective
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R) :
    Function.Injective (supportDepthRankFin T S) := by
  intro p q hpq
  apply Subtype.ext
  apply Subtype.ext
  by_contra hpqVal
  have hrankNe :=
    supportDepthRank_ne_of_ne (T := T) p.2 q.2
      (fun hpq => hpqVal (congrArg Subtype.val hpq))
  have hrankEq :=
    congrArg (fun x : Fin S.card => x.1) hpq
  exact hrankNe hrankEq

theorem supportDepthRankFin_bijective
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R) :
    Function.Bijective (supportDepthRankFin T S) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨supportDepthRankFin_injective T S, ?_⟩
  simp

/-- The canonical rank enumeration of the support. -/
noncomputable def supportDepthRankEquiv
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R) :
    ↥S ≃ Fin S.card :=
  Equiv.ofBijective (supportDepthRankFin T S)
    (supportDepthRankFin_bijective T S)

@[simp]
theorem supportDepthRankEquiv_apply_val
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R)
    (p : ↥S) :
    (supportDepthRankEquiv T S p).1 =
      supportDepthRank T S p.1 := by
  rfl

/-- Every admissible numerical rank is attained by a unique support
point. -/
theorem existsUnique_supportDepthRank_eq
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    (i : Fin S.card) :
    ∃! p : ↥S, supportDepthRank T S p.1 = i.1 := by
  obtain ⟨p, hp⟩ :
      ∃ p : ↥S, supportDepthRankFin T S p = i :=
    (supportDepthRankFin_bijective T S).2 i
  have hpRank :=
    congrArg (fun x : Fin S.card => x.1) hp
  refine ⟨p, hpRank, ?_⟩
  intro q hq
  apply supportDepthRankFin_injective T S
  apply Fin.ext
  exact hq.trans hpRank.symm

/-- Inserting two new points in increasing key order does not change the
background count below the first inserted point. -/
theorem supportDepthRank_insert_two_first
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {p q : ↥R}
    (hpq : supportDepthKey T p < supportDepthKey T q) :
    supportDepthRank T (insert p (insert q A)) p =
      (A.filter fun r =>
        supportDepthKey T r < supportDepthKey T p).card := by
  classical
  unfold supportDepthRank
  rw [Finset.filter_insert, if_neg (lt_irrefl _),
    Finset.filter_insert, if_neg (not_lt_of_ge hpq.le)]

/-- The earlier inserted point contributes exactly one to the rank of
the second inserted point. -/
theorem supportDepthRank_insert_two_second
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {p q : ↥R} (hpA : p ∉ A)
    (hpq : supportDepthKey T p < supportDepthKey T q) :
    supportDepthRank T (insert p (insert q A)) q =
      (A.filter fun r =>
        supportDepthKey T r < supportDepthKey T q).card + 1 := by
  classical
  have hpFilter :
      p ∉ A.filter fun r =>
        supportDepthKey T r < supportDepthKey T q := by
    intro hpMem
    exact hpA (Finset.mem_filter.mp hpMem).1
  unfold supportDepthRank
  rw [Finset.filter_insert, if_pos hpq,
    Finset.filter_insert, if_neg (lt_irrefl _),
    Finset.card_insert_of_notMem hpFilter, Nat.add_comm]

/-- Collision-facing form of the two insertion identities: prescribed
full-support ranks are exactly the indicated background filter counts. -/
theorem supportDepthRank_insert_two_eq_iff
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {p q : ↥R} (hpA : p ∉ A)
    (hpq : supportDepthKey T p < supportDepthKey T q)
    (i j : ℕ) :
    (supportDepthRank T (insert p (insert q A)) p = i ∧
        supportDepthRank T (insert p (insert q A)) q = j) ↔
      ((A.filter fun r =>
          supportDepthKey T r < supportDepthKey T p).card = i ∧
        (A.filter fun r =>
          supportDepthKey T r < supportDepthKey T q).card = j - 1 ∧
        0 < j) := by
  rw [supportDepthRank_insert_two_first hpq,
    supportDepthRank_insert_two_second hpA hpq]
  omega

theorem supportDepthRank_le_of_key_le
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {p q : ↥R}
    (hpq :
      supportDepthKey T p ≤ supportDepthKey T q) :
    supportDepthRank T S p ≤ supportDepthRank T S q := by
  unfold supportDepthRank
  apply Finset.card_le_card
  intro r hr
  exact Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hr).1,
      (Finset.mem_filter.mp hr).2.trans_le hpq⟩

/-- The first `k` support points in canonical depth order. -/
def supportRankPrefix
    {R : Finset ℕ} (T : ℝ)
    (S : Finset ↥R) (k : ℕ) :
    Finset ↥S :=
  Finset.univ.filter fun p =>
    supportDepthRank T S p.1 < k

@[simp]
theorem mem_supportRankPrefix
    {R : Finset ℕ} {T : ℝ}
    {S : Finset ↥R} {k : ℕ} {p : ↥S} :
    p ∈ supportRankPrefix T S k ↔
      supportDepthRank T S p.1 < k := by
  simp [supportRankPrefix]

/-- Below the support cardinality, a canonical rank prefix has exactly
the requested number of points. -/
theorem supportRankPrefix_card
    {R : Finset ℕ} {T : ℝ}
    {S : Finset ↥R} {k : ℕ}
    (hk : k ≤ S.card) :
    (supportRankPrefix T S k).card = k := by
  classical
  calc
    (supportRankPrefix T S k).card =
        (Finset.range k).card := by
      apply Finset.card_bij
        (fun p _hp =>
          supportDepthRank T S p.1)
      · intro p hp
        rw [Finset.mem_range]
        exact mem_supportRankPrefix.mp hp
      · intro p _hp q _hq hpqRank
        apply supportDepthRankFin_injective T S
        apply Fin.ext
        exact hpqRank
      · intro i hi
        have hiK : i < k :=
          Finset.mem_range.mp hi
        let iS : Fin S.card :=
          ⟨i, hiK.trans_le hk⟩
        obtain ⟨p, hpRank, _hpUnique⟩ :=
          existsUnique_supportDepthRank_eq
            (T := T) (S := S) iS
        refine ⟨p, ?_, hpRank⟩
        exact mem_supportRankPrefix.mpr
          (by simpa only [hpRank] using hiK)
    _ = k := Finset.card_range k

/-- A key cut through the support is the canonical rank prefix at the
rank of the cutting point.  The cutting point need not itself belong to
the support. -/
theorem supportDepthCut_eq_supportRankPrefix
    {R : Finset ℕ} {T : ℝ}
    {S : Finset ↥R} {p : ↥R} {k : ℕ}
    (hpRank : supportDepthRank T S p = k) :
    (Finset.univ.filter fun r : ↥S =>
        supportDepthKey T r.1 < supportDepthKey T p) =
      supportRankPrefix T S k := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_supportRankPrefix]
  constructor
  · intro hrp
    rw [← hpRank]
    exact supportDepthRank_lt_of_key_lt r.2 hrp
  · intro hrank
    by_contra hnot
    have hle :
        supportDepthRank T S p ≤
          supportDepthRank T S r.1 :=
      supportDepthRank_le_of_key_le
        (le_of_not_gt hnot)
    rw [hpRank] at hle
    exact (not_lt_of_ge hle) hrank

/-- The zero mark is collinear with every mark. -/
theorem zeroNineMark_collinear (v : NineMark) :
    NineMarkCollinear zeroNineMark v := by
  rcases v with ⟨a, b⟩
  simp [NineMarkCollinear, nineMarkDet, zeroNineMark,
    signedDigitValue]

/-- Every mark is collinear with the zero mark. -/
theorem nineMark_collinear_zero (v : NineMark) :
    NineMarkCollinear v zeroNineMark := by
  rcases v with ⟨a, b⟩
  simp [NineMarkCollinear, nineMarkDet, zeroNineMark,
    signedDigitValue]

theorem nineMark_collinear_self (v : NineMark) :
    NineMarkCollinear v v := by
  unfold NineMarkCollinear nineMarkDet
  ring

theorem nineMark_collinear_comm {v w : NineMark} :
    NineMarkCollinear v w ↔ NineMarkCollinear w v := by
  unfold NineMarkCollinear nineMarkDet
  constructor <;> intro h <;> linarith

/-- Two marks on the line of a common nonzero mark are collinear. -/
theorem nineMark_collinear_of_common_nonzero
    {v a b : NineMark} (hv : v ≠ zeroNineMark)
    (ha : NineMarkCollinear v a)
    (hb : NineMarkCollinear v b) :
    NineMarkCollinear a b := by
  have hvCoord :
      signedDigitValue v.1 ≠ 0 ∨
        signedDigitValue v.2 ≠ 0 := by
    rw [← not_and_or]
    intro hzero
    exact hv ((nineMark_eq_zero_iff v).mpr hzero)
  unfold NineMarkCollinear nineMarkDet at ha hb ⊢
  rcases hvCoord with hv₁ | hv₂
  · have hmul :
        signedDigitValue v.1 *
            (signedDigitValue a.1 * signedDigitValue b.2 -
              signedDigitValue a.2 * signedDigitValue b.1) =
          0 := by
      calc
        _ =
            signedDigitValue a.1 *
                (signedDigitValue v.1 * signedDigitValue b.2 -
                  signedDigitValue v.2 * signedDigitValue b.1) -
              signedDigitValue b.1 *
                (signedDigitValue v.1 * signedDigitValue a.2 -
                  signedDigitValue v.2 * signedDigitValue a.1) := by
              ring
        _ = 0 := by rw [ha, hb]; ring
    exact (mul_eq_zero.mp hmul).resolve_left hv₁
  · have hmul :
        signedDigitValue v.2 *
            (signedDigitValue a.1 * signedDigitValue b.2 -
              signedDigitValue a.2 * signedDigitValue b.1) =
          0 := by
      calc
        _ =
            signedDigitValue a.2 *
                (signedDigitValue v.1 * signedDigitValue b.2 -
                  signedDigitValue v.2 * signedDigitValue b.1) -
              signedDigitValue b.2 *
                (signedDigitValue v.1 * signedDigitValue a.2 -
                  signedDigitValue v.2 * signedDigitValue a.1) := by
              ring
        _ = 0 := by rw [ha, hb]; ring
    exact (mul_eq_zero.mp hmul).resolve_left hv₂

/-- A noncollinear pair consists of two distinct nonzero marks. -/
theorem ne_zero_and_ne_zero_and_ne_of_not_collinear
    {v w : NineMark} (h : ¬NineMarkCollinear v w) :
    v ≠ zeroNineMark ∧ w ≠ zeroNineMark ∧ v ≠ w := by
  refine ⟨?_, ?_, ?_⟩
  · intro hv
    exact h (hv ▸ zeroNineMark_collinear w)
  · intro hw
    exact h (hw ▸ nineMark_collinear_zero v)
  · intro hvw
    exact h (hvw ▸ nineMark_collinear_self v)

/-- A first nonzero pivot precedes every mark outside its line. -/
theorem supportDepthKey_lt_of_firstNonzero_not_collinear
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {p q : ↥S}
    (hp : IsFirstNonzeroSupportPivot T m p)
    (hpq : ¬NineMarkCollinear (m p) (m q)) :
    supportDepthKey T p.1 < supportDepthKey T q.1 := by
  rcases lt_trichotomy
      (supportDepthKey T p.1)
      (supportDepthKey T q.1) with hlt | heq | hgt
  · exact hlt
  · have hpqPoint : p = q := by
      apply Subtype.ext
      exact supportDepthKey_injective T heq
    subst q
    exact False.elim (hpq (nineMark_collinear_self (m p)))
  · have hzero := hp.2 q hgt
    exact False.elim
      (hpq (hzero ▸ nineMark_collinear_zero (m p)))

/-- A finite marking with a nonzero mark has a unique first nonzero
pivot, exposed together with its numerical rank. -/
theorem exists_firstNonzeroSupportPivot
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S}
    (hnonzero : ∃ p : ↥S, m p ≠ zeroNineMark) :
    ∃ i : ℕ, ∃ p : ↥S,
      supportDepthRank T S p.1 = i ∧
        IsFirstNonzeroSupportPivot T m p := by
  classical
  let P : ℕ → Prop := fun i =>
    ∃ p : ↥S,
      supportDepthRank T S p.1 = i ∧
        m p ≠ zeroNineMark
  have hP : ∃ i : ℕ, P i := by
    obtain ⟨p, hp⟩ := hnonzero
    exact ⟨supportDepthRank T S p.1, p, rfl, hp⟩
  obtain ⟨p, hpRank, hpNonzero⟩ :=
    Nat.find_spec hP
  refine ⟨Nat.find hP, p, hpRank, hpNonzero, ?_⟩
  intro q hqp
  by_contra hqNonzero
  have hRankLt :
      supportDepthRank T S q.1 <
        supportDepthRank T S p.1 :=
    supportDepthRank_lt_of_key_lt q.2 hqp
  have hFindLt :
      supportDepthRank T S q.1 < Nat.find hP := by
    rw [← hpRank]
    exact hRankLt
  exact (Nat.find_min hP hFindLt)
    ⟨q, rfl, hqNonzero⟩

theorem isFirstNonzeroSupportPivot_unique
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {p q : ↥S}
    (hp : IsFirstNonzeroSupportPivot T m p)
    (hq : IsFirstNonzeroSupportPivot T m q) :
    p = q := by
  rcases lt_trichotomy
      (supportDepthKey T p.1)
      (supportDepthKey T q.1) with hpq | heq | hqp
  · exact False.elim (hp.1 (hq.2 p hpq))
  · apply Subtype.ext
    exact supportDepthKey_injective T heq
  · exact False.elim (hq.1 (hp.2 q hqp))

theorem isFirstNoncollinearSupportPivot_unique
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {p q r : ↥S}
    (hq : IsFirstNoncollinearSupportPivot T m p q)
    (hr : IsFirstNoncollinearSupportPivot T m p r) :
    q = r := by
  rcases lt_trichotomy
      (supportDepthKey T q.1)
      (supportDepthKey T r.1) with hqr | heq | hrq
  · exact False.elim (hq.2.1 (hr.2.2 q hq.1 hqr))
  · apply Subtype.ext
    exact supportDepthKey_injective T heq
  · exact False.elim (hr.2.1 (hq.2.2 r hr.1 hrq))

/-- Every rank-two marking has canonical first and second pivots, and
their ranks are strictly increasing. -/
theorem supportMarkRankTwo_exists_canonical
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S}
    (htwo : SupportMarkRankTwo m) :
    ∃ i j : ℕ, i < j ∧
      CanonicalSupportMarkRankTwo T m i j := by
  classical
  obtain ⟨a, b, _hab, hab⟩ := htwo
  have haNonzero :
      m a ≠ zeroNineMark :=
    (ne_zero_and_ne_zero_and_ne_of_not_collinear hab).1
  obtain ⟨i, p, hpRank, hpFirst⟩ :=
    exists_firstNonzeroSupportPivot (T := T)
      ⟨a, haNonzero⟩
  have hpCandidate :
      ∃ q : ↥S,
        ¬NineMarkCollinear (m p) (m q) := by
    by_contra hnone
    push_neg at hnone
    exact hab
      (nineMark_collinear_of_common_nonzero hpFirst.1
        (hnone a) (hnone b))
  let Q : ℕ → Prop := fun j =>
    ∃ q : ↥S,
      supportDepthRank T S q.1 = j ∧
        ¬NineMarkCollinear (m p) (m q)
  have hQ : ∃ j : ℕ, Q j := by
    obtain ⟨q, hq⟩ := hpCandidate
    exact ⟨supportDepthRank T S q.1, q, rfl, hq⟩
  obtain ⟨q, hqRank, hpqNoncollinear⟩ :=
    Nat.find_spec hQ
  have hpqKey :
      supportDepthKey T p.1 < supportDepthKey T q.1 :=
    supportDepthKey_lt_of_firstNonzero_not_collinear
      hpFirst hpqNoncollinear
  have hpqRank :
      supportDepthRank T S p.1 <
        supportDepthRank T S q.1 :=
    supportDepthRank_lt_of_key_lt p.2 hpqKey
  refine ⟨i, Nat.find hQ, ?_, p, q,
    hpRank, hqRank, hpFirst, hpqKey,
    hpqNoncollinear, ?_⟩
  · rw [← hpRank, ← hqRank]
    exact hpqRank
  · intro r hpr hrq
    by_contra hprNoncollinear
    have hrankLt :
        supportDepthRank T S r.1 <
          supportDepthRank T S q.1 :=
      supportDepthRank_lt_of_key_lt r.2 hrq
    have hfindLt :
        supportDepthRank T S r.1 < Nat.find hQ := by
      rw [← hqRank]
      exact hrankLt
    exact (Nat.find_min hQ hfindLt)
      ⟨r, rfl, hprNoncollinear⟩

theorem canonicalSupportMarkRankTwo_supportMarkRankTwo
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {i j : ℕ}
    (hcanonical : CanonicalSupportMarkRankTwo T m i j) :
    SupportMarkRankTwo m := by
  obtain ⟨p, q, _hpRank, _hqRank, _hpFirst, hpq⟩ :=
    hcanonical
  refine ⟨p, q, ?_, hpq.2.1⟩
  intro hpqPoint
  subst q
  exact (lt_irrefl (supportDepthKey T p.1)) hpq.1

theorem supportMarkRankTwo_iff_exists_canonical
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} :
    SupportMarkRankTwo m ↔
      ∃ i j : ℕ, i < j ∧
        CanonicalSupportMarkRankTwo T m i j := by
  constructor
  · exact supportMarkRankTwo_exists_canonical
  · rintro ⟨i, j, _hij, hcanonical⟩
    exact canonicalSupportMarkRankTwo_supportMarkRankTwo
      hcanonical

theorem canonicalSupportMarkRankTwo_ranks_unique
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {i j i' j' : ℕ}
    (h : CanonicalSupportMarkRankTwo T m i j)
    (h' : CanonicalSupportMarkRankTwo T m i' j') :
    i = i' ∧ j = j' := by
  obtain ⟨p, q, hpRank, hqRank, hpFirst, hqFirst⟩ := h
  obtain ⟨p', q', hpRank', hqRank', hpFirst', hqFirst'⟩ := h'
  have hpp' :=
    isFirstNonzeroSupportPivot_unique hpFirst hpFirst'
  subst p'
  have hqq' :=
    isFirstNoncollinearSupportPivot_unique hqFirst hqFirst'
  subst q'
  exact ⟨hpRank.symm.trans hpRank',
    hqRank.symm.trans hqRank'⟩

/-- Every global rank-one marking has a canonical first pivot. -/
theorem supportMarkRankOne_exists_canonical
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S}
    (hone : SupportMarkRankOne m) :
    ∃ i : ℕ, CanonicalSupportMarkRankOne T m i := by
  obtain ⟨i, p, hpRank, hpFirst⟩ :=
    exists_firstNonzeroSupportPivot (T := T) hone.2
  refine ⟨i, p, hpRank, hpFirst, ?_⟩
  intro q hpq
  by_contra hpqNoncollinear
  apply hone.1
  refine ⟨p, q, ?_, hpqNoncollinear⟩
  intro hpqPoint
  subst q
  exact (lt_irrefl (supportDepthKey T p.1)) hpq

theorem canonicalSupportMarkRankOne_supportMarkRankOne
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {i : ℕ}
    (hcanonical : CanonicalSupportMarkRankOne T m i) :
    SupportMarkRankOne m := by
  obtain ⟨p, _hpRank, hpFirst, hpLine⟩ :=
    hcanonical
  have hpCommon :
      ∀ q : ↥S,
        NineMarkCollinear (m p) (m q) := by
    intro q
    rcases lt_trichotomy
        (supportDepthKey T q.1)
        (supportDepthKey T p.1) with hqp | heq | hpq
    · rw [hpFirst.2 q hqp]
      exact nineMark_collinear_zero (m p)
    · have hqpPoint : q = p := by
        apply Subtype.ext
        exact supportDepthKey_injective T heq
      subst q
      exact nineMark_collinear_self (m p)
    · exact hpLine q hpq
  refine ⟨?_, ⟨p, hpFirst.1⟩⟩
  intro htwo
  obtain ⟨a, b, _hab, habNoncollinear⟩ := htwo
  exact habNoncollinear
    (nineMark_collinear_of_common_nonzero hpFirst.1
      (hpCommon a) (hpCommon b))

theorem supportMarkRankOne_iff_exists_canonical
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} :
    SupportMarkRankOne m ↔
      ∃ i : ℕ, CanonicalSupportMarkRankOne T m i := by
  constructor
  · exact supportMarkRankOne_exists_canonical
  · rintro ⟨i, hi⟩
    exact canonicalSupportMarkRankOne_supportMarkRankOne hi

theorem canonicalSupportMarkRankOne_rank_unique
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {i j : ℕ}
    (hi : CanonicalSupportMarkRankOne T m i)
    (hj : CanonicalSupportMarkRankOne T m j) :
    i = j := by
  obtain ⟨p, hpRank, hpFirst, _hpLine⟩ := hi
  obtain ⟨q, hqRank, hqFirst, _hqLine⟩ := hj
  have hpq :=
    isFirstNonzeroSupportPivot_unique hpFirst hqFirst
  subst q
  exact hpRank.symm.trans hqRank

/-- Prefix rank-one data: the first nonzero rank is `i < K`, every
subsequent support point of rank below `K` stays on its line, and ranks
at least `K` are unrestricted. -/
def CanonicalSupportMarkRankOneBefore
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (i K : ℕ) : Prop :=
  ∃ p : ↥S,
    supportDepthRank T S p.1 = i ∧
    IsFirstNonzeroSupportPivot T m p ∧
    ∀ q : ↥S,
      supportDepthRank T S q.1 < K →
      supportDepthKey T p.1 < supportDepthKey T q.1 →
        NineMarkCollinear (m p) (m q)

/-- Prefix rank zero means precisely that the first `K` canonical ranks
are zero; the tail is unrestricted. -/
def SupportMarkRankZeroBefore
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (K : ℕ) : Prop :=
  ∀ p : ↥S,
    supportDepthRank T S p.1 < K →
      m p = zeroNineMark

theorem canonicalSupportMarkRankOne_before
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {m : SupportNineMarking S} {i K : ℕ}
    (h : CanonicalSupportMarkRankOne T m i) :
    CanonicalSupportMarkRankOneBefore T m i K := by
  obtain ⟨p, hpRank, hpFirst, hpLine⟩ := h
  exact ⟨p, hpRank, hpFirst,
    fun q _hqK hpq => hpLine q hpq⟩

/-- Exact endpoint trichotomy.  Below rank `K`, a marking either has two
canonical pivots, one canonical line pivot, or is identically zero.
Nothing is asserted about the tail at ranks at least `K`. -/
theorem supportMark_rank_trichotomy_before
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    (m : SupportNineMarking S) (K : ℕ) :
    (∃ i j : ℕ, i < j ∧ j < K ∧
        CanonicalSupportMarkRankTwo T m i j) ∨
      (∃ i : ℕ, i < K ∧
        CanonicalSupportMarkRankOneBefore T m i K) ∨
      SupportMarkRankZeroBefore T m K := by
  rcases supportMark_rank_trichotomy m with htwo | hone | hzero
  · obtain ⟨i, j, hij, hcanonical⟩ :=
      supportMarkRankTwo_exists_canonical (T := T) htwo
    by_cases hjK : j < K
    · exact Or.inl ⟨i, j, hij, hjK, hcanonical⟩
    · by_cases hiK : i < K
      · apply Or.inr
        apply Or.inl
        refine ⟨i, hiK, ?_⟩
        obtain ⟨p, q, hpRank, hqRank, hpFirst, hqFirst⟩ :=
          hcanonical
        refine ⟨p, hpRank, hpFirst, ?_⟩
        intro r hrK hpr
        apply hqFirst.2.2 r hpr
        apply supportDepthKey_lt_of_rank_lt r.2 q.2
        rw [hqRank]
        exact hrK.trans_le (le_of_not_gt hjK)
      · apply Or.inr
        apply Or.inr
        intro r hrK
        obtain ⟨p, _q, hpRank, _hqRank, hpFirst, _hqFirst⟩ :=
          hcanonical
        by_contra hrNonzero
        have hri :
            supportDepthRank T S r.1 < i := by
          exact hrK.trans_le (le_of_not_gt hiK)
        have hrp :
            supportDepthKey T r.1 <
              supportDepthKey T p.1 :=
          supportDepthKey_lt_of_rank_lt r.2 p.2
            (by simpa only [hpRank] using hri)
        exact hrNonzero (hpFirst.2 r hrp)
  · obtain ⟨i, hcanonical⟩ :=
      supportMarkRankOne_exists_canonical (T := T) hone
    by_cases hiK : i < K
    · exact Or.inr (Or.inl
        ⟨i, hiK,
          canonicalSupportMarkRankOne_before hcanonical⟩)
    · apply Or.inr
      apply Or.inr
      intro r hrK
      obtain ⟨p, hpRank, hpFirst, _hpLine⟩ := hcanonical
      by_contra hrNonzero
      have hrank :
          supportDepthRank T S r.1 <
            supportDepthRank T S p.1 := by
        rw [hpRank]
        exact hrK.trans_le (le_of_not_gt hiK)
      have hrp :
          supportDepthKey T r.1 <
            supportDepthKey T p.1 :=
        supportDepthKey_lt_of_rank_lt r.2 p.2 hrank
      exact hrNonzero (hpFirst.2 r hrp)
  · exact Or.inr (Or.inr
      (fun p _hpK => hzero p))

/-- A valid delayed endpoint forces at least all advertised pivot ranks
to occur in the represented support. -/
theorem quadraticRootGood_pivotCount_le_support_card
    {T H : ℕ} {w : ℝ}
    {s : Fin 3}
    {S : Finset ↥(quadraticProfilePrimeBand T)}
    {m : SupportNineMarking S}
    (hH :
      H ∈ quadraticDelayedProfileChecks T H)
    (hgood :
      PrimeBandRootGood
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ) w
        (quadraticDelayedProfileDepths T H)
        quadraticDelayedProfileThresholdAtDepth s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m)) :
    quadraticDelayedPivotCount H ≤ S.card := by
  have hd :
      quadraticDelayedProfileDepth H ∈
        quadraticDelayedProfileDepths T H := by
    rw [mem_quadraticDelayedProfileDepths]
    exact ⟨H, hH, rfl⟩
  have hprefix :=
    primeBandRootGood_supportPrefix_card hgood hd
  have hforced :
      quadraticDelayedPivotCount H ≤
        (S.filter fun p =>
          normalizedLogDepth
            ((T ^ 2 : ℕ) : ℝ) p.1 ≤
              quadraticDelayedProfileDepth H).card := by
    simpa only [
      quadraticDelayedProfileThresholdAtDepth_eq,
      quadraticDelayedPivotCount] using hprefix
  exact hforced.trans (Finset.card_filter_le _ _)

end Erdos536
