import Erdos536.PrimeBandRootRankMass
import Erdos536.PrimeBandRootRankOneInsertion
import Erdos536.PrimeBandRootTruncatedMarkCounts

/-!
# Annealed truncated rank-one mass

This module exposes the canonical first pivot as an ambient support point.
That makes the one-point factorial-insertion identity directly applicable
to the truncated rank-one part of the root-good marking mass.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

set_option maxHeartbeats 800000

/-- A deterministic lower endpoint for the scalar interval forced by a
nonzero one-pivot mark.  Unlike an existentially chosen endpoint, this
depends only on the mark and the deleted background sums, so it is
uniform while the inserted prime varies. -/
noncomputable def onePivotIntervalStart
    (v : NineMark) (z₁ z₂ w : ℝ) : ℝ :=
  if signedDigitReal v.1 = -1 then -z₁ - w
  else if signedDigitReal v.1 = 1 then z₁ - w
  else if signedDigitReal v.2 = -1 then -z₂ - w
  else z₂ - w

theorem nonzero_onePivot_forces_fixed_interval
    {v : NineMark} (hv : v ≠ zeroNineMark)
    {x z₁ z₂ w : ℝ}
    (hfirst :
      |signedDigitReal v.1 * x - z₁| ≤ w)
    (hsecond :
      |signedDigitReal v.2 * x - z₂| ≤ w) :
    onePivotIntervalStart v z₁ z₂ w ≤ x ∧
      x ≤ onePivotIntervalStart v z₁ z₂ w + 2 * w := by
  rcases v with ⟨v₁, v₂⟩
  fin_cases v₁ <;> fin_cases v₂ <;>
    simp [onePivotIntervalStart, zeroNineMark,
      signedDigitReal, signedDigitValue] at hv hfirst hsecond ⊢
  all_goals norm_num at *
  all_goals
    first
    | (rw [abs_le] at hfirst; constructor <;> linarith)
    | (rw [abs_le] at hsecond; constructor <;> linarith)

/-- Fixed-center version of
`supportMarkSmallBall_insert_forces_interval`. -/
theorem supportMarkSmallBall_insert_forces_fixed_interval
    {R : Finset ℕ} {T w : ℝ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A)
    (v : NineMark) (hv : v ≠ zeroNineMark)
    (m : SupportNineMarking A)
    (hsmall :
      SupportMarkSmallBall R T w (insert p A)
        ((supportMarkingInsertEquiv hpA).symm (v, m))) :
    onePivotIntervalStart v
        (-supportMarkFirstNormalizedSum R T A m)
        (-supportMarkSecondNormalizedSum R T A m) w ≤
        normalizedLogWeight T p.1 ∧
      normalizedLogWeight T p.1 ≤
        onePivotIntervalStart v
            (-supportMarkFirstNormalizedSum R T A m)
            (-supportMarkSecondNormalizedSum R T A m) w +
          2 * w := by
  have hcoordinates :=
    (supportMarkSmallBall_insert_iff hpA v m).mp hsmall
  exact nonzero_onePivot_forces_fixed_interval hv
    hcoordinates.1 hcoordinates.2

/-- Ambient-point form of a canonical first pivot whose line condition is
required only below rank `K`. -/
def CanonicalSupportMarkRankOneBeforePoint
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (i K : ℕ) (p : ↥R) : Prop :=
  ∃ hp : p ∈ S,
    supportDepthRank T S p = i ∧
      IsFirstNonzeroSupportPivot T m ⟨p, hp⟩ ∧
      ∀ q : ↥S,
        supportDepthRank T S q.1 < K →
        supportDepthKey T p < supportDepthKey T q.1 →
          NineMarkCollinear (m ⟨p, hp⟩) (m q)

/-- Inserting a point does not change its own depth rank. -/
theorem supportDepthRank_insert_self
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {p : ↥R} :
    supportDepthRank T (insert p A) p =
      supportDepthRank T A p := by
  classical
  unfold supportDepthRank
  rw [Finset.filter_insert, if_neg (lt_irrefl _)]

/-- A newly inserted point contributes one to every later background
rank. -/
theorem supportDepthRank_insert_of_key_lt
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {p r : ↥R} (hpA : p ∉ A)
    (hpr : supportDepthKey T p < supportDepthKey T r) :
    supportDepthRank T (insert p A) r =
      supportDepthRank T A r + 1 := by
  classical
  have hpFilter :
      p ∉ A.filter fun q =>
        supportDepthKey T q < supportDepthKey T r := by
    intro hp
    exact hpA (Finset.mem_filter.mp hp).1
  unfold supportDepthRank
  rw [Finset.filter_insert, if_pos hpr,
    Finset.card_insert_of_notMem hpFilter, Nat.add_comm]

/-- Strict rank comparison against a point outside the background still
forces strict key comparison. -/
theorem supportDepthKey_lt_of_rank_lt_outside
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

/-- Deleting a canonical truncated rank-one pivot leaves exactly a
zero/collinear/unrestricted background of the form counted in
`TruncatedOnePivotResidualMarking`. -/
theorem canonicalSupportMarkRankOneBeforePoint_insert_background
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A)
    {i K : ℕ} (v : NineMark) (m : SupportNineMarking A)
    (hcanonical :
      CanonicalSupportMarkRankOneBeforePoint T
        ((supportMarkingInsertEquiv hpA).symm (v, m))
        i K p) :
    v ≠ zeroNineMark ∧
      supportDepthRank T A p = i ∧
      (∀ r ∈ supportRankPrefix T A i,
        m r = zeroNineMark) ∧
      ∀ r ∈ supportRankPrefix T A (K - 1),
        NineMarkCollinear v (m r) := by
  let inserted :=
    (supportMarkingInsertEquiv hpA).symm (v, m)
  obtain ⟨hpInsert, hpRank, hpFirst, hpLine⟩ :=
    hcanonical
  let pivot : ↥(insert p A) := ⟨p, hpInsert⟩
  have hpMark : inserted pivot = v := by
    have hpivot :
        pivot =
          ⟨p, Finset.mem_insert_self p A⟩ := by
      apply Subtype.ext
      rfl
    rw [hpivot]
    exact supportMarkingInsertEquiv_symm_head hpA v m
  have hv : v ≠ zeroNineMark := by
    intro hvZero
    apply hpFirst.1
    change inserted pivot = zeroNineMark
    rw [hpMark, hvZero]
  have hpRankA :
      supportDepthRank T A p = i := by
    rw [← supportDepthRank_insert_self]
    exact hpRank
  refine ⟨hv, hpRankA, ?_, ?_⟩
  · intro r hr
    have hrank :
        supportDepthRank T A r.1 < i :=
      mem_supportRankPrefix.mp hr
    have hrpKey :
        supportDepthKey T r.1 <
          supportDepthKey T p :=
      supportDepthKey_lt_of_rank_lt_outside
        hpA r.2 (by simpa only [hpRankA] using hrank)
    let rInserted : ↥(insert p A) :=
      ⟨r.1, Finset.mem_insert_of_mem r.2⟩
    have hrZero : inserted rInserted = zeroNineMark :=
      hpFirst.2 rInserted hrpKey
    have hrTail : inserted rInserted = m r := by
      exact supportMarkingInsertEquiv_symm_tail hpA v m r
    exact hrTail.symm.trans hrZero
  · intro r hr
    have hrank :
        supportDepthRank T A r.1 < K - 1 :=
      mem_supportRankPrefix.mp hr
    rcases lt_trichotomy
        (supportDepthKey T r.1)
        (supportDepthKey T p) with hrp | heq | hpr
    · let rInserted : ↥(insert p A) :=
        ⟨r.1, Finset.mem_insert_of_mem r.2⟩
      have hrZero : inserted rInserted = zeroNineMark :=
        hpFirst.2 rInserted hrp
      have hrTail : inserted rInserted = m r := by
        exact supportMarkingInsertEquiv_symm_tail hpA v m r
      rw [← hrTail, hrZero]
      exact nineMarkCollinear_zero_right v
    · have hrpPoint : r.1 = p :=
        supportDepthKey_injective T heq
      exact False.elim (hpA (hrpPoint ▸ r.2))
    · let rInserted : ↥(insert p A) :=
        ⟨r.1, Finset.mem_insert_of_mem r.2⟩
      have hrankInsert :
          supportDepthRank T (insert p A) r.1 < K := by
        rw [supportDepthRank_insert_of_key_lt hpA hpr]
        omega
      have hrLine :=
        hpLine rInserted hrankInsert hpr
      have hrTail : inserted rInserted = m r := by
        exact supportMarkingInsertEquiv_symm_tail hpA v m r
      change NineMarkCollinear
        (inserted pivot) (inserted rInserted) at hrLine
      rw [hpMark, hrTail] at hrLine
      exact hrLine

noncomputable def primeBandRootGoodRankOneBeforePointIndicator
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ)
    (S : Finset ↥R) (p : ↥R) : ℝ := by
  classical
  exact
    ∑ m : SupportNineMarking S,
      if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) ∧
          CanonicalSupportMarkRankOneBeforePoint
            T m i K p
      then (1 / 9 : ℝ) ^ S.card else 0

noncomputable def annealedPrimeBandRootGoodRankOneBeforePointSum
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ p ∈ S,
          primeBandRootGoodRankOneBeforePointIndicator
            R T w depths threshold s i K S p

/-- Exposing the unique canonical first pivot can only overcount the
truncated rank-one mass. -/
theorem annealedPrimeBandRootGoodRankOneBeforeMass_le_pointSum
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ) :
    annealedPrimeBandRootGoodRankOneBeforeMass
        R T w depths threshold s i K ≤
      annealedPrimeBandRootGoodRankOneBeforePointSum
        R T w depths threshold s i K := by
  classical
  unfold annealedPrimeBandRootGoodRankOneBeforeMass
    annealedPrimeBandRootGoodRankOneBeforePointSum
  apply Finset.sum_le_sum
  intro S _hS
  apply mul_le_mul_of_nonneg_left
  · unfold primeBandRootGoodRankOneBeforePointIndicator
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro m _hm
    by_cases hE :
        PrimeBandRootGood R T w depths threshold s
              (S, supportMarkRootFirst s S m,
                supportMarkRootSecond s S m) ∧
            CanonicalSupportMarkRankOneBefore T m i K
    · rw [if_pos hE]
      obtain ⟨p, hpRank, hpFirst, hpLine⟩ := hE.2
      calc
        (1 / 9 : ℝ) ^ S.card =
            (if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBeforePoint
                    T m i K p.1
              then (1 / 9 : ℝ) ^ S.card else 0) := by
          rw [if_pos]
          exact ⟨hE.1, p.2, hpRank, hpFirst, hpLine⟩
        _ ≤
            ∑ p ∈ S,
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBeforePoint
                    T m i K p
              then (1 / 9 : ℝ) ^ S.card else 0 := by
          refine Finset.single_le_sum
            (s := S)
            (f := fun p =>
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBeforePoint
                    T m i K p
              then (1 / 9 : ℝ) ^ S.card else 0)
            ?_ p.2
          intro q hq
          by_cases hqEvent :
              PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBeforePoint
                    T m i K q
          · change 0 ≤
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBeforePoint
                    T m i K q
              then (1 / 9 : ℝ) ^ S.card else 0
            simp [hqEvent]
          · change 0 ≤
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBeforePoint
                    T m i K q
              then (1 / 9 : ℝ) ^ S.card else 0
            simp [hqEvent]
    · rw [if_neg hE]
      apply Finset.sum_nonneg
      intro p hp
      by_cases hpEvent :
          PrimeBandRootGood R T w depths threshold s
                (S, supportMarkRootFirst s S m,
                  supportMarkRootSecond s S m) ∧
              CanonicalSupportMarkRankOneBeforePoint
                T m i K p
      · rw [if_pos hpEvent]
        positivity
      · rw [if_neg hpEvent]
  · apply subtypeBernoulliWeight_nonneg
    · intro p _hp
      exact reciprocalBernoulli_nonneg p
    · intro p _hp
      rw [reciprocalBernoulli]
      apply (div_le_one (by positivity)).mpr
      have hpNonneg : (0 : ℝ) ≤ p := by positivity
      linarith

/-- Exact one-point factorial insertion for the exposed canonical pivot. -/
theorem annealedPrimeBandRootGoodRankOneBeforePointSum_eq_insertions
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ) :
    annealedPrimeBandRootGoodRankOneBeforePointSum
        R T w depths threshold s i K =
      ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ∑ p ∈ Finset.univ \ A,
            (1 / (p.1 : ℝ)) *
              primeBandRootGoodRankOneBeforePointIndicator
                R T w depths threshold s i K
                (insert p A) p := by
  unfold annealedPrimeBandRootGoodRankOneBeforePointSum
  exact annealedPointSum_eq_insertions hR
    (primeBandRootGoodRankOneBeforePointIndicator
      R T w depths threshold s i K)

/-- The one-pivot indicator after deletion, with the pivot mark and the
background marking displayed as separate coordinates. -/
noncomputable def primeBandRootGoodRankOneBeforePointExpansion
    {R : Finset ℕ} (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ)
    (A : Finset ↥R) (p : ↥R) (hpA : p ∉ A) : ℝ := by
  classical
  exact
    ∑ v : NineMark, ∑ m : SupportNineMarking A,
      let inserted :=
        (supportMarkingInsertEquiv hpA).symm (v, m)
      if PrimeBandRootGood R T w depths threshold s
            (insert p A,
              supportMarkRootFirst s (insert p A) inserted,
              supportMarkRootSecond s (insert p A) inserted) ∧
          CanonicalSupportMarkRankOneBeforePoint
            T inserted i K p
      then (1 / 9 : ℝ) ^ (insert p A).card else 0

/-- The deleted-background event, with the proof that the exposed
point is absent packaged existentially.  Proof irrelevance makes this
independent of which absence proof is used for insertion. -/
def PrimeBandRootGoodRankOneBeforeDeletedEvent
    {R : Finset ℕ} (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ)
    (A : Finset ↥R) (p : ↥R)
    (v : NineMark) (m : SupportNineMarking A) : Prop :=
  ∃ hpA : p ∉ A,
    let inserted :=
      (supportMarkingInsertEquiv hpA).symm (v, m)
    PrimeBandRootGood R T w depths threshold s
          (insert p A,
            supportMarkRootFirst s (insert p A) inserted,
            supportMarkRootSecond s (insert p A) inserted) ∧
      CanonicalSupportMarkRankOneBeforePoint
        T inserted i K p

noncomputable instance
    decidablePrimeBandRootGoodRankOneBeforeDeletedEvent
    {R : Finset ℕ} (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ)
    (A : Finset ↥R) (p : ↥R)
    (v : NineMark) (m : SupportNineMarking A) :
    Decidable
      (PrimeBandRootGoodRankOneBeforeDeletedEvent
        T w depths threshold s i K A p v m) :=
  Classical.propDecidable _

/-- The zero/line/tail condition on a deleted one-pivot
background. -/
def TruncatedOnePivotResidualCondition
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i K : ℕ) (v : NineMark)
    (m : SupportNineMarking A) : Prop :=
  v ≠ zeroNineMark ∧
    (∀ r ∈ supportRankPrefix T A i,
      m r = zeroNineMark) ∧
    ∀ r ∈ supportRankPrefix T A (K - 1),
      NineMarkCollinear v (m r)

noncomputable instance
    decidableTruncatedOnePivotResidualCondition
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i K : ℕ) (v : NineMark)
    (m : SupportNineMarking A) :
    Decidable
      (TruncatedOnePivotResidualCondition
        T A i K v m) :=
  Classical.propDecidable _

/-- Direct-coordinate form of the complete residual one-pivot mark
data. -/
abbrev TruncatedOnePivotResidualPair
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i K : ℕ) :=
  {data : NineMark × SupportNineMarking A //
    TruncatedOnePivotResidualCondition
      T A i K data.1 data.2}

/-- Direct residual pairs are the sigma type consisting of a nonzero
pivot mark and a zero/line/tail background. -/
noncomputable def truncatedOnePivotResidualPairEquiv
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i K : ℕ) :
    TruncatedOnePivotResidualPair T A i K ≃
      Σ v : {v : NineMark // v ≠ zeroNineMark},
        TruncatedOnePivotResidualMarking T A i K v.1 where
  toFun data :=
    ⟨⟨data.1.1, data.2.1⟩,
      ⟨data.1.2, data.2.2⟩⟩
  invFun data :=
    ⟨(data.1.1, data.2.1),
      ⟨data.1.2, data.2.2.1, data.2.2.2⟩⟩
  left_inv data := by
    apply Subtype.ext
    rfl
  right_inv data := by
    rcases data with ⟨v, m⟩
    rfl

theorem fintype_sum_ite_const_eq_card_subtype_mul
    {α : Type*} [Fintype α]
    (P : α → Prop) [DecidablePred P] (c : ℝ) :
    (∑ a : α, if P a then c else 0) =
      (Fintype.card {a : α // P a} : ℝ) * c := by
  classical
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul,
    Fintype.card_subtype]

/-- A residual support marking has the same finite coordinates as the
abstract zero/line/tail block used in the exact count. -/
noncomputable def truncatedOnePivotResidualMarkingEquivData
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {i K : ℕ} (hiK : i < K) (hK : K ≤ A.card + 1)
    (v : {v : NineMark // v ≠ zeroNineMark}) :
    TruncatedOnePivotResidualMarking T A i K v.1 ≃
      (Fin (K - 1 - i) →
        {z : NineMark // NineMarkCollinear v.1 z}) ×
      (Fin (A.card - (K - 1)) → NineMark) :=
  Fintype.equivOfCardEq (by
    rw [card_truncatedOnePivotResidualMarking
      (T := T) (A := A) hiK hK v.1 v.2,
      Fintype.card_prod, Fintype.card_pi_const,
      Fintype.card_pi_const,
      card_nineMarkCollinear v.1 v.2]
    norm_num)

/-- Coordinatewise equivalence from direct residual data to the exact
abstract one-pivot mark-data type. -/
noncomputable def truncatedOnePivotResidualSigmaEquivData
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {i K : ℕ} (hiK : i < K) (hK : K ≤ A.card + 1) :
    (Σ v : {v : NineMark // v ≠ zeroNineMark},
      TruncatedOnePivotResidualMarking T A i K v.1) ≃
        TruncatedOnePivotMarkData A i K :=
  Equiv.sigmaCongrRight fun v =>
    truncatedOnePivotResidualMarkingEquivData
      hiK hK v

/-- The exact normalized count of direct-coordinate deleted
one-pivot data. -/
theorem truncatedOnePivotResidualPair_normalized
    {R : Finset ℕ} {T : ℝ} (A : Finset ↥R)
    {i K : ℕ} (hiK : i < K) (hK : K ≤ A.card + 1) :
    (Fintype.card
        (TruncatedOnePivotResidualPair T A i K) : ℝ) /
          (9 : ℝ) ^ (A.card + 1) =
      8 * (1 / 3 : ℝ) ^ K * pivotRankDecay i := by
  rw [Fintype.card_congr
    (truncatedOnePivotResidualPairEquiv T A i K),
    Fintype.card_congr
      (truncatedOnePivotResidualSigmaEquivData
        hiK hK)]
  exact truncatedOnePivotMarkData_normalized A hiK hK

/-- An event which forces eligibility and one fixed interval is bounded
by the corresponding reciprocal-window mass. -/
theorem finset_indicator_reciprocal_le_window
    {α : Type*} [DecidableEq α]
    (D P : Finset α) (hDP : D ⊆ P)
    (n : α → ℕ) (u : α → ℝ)
    (eligible event : α → Prop)
    [DecidablePred eligible] [DecidablePred event]
    (a width : ℝ)
    (hforce : ∀ p ∈ D, event p →
      eligible p ∧ a ≤ u p ∧ u p ≤ a + width) :
    (∑ p ∈ D,
        if event p then 1 / (n p : ℝ) else 0) ≤
      reciprocalWindowMassAlong
        P n u eligible a width := by
  classical
  calc
    (∑ p ∈ D,
        if event p then 1 / (n p : ℝ) else 0) ≤
      reciprocalWindowMassAlong
        D n u eligible a width := by
      unfold reciprocalWindowMassAlong
      apply Finset.sum_le_sum
      intro p hp
      by_cases hevent : event p
      · have hinterval := hforce p hp hevent
        simp [hevent, hinterval]
      · simp [hevent]
        split_ifs
        · positivity
        · exact le_rfl
    _ ≤ reciprocalWindowMassAlong
        P n u eligible a width :=
      reciprocalWindowMassAlong_mono
        hDP n u eligible a width

/-- Exact reindexing of the marking sum after deleting its exposed
canonical pivot. -/
theorem primeBandRootGoodRankOneBeforePointIndicator_insert_eq
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A) :
    primeBandRootGoodRankOneBeforePointIndicator
        R T w depths threshold s i K (insert p A) p =
      primeBandRootGoodRankOneBeforePointExpansion
        T w depths threshold s i K A p hpA := by
  classical
  unfold primeBandRootGoodRankOneBeforePointIndicator
    primeBandRootGoodRankOneBeforePointExpansion
  let F : SupportNineMarking (insert p A) → ℝ := fun m =>
    if PrimeBandRootGood R T w depths threshold s
          (insert p A,
            supportMarkRootFirst s (insert p A) m,
            supportMarkRootSecond s (insert p A) m) ∧
        CanonicalSupportMarkRankOneBeforePoint
          T m i K p
    then (1 / 9 : ℝ) ^ (insert p A).card else 0
  calc
    (∑ m : SupportNineMarking (insert p A), F m) =
        ∑ data : NineMark × SupportNineMarking A,
          F ((supportMarkingInsertEquiv hpA).symm data) := by
      apply Fintype.sum_equiv
        (supportMarkingInsertEquiv hpA)
      intro m
      have hleft :=
        (supportMarkingInsertEquiv hpA).left_inv m
      exact (congrArg F hleft).symm
    _ = ∑ v : NineMark, ∑ m : SupportNineMarking A,
          F ((supportMarkingInsertEquiv hpA).symm
            (v, m)) := by
      exact Fintype.sum_prod_type _
    _ = _ := by
      rfl

theorem primeBandRootGoodRankOneBeforePointExpansion_eq_deletedEvent
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A) :
    primeBandRootGoodRankOneBeforePointExpansion
        T w depths threshold s i K A p hpA =
      ∑ v : NineMark, ∑ m : SupportNineMarking A,
        if PrimeBandRootGoodRankOneBeforeDeletedEvent
            T w depths threshold s i K A p v m
        then (1 / 9 : ℝ) ^ (A.card + 1) else 0 := by
  classical
  unfold primeBandRootGoodRankOneBeforePointExpansion
  apply Finset.sum_congr rfl
  intro v _hv
  apply Finset.sum_congr rfl
  intro m _hm
  have hcard :
      (insert p A).card = A.card + 1 :=
    Finset.card_insert_of_notMem hpA
  rw [hcard]
  dsimp only
  congr 1
  apply propext
  unfold PrimeBandRootGoodRankOneBeforeDeletedEvent
  constructor
  · intro hevent
    exact ⟨hpA, hevent⟩
  · rintro ⟨hpA', hevent⟩
    simpa only using hevent

/-- Every deleted event lies in the counted zero/line/tail residual
class. -/
theorem deletedRankOneBeforeEvent_residual
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ}
    {A : Finset ↥R} {p : ↥R}
    {v : NineMark} {m : SupportNineMarking A}
    (hevent :
      PrimeBandRootGoodRankOneBeforeDeletedEvent
        T w depths threshold s i K A p v m) :
    TruncatedOnePivotResidualCondition
      T A i K v m := by
  rcases hevent with ⟨hpA, hevent⟩
  dsimp only at hevent
  have hbackground :=
    canonicalSupportMarkRankOneBeforePoint_insert_background
      hpA v m hevent.2
  exact ⟨hbackground.1, hbackground.2.2.1,
    hbackground.2.2.2⟩

/-- Root-goodness, the canonical-rank profile lower bound, and the
one-pivot geometry place every deleted event in one common eligible
window for its fixed pivot mark and background marking. -/
theorem deletedRankOneBeforeEvent_forces_eligible_interval
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ} {ell : ℕ → ℝ}
    {A : Finset ↥R} {p : ↥R}
    {v : NineMark} {m : SupportNineMarking A}
    (hw : 0 ≤ w)
    (hprofile :
      ∀ {S : Finset ↥R} (mS : SupportNineMarking S)
          (q : ↥R) (_hq : q ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S mS,
              supportMarkRootSecond s S mS) →
        supportDepthRank T S q = i →
        ell i ≤ normalizedLogWeight T q.1)
    (hevent :
      PrimeBandRootGoodRankOneBeforeDeletedEvent
        T w depths threshold s i K A p v m) :
    ell i ≤ normalizedLogWeight T p.1 ∧
      onePivotIntervalStart v
          (-supportMarkFirstNormalizedSum R T A m)
          (-supportMarkSecondNormalizedSum R T A m) w ≤
        normalizedLogWeight T p.1 ∧
      normalizedLogWeight T p.1 ≤
        onePivotIntervalStart v
            (-supportMarkFirstNormalizedSum R T A m)
            (-supportMarkSecondNormalizedSum R T A m) w +
          4 * w := by
  rcases hevent with ⟨hpA, hevent⟩
  dsimp only at hevent
  let inserted :=
    (supportMarkingInsertEquiv hpA).symm (v, m)
  obtain ⟨hpInsert, hpRank, _hpFirst, _hpLine⟩ :=
    hevent.2
  have heligible :
      ell i ≤ normalizedLogWeight T p.1 :=
    hprofile inserted p hpInsert hevent.1 hpRank
  have hbackground :=
    canonicalSupportMarkRankOneBeforePoint_insert_background
      hpA v m hevent.2
  have hsmall :
      SupportMarkSmallBall R T w (insert p A) inserted :=
    primeBandRootGood_supportMark_smallBall hevent.1
  have hinterval :=
    supportMarkSmallBall_insert_forces_fixed_interval
      hpA v hbackground.1 m hsmall
  exact ⟨heligible, hinterval.1,
    hinterval.2.trans (by linarith)⟩

/-- For fixed pivot mark and deleted background, the inserted-prime
sum is one reciprocal window; outside the exact residual class it
vanishes. -/
theorem deletedRankOneBeforeEvent_reciprocalSum_le_residual
    {R : Finset ℕ} {T w C : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ} {ell : ℕ → ℝ}
    (A : Finset ↥R) (v : NineMark)
    (m : SupportNineMarking A)
    (hw : 0 ≤ w)
    (hprofile :
      ∀ {S : Finset ↥R} (mS : SupportNineMarking S)
          (q : ↥R) (_hq : q ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S mS,
              supportMarkRootSecond s S mS) →
        supportDepthRank T S q = i →
        ell i ≤ normalizedLogWeight T q.1)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          (Finset.univ : Finset ↥R)
          (fun q : ↥R => q.1)
          (fun q : ↥R =>
            normalizedLogWeight T q.1)
          (fun q : ↥R =>
            ell i ≤ normalizedLogWeight T q.1)
          x (4 * w) ≤ C * w / ell i) :
    (∑ p ∈ (Finset.univ : Finset ↥R) \ A,
        if PrimeBandRootGoodRankOneBeforeDeletedEvent
            T w depths threshold s i K A p v m
        then 1 / (p.1 : ℝ) else 0) ≤
      if TruncatedOnePivotResidualCondition
          T A i K v m
      then C * w / ell i else 0 := by
  classical
  by_cases hresidual :
      TruncatedOnePivotResidualCondition
        T A i K v m
  · rw [if_pos hresidual]
    let a :=
      onePivotIntervalStart v
        (-supportMarkFirstNormalizedSum R T A m)
        (-supportMarkSecondNormalizedSum R T A m) w
    calc
      (∑ p ∈ (Finset.univ : Finset ↥R) \ A,
          if PrimeBandRootGoodRankOneBeforeDeletedEvent
              T w depths threshold s i K A p v m
          then 1 / (p.1 : ℝ) else 0) ≤
        reciprocalWindowMassAlong
          (Finset.univ : Finset ↥R)
          (fun q : ↥R => q.1)
          (fun q : ↥R =>
            normalizedLogWeight T q.1)
          (fun q : ↥R =>
            ell i ≤ normalizedLogWeight T q.1)
          a (4 * w) := by
        apply finset_indicator_reciprocal_le_window
          ((Finset.univ : Finset ↥R) \ A)
          Finset.univ Finset.sdiff_subset
          (fun q : ↥R => q.1)
          (fun q : ↥R =>
            normalizedLogWeight T q.1)
          (fun q : ↥R =>
            ell i ≤ normalizedLogWeight T q.1)
          (fun p : ↥R =>
            PrimeBandRootGoodRankOneBeforeDeletedEvent
              T w depths threshold s i K A p v m)
          a (4 * w)
        intro p _hp hevent
        exact
          deletedRankOneBeforeEvent_forces_eligible_interval
            hw hprofile hevent
      _ ≤ C * w / ell i := hwindow a
  · rw [if_neg hresidual]
    apply Finset.sum_nonpos
    intro p hp
    have hnoevent :
        ¬PrimeBandRootGoodRankOneBeforeDeletedEvent
          T w depths threshold s i K A p v m := by
      intro hevent
      exact hresidual
        (deletedRankOneBeforeEvent_residual hevent)
    simp [hnoevent]

/-- After one-point factorial insertion, the complete fixed-rank
one-pivot contribution is the exact residual marking probability times
one reciprocal window. -/
theorem insertedPrimeBandRootGoodRankOneBeforePointSum_le
    {R : Finset ℕ} {T w C : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ} {ell : ℕ → ℝ}
    (A : Finset ↥R)
    (hw : 0 ≤ w) (hiK : i < K)
    (hK : K ≤ A.card + 1)
    (hprofile :
      ∀ {S : Finset ↥R} (mS : SupportNineMarking S)
          (q : ↥R) (_hq : q ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S mS,
              supportMarkRootSecond s S mS) →
        supportDepthRank T S q = i →
        ell i ≤ normalizedLogWeight T q.1)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          (Finset.univ : Finset ↥R)
          (fun q : ↥R => q.1)
          (fun q : ↥R =>
            normalizedLogWeight T q.1)
          (fun q : ↥R =>
            ell i ≤ normalizedLogWeight T q.1)
          x (4 * w) ≤ C * w / ell i) :
    (∑ p ∈ (Finset.univ : Finset ↥R) \ A,
        (1 / (p.1 : ℝ)) *
          primeBandRootGoodRankOneBeforePointIndicator
            R T w depths threshold s i K
            (insert p A) p) ≤
      8 * (1 / 3 : ℝ) ^ K * pivotRankDecay i *
        (C * w / ell i) := by
  classical
  let D : Finset ↥R :=
    (Finset.univ : Finset ↥R) \ A
  let qMass : ℝ := (1 / 9 : ℝ) ^ (A.card + 1)
  let windowMass : ℝ := C * w / ell i
  have hrewrite :
      (∑ p ∈ D,
          (1 / (p.1 : ℝ)) *
            primeBandRootGoodRankOneBeforePointIndicator
              R T w depths threshold s i K
              (insert p A) p) =
        ∑ p ∈ D,
          (1 / (p.1 : ℝ)) *
            ∑ v : NineMark,
              ∑ m : SupportNineMarking A,
                if
                  PrimeBandRootGoodRankOneBeforeDeletedEvent
                    T w depths threshold s i K A p v m
                then qMass else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    have hpA : p ∉ A :=
      (Finset.mem_sdiff.mp hp).2
    rw [primeBandRootGoodRankOneBeforePointIndicator_insert_eq
      hpA,
      primeBandRootGoodRankOneBeforePointExpansion_eq_deletedEvent
        hpA]
  rw [show
    (Finset.univ : Finset ↥R) \ A = D by rfl,
    hrewrite]
  calc
    (∑ p ∈ D,
        (1 / (p.1 : ℝ)) *
          ∑ v : NineMark,
            ∑ m : SupportNineMarking A,
              if
                PrimeBandRootGoodRankOneBeforeDeletedEvent
                  T w depths threshold s i K A p v m
              then qMass else 0) =
      ∑ p ∈ D,
        ∑ v : NineMark,
          ∑ m : SupportNineMarking A,
            if
              PrimeBandRootGoodRankOneBeforeDeletedEvent
                T w depths threshold s i K A p v m
            then qMass * (1 / (p.1 : ℝ)) else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      by_cases hevent :
          PrimeBandRootGoodRankOneBeforeDeletedEvent
            T w depths threshold s i K A p v m
      · simp [hevent]
        ring
      · simp [hevent]
    _ =
      ∑ v : NineMark,
        ∑ m : SupportNineMarking A,
          ∑ p ∈ D,
            if
              PrimeBandRootGoodRankOneBeforeDeletedEvent
                T w depths threshold s i K A p v m
            then qMass * (1 / (p.1 : ℝ)) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.sum_comm]
    _ =
      qMass *
        ∑ v : NineMark,
          ∑ m : SupportNineMarking A,
            ∑ p ∈ D,
              if
                PrimeBandRootGoodRankOneBeforeDeletedEvent
                  T w depths threshold s i K A p v m
              then 1 / (p.1 : ℝ) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hevent :
          PrimeBandRootGoodRankOneBeforeDeletedEvent
            T w depths threshold s i K A p v m
      · simp [hevent]
      · simp [hevent]
    _ ≤
      qMass *
        ∑ v : NineMark,
          ∑ m : SupportNineMarking A,
            if TruncatedOnePivotResidualCondition
                T A i K v m
            then windowMass else 0 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro v _hv
        apply Finset.sum_le_sum
        intro m _hm
        exact
          deletedRankOneBeforeEvent_reciprocalSum_le_residual
            A v m hw hprofile hwindow
      · dsimp only [qMass]
        positivity
    _ =
      qMass *
        (Fintype.card
          (TruncatedOnePivotResidualPair T A i K) : ℝ) *
        windowMass := by
      rw [mul_assoc]
      congr 1
      calc
        (∑ v : NineMark,
            ∑ m : SupportNineMarking A,
              if TruncatedOnePivotResidualCondition
                  T A i K v m
              then windowMass else 0) =
            ∑ data :
                NineMark × SupportNineMarking A,
              if TruncatedOnePivotResidualCondition
                  T A i K data.1 data.2
              then windowMass else 0 :=
          (Fintype.sum_prod_type
            (fun data :
                NineMark × SupportNineMarking A =>
              if TruncatedOnePivotResidualCondition
                  T A i K data.1 data.2
              then windowMass else 0)).symm
        _ = _ :=
          fintype_sum_ite_const_eq_card_subtype_mul
            (fun data :
                NineMark × SupportNineMarking A =>
              TruncatedOnePivotResidualCondition
                T A i K data.1 data.2)
            windowMass
    _ =
      8 * (1 / 3 : ℝ) ^ K * pivotRankDecay i *
        (C * w / ell i) := by
      have hnormalized :=
        truncatedOnePivotResidualPair_normalized
          (T := T) A hiK hK
      dsimp only [qMass, windowMass]
      rw [one_div_pow]
      calc
        1 / (9 : ℝ) ^ (A.card + 1) *
              (Fintype.card
                (TruncatedOnePivotResidualPair
                  T A i K) : ℝ) *
              (C * w / ell i) =
            ((Fintype.card
                (TruncatedOnePivotResidualPair
                  T A i K) : ℝ) /
              (9 : ℝ) ^ (A.card + 1)) *
              (C * w / ell i) := by ring
        _ = _ := by rw [hnormalized]

/-- Canonical fixed-rank truncated one-pivot mass bound.  The factor
`8 * 3^{-K} * pivotRankDecay i` is the exact marking probability; the
remaining factor is the uniform reciprocal prime window. -/
theorem annealedPrimeBandRootGoodRankOneBeforeMass_le_of_window
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {T w C : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i K : ℕ} {ell : ℕ → ℝ}
    (hw : 0 ≤ w) (hiK : i < K)
    (hcard :
      ∀ (S : Finset ↥R) (m : SupportNineMarking S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) →
        K ≤ S.card)
    (hprofile :
      ∀ {S : Finset ↥R} (mS : SupportNineMarking S)
          (q : ↥R) (_hq : q ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S mS,
              supportMarkRootSecond s S mS) →
        supportDepthRank T S q = i →
        ell i ≤ normalizedLogWeight T q.1)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          (Finset.univ : Finset ↥R)
          (fun q : ↥R => q.1)
          (fun q : ↥R =>
            normalizedLogWeight T q.1)
          (fun q : ↥R =>
            ell i ≤ normalizedLogWeight T q.1)
          x (4 * w) ≤ C * w / ell i) :
    annealedPrimeBandRootGoodRankOneBeforeMass
        R T w depths threshold s i K ≤
      8 * C * w * (1 / 3 : ℝ) ^ K *
        (pivotRankDecay i / ell i) := by
  classical
  have hwindowMass :
      0 ≤ C * w / ell i := by
    calc
      0 ≤ reciprocalWindowMassAlong
          (Finset.univ : Finset ↥R)
          (fun q : ↥R => q.1)
          (fun q : ↥R =>
            normalizedLogWeight T q.1)
          (fun q : ↥R =>
            ell i ≤ normalizedLogWeight T q.1)
          0 (4 * w) := by
        unfold reciprocalWindowMassAlong
        apply Finset.sum_nonneg
        intro q _hq
        split_ifs
        · positivity
        · exact le_rfl
      _ ≤ C * w / ell i := hwindow 0
  calc
    annealedPrimeBandRootGoodRankOneBeforeMass
        R T w depths threshold s i K ≤
      annealedPrimeBandRootGoodRankOneBeforePointSum
        R T w depths threshold s i K :=
      annealedPrimeBandRootGoodRankOneBeforeMass_le_pointSum
        R T w depths threshold s i K
    _ =
      ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ∑ p ∈ (Finset.univ : Finset ↥R) \ A,
            (1 / (p.1 : ℝ)) *
              primeBandRootGoodRankOneBeforePointIndicator
                R T w depths threshold s i K
                (insert p A) p := by
      exact
        annealedPrimeBandRootGoodRankOneBeforePointSum_eq_insertions
          hR T w depths threshold s i K
    _ ≤
      ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          (8 * (1 / 3 : ℝ) ^ K *
            pivotRankDecay i * (C * w / ell i)) := by
      apply Finset.sum_le_sum
      intro A _hA
      apply mul_le_mul_of_nonneg_left
      · by_cases hK : K ≤ A.card + 1
        · exact
            insertedPrimeBandRootGoodRankOneBeforePointSum_le
              A hw hiK hK hprofile hwindow
        · have hzero :
              (∑ p ∈
                  (Finset.univ : Finset ↥R) \ A,
                (1 / (p.1 : ℝ)) *
                  primeBandRootGoodRankOneBeforePointIndicator
                    R T w depths threshold s i K
                    (insert p A) p) = 0 := by
            apply Finset.sum_eq_zero
            intro p hp
            have hpA : p ∉ A :=
              (Finset.mem_sdiff.mp hp).2
            have hindicator :
                primeBandRootGoodRankOneBeforePointIndicator
                    R T w depths threshold s i K
                    (insert p A) p = 0 := by
              unfold
                primeBandRootGoodRankOneBeforePointIndicator
              apply Finset.sum_eq_zero
              intro m _hm
              by_cases hevent :
                  PrimeBandRootGood R T w depths threshold s
                        (insert p A,
                          supportMarkRootFirst s
                            (insert p A) m,
                          supportMarkRootSecond s
                            (insert p A) m) ∧
                    CanonicalSupportMarkRankOneBeforePoint
                      T m i K p
              · have hKInsert :=
                  hcard (insert p A) m hevent.1
                have hcardInsert :
                    (insert p A).card = A.card + 1 :=
                  Finset.card_insert_of_notMem hpA
                exact False.elim
                  (hK (by simpa only [hcardInsert]
                    using hKInsert))
              · simp [hevent]
            rw [hindicator, mul_zero]
          rw [hzero]
          apply mul_nonneg
          · unfold pivotRankDecay
            positivity
          · exact hwindowMass
      · apply subtypeBernoulliWeight_nonneg
        · intro p _hp
          exact reciprocalBernoulli_nonneg p
        · intro p hp
          rw [reciprocalBernoulli]
          apply (div_le_one (by positivity)).mpr
          have hpOne : (1 : ℝ) ≤ p := by
            exact_mod_cast (hR p hp).one_le
          linarith
    _ =
      8 * (1 / 3 : ℝ) ^ K *
        pivotRankDecay i * (C * w / ell i) := by
      rw [← Finset.sum_mul,
        sum_subtypeBernoulliWeight, one_mul]
    _ =
      8 * C * w * (1 / 3 : ℝ) ^ K *
        (pivotRankDecay i / ell i) := by ring

end Erdos536
