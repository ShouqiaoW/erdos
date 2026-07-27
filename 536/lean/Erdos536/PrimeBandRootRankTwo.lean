import Erdos536.PrimeBandCollision

/-!
# Annealed rank-two exposed-root estimate

This module keeps the Bernoulli represented-support weight throughout
two-point factorial insertion.  It reindexes the two inserted nine-marks
and the background marking exactly, then identifies the remaining prime
pair sum with `twoPivotReciprocalMassAlong`.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

def supportMarkAt
    {α : Type*} [DecidableEq α] {P : Finset α}
    (S : Finset ↥P) (m : SupportNineMarking S)
    (p : ↥P) : NineMark :=
  if hp : p ∈ S then m ⟨p, hp⟩ else zeroNineMark

def EligibleSupportMarkRankTwo
    {R : Finset ℕ} (T d : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) : Prop :=
  ∃ pq ∈ orderedDistinctPairs S,
    normalizedLogDepth T pq.1.1 ≤ d ∧
    normalizedLogDepth T pq.2.1 ≤ d ∧
    ¬NineMarkCollinear
      (supportMarkAt S m pq.1)
      (supportMarkAt S m pq.2)

noncomputable def annealedEligibleRankTwoSmallBallMass
    (R : Finset ℕ) (T d w : ℝ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S,
          if SupportMarkSmallBall R T w S m ∧
              EligibleSupportMarkRankTwo T d S m
          then (1 / 9 : ℝ) ^ S.card else 0

def markedPairIndicator
    (R : Finset ℕ) (T d w : ℝ)
    (S : Finset ↥R) (p q : ↥R) : ℝ := by
  classical
  exact
    ∑ m : SupportNineMarking S,
      if SupportMarkSmallBall R T w S m ∧
          normalizedLogDepth T p.1 ≤ d ∧
          normalizedLogDepth T q.1 ≤ d ∧
          ¬NineMarkCollinear
            (supportMarkAt S m p) (supportMarkAt S m q)
      then (1 / 9 : ℝ) ^ S.card else 0

noncomputable def annealedMarkedPairSum
    (R : Finset ℕ) (T d w : ℝ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ pq ∈ orderedDistinctPairs S,
          markedPairIndicator R T d w S pq.1 pq.2

theorem annealedEligibleRankTwoSmallBallMass_le_pairSum
    (R : Finset ℕ) (T d w : ℝ) :
    annealedEligibleRankTwoSmallBallMass R T d w ≤
      annealedMarkedPairSum R T d w := by
  classical
  unfold annealedEligibleRankTwoSmallBallMass
    annealedMarkedPairSum
  apply Finset.sum_le_sum
  intro S _hS
  apply mul_le_mul_of_nonneg_left
  · unfold markedPairIndicator
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro m _hm
    by_cases hE :
        SupportMarkSmallBall R T w S m ∧
          EligibleSupportMarkRankTwo T d S m
    · rw [if_pos hE]
      obtain ⟨pq, hpqS, hpDepth, hqDepth, hpqMark⟩ := hE.2
      calc
        (1 / 9 : ℝ) ^ S.card =
            (if SupportMarkSmallBall R T w S m ∧
                  normalizedLogDepth T pq.1.1 ≤ d ∧
                  normalizedLogDepth T pq.2.1 ≤ d ∧
                  ¬NineMarkCollinear
                    (supportMarkAt S m pq.1)
                    (supportMarkAt S m pq.2)
            then (1 / 9 : ℝ) ^ S.card else 0) := by
          rw [if_pos ⟨hE.1, hpDepth, hqDepth, hpqMark⟩]
        _ ≤
            ∑ pq ∈ orderedDistinctPairs S,
              if SupportMarkSmallBall R T w S m ∧
                    normalizedLogDepth T pq.1.1 ≤ d ∧
                    normalizedLogDepth T pq.2.1 ≤ d ∧
                    ¬NineMarkCollinear
                      (supportMarkAt S m pq.1)
                      (supportMarkAt S m pq.2)
              then (1 / 9 : ℝ) ^ S.card else 0 := by
          refine Finset.single_le_sum
            (s := orderedDistinctPairs S)
            (f := fun z =>
              if SupportMarkSmallBall R T w S m ∧
                    normalizedLogDepth T z.1.1 ≤ d ∧
                    normalizedLogDepth T z.2.1 ≤ d ∧
                    ¬NineMarkCollinear
                      (supportMarkAt S m z.1)
                      (supportMarkAt S m z.2)
              then (1 / 9 : ℝ) ^ S.card else 0)
            ?_ hpqS
          · intro z hz
            dsimp
            split_ifs
            · positivity
            · exact le_rfl
    · rw [if_neg hE]
      apply Finset.sum_nonneg
      intro pq _hpq
      split_ifs
      · positivity
      · exact le_rfl
  · apply subtypeBernoulliWeight_nonneg
    · intro p _hp
      exact reciprocalBernoulli_nonneg p
    · intro p _hp
      rw [reciprocalBernoulli]
      apply (div_le_one (by positivity)).mpr
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      linarith

theorem reciprocalBernoulli_odds_eq_reciprocal
    {p : ℕ} (hp : 0 < p) :
    reciprocalBernoulli p /
        (1 - reciprocalBernoulli p) =
      1 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [one_sub_reciprocalBernoulli hp,
    reciprocalBernoulli]
  field_simp [hpR.ne']

theorem annealedMarkedPairSum_eq_insertions
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T d w : ℝ) :
    annealedMarkedPairSum R T d w =
      ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
            (1 / (pq.1.1 : ℝ)) *
              (1 / (pq.2.1 : ℝ)) *
              markedPairIndicator R T d w
                (insert pq.1 (insert pq.2 A))
                pq.1 pq.2 := by
  classical
  have hpow :
      (Finset.univ : Finset (Finset ↥R)) =
        (Finset.univ : Finset ↥R).powerset := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_powerset, true_iff]
    exact Finset.subset_univ S
  unfold annealedMarkedPairSum
  calc
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ pq ∈ orderedDistinctPairs S,
            markedPairIndicator R T d w S pq.1 pq.2) =
        ∑ S ∈ (Finset.univ : Finset ↥R).powerset,
          ∑ pq ∈ orderedDistinctPairs S,
            subsetWeight Finset.univ
                (fun p : ↥R => reciprocalBernoulli p.1) S *
              markedPairIndicator R T d w S pq.1 pq.2 := by
      rw [← hpow]
      simp [subtypeBernoulliWeight_eq_subsetWeight,
        Finset.mul_sum]
    _ = ∑ A ∈ (Finset.univ : Finset ↥R).powerset,
          ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
            subsetWeight Finset.univ
                (fun p : ↥R => reciprocalBernoulli p.1) A *
              (reciprocalBernoulli pq.1.1 /
                (1 - reciprocalBernoulli pq.1.1)) *
              (reciprocalBernoulli pq.2.1 /
                (1 - reciprocalBernoulli pq.2.1)) *
              markedPairIndicator R T d w
                (insert pq.1 (insert pq.2 A))
                pq.1 pq.2 := by
      exact factorialInsertion_two_odds
        Finset.univ
        (fun p : ↥R => reciprocalBernoulli p.1)
        (markedPairIndicator R T d w)
        (fun p _hp => by
          change 1 / ((p.1 : ℝ) + 1) ≠ 1
          have hpR : (0 : ℝ) < p.1 := by
            exact_mod_cast (hR p.1 p.2).pos
          have hlt :
              1 / ((p.1 : ℝ) + 1) < 1 := by
            apply (div_lt_one (by positivity)).mpr
            linarith
          exact hlt.ne)
    _ = ∑ A : Finset ↥R,
          subtypeBernoulliWeight R reciprocalBernoulli A *
            ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
              (1 / (pq.1.1 : ℝ)) *
                (1 / (pq.2.1 : ℝ)) *
                markedPairIndicator R T d w
                  (insert pq.1 (insert pq.2 A))
                  pq.1 pq.2 := by
      rw [← hpow]
      simp only [subtypeBernoulliWeight_eq_subsetWeight]
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro pq _hpq
      have hpPos := (hR pq.1.1 pq.1.2).pos
      have hqPos := (hR pq.2.1 pq.2.2).pos
      rw [reciprocalBernoulli_odds_eq_reciprocal hpPos,
        reciprocalBernoulli_odds_eq_reciprocal hqPos]
      ring

noncomputable def insertTwoSupportMarking
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    SupportNineMarking (insert p (insert q A)) :=
  (supportMarkingInsertEquiv (by simp [hpq, hpA])).symm
    (v, (supportMarkingInsertEquiv hqA).symm (z, m))

noncomputable def supportMarkingInsertTwoEquiv
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A) :
    SupportNineMarking (insert p (insert q A)) ≃
      NineMark × (NineMark × SupportNineMarking A) :=
  (supportMarkingInsertEquiv (by simp [hpq, hpA])).trans
    ((Equiv.refl NineMark).prodCongr
      (supportMarkingInsertEquiv hqA))

@[simp]
theorem supportMarkingInsertTwoEquiv_symm_apply
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    (supportMarkingInsertTwoEquiv hpq hpA hqA).symm
        (v, z, m) =
      insertTwoSupportMarking hpq hpA hqA v z m := by
  rfl

@[simp]
theorem supportMarkAt_insertTwoSupportMarking_first
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    supportMarkAt (insert p (insert q A))
        (insertTwoSupportMarking hpq hpA hqA v z m) p = v := by
  simp [supportMarkAt, insertTwoSupportMarking]

@[simp]
theorem supportMarkAt_insertTwoSupportMarking_second
    {R : Finset ℕ} {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    supportMarkAt (insert p (insert q A))
        (insertTwoSupportMarking hpq hpA hqA v z m) q = z := by
  let hpInsert : p ∉ insert q A := by
    simp [hpq, hpA]
  let mq : SupportNineMarking (insert q A) :=
    (supportMarkingInsertEquiv hqA).symm (z, m)
  unfold supportMarkAt
  rw [dif_pos (by simp)]
  change
    (supportMarkingInsertEquiv hpInsert).symm
        (v, mq) ⟨q, _⟩ = z
  calc
    (supportMarkingInsertEquiv hpInsert).symm
        (v, mq) ⟨q, _⟩ =
      mq ⟨q, mem_insert_self q A⟩ := by
        exact supportMarkingInsertEquiv_symm_tail
          hpInsert v mq ⟨q, mem_insert_self q A⟩
    _ = z := by
      exact supportMarkingInsertEquiv_symm_head hqA z m

theorem supportMarkFirstNormalizedSum_insert_two
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    supportMarkFirstNormalizedSum R T
        (insert p (insert q A))
        (insertTwoSupportMarking hpq hpA hqA v z m) =
      nineMarkLinearFirst v z
          (normalizedLogWeight T p.1)
          (normalizedLogWeight T q.1) +
        supportMarkFirstNormalizedSum R T A m := by
  rw [insertTwoSupportMarking,
    supportMarkFirstNormalizedSum_insert,
    supportMarkFirstNormalizedSum_insert]
  unfold nineMarkLinearFirst
  ring

theorem supportMarkSecondNormalizedSum_insert_two
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    supportMarkSecondNormalizedSum R T
        (insert p (insert q A))
        (insertTwoSupportMarking hpq hpA hqA v z m) =
      nineMarkLinearSecond v z
          (normalizedLogWeight T p.1)
          (normalizedLogWeight T q.1) +
        supportMarkSecondNormalizedSum R T A m := by
  rw [insertTwoSupportMarking,
    supportMarkSecondNormalizedSum_insert,
    supportMarkSecondNormalizedSum_insert]
  unfold nineMarkLinearSecond
  ring

noncomputable def markedPairExpansion
    (R : Finset ℕ) (T d w : ℝ)
    (A : Finset ↥R) (p q : ↥R)
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A) : ℝ := by
  classical
  exact
    ∑ v : NineMark, ∑ z : NineMark,
      ∑ m : SupportNineMarking A,
        if SupportMarkSmallBall R T w
              (insert p (insert q A))
              (insertTwoSupportMarking
                hpq hpA hqA v z m) ∧
            normalizedLogDepth T p.1 ≤ d ∧
            normalizedLogDepth T q.1 ≤ d ∧
            ¬NineMarkCollinear v z
        then (1 / 9 : ℝ) ^
          (insert p (insert q A)).card
        else 0

theorem markedPairIndicator_insert_eq
    {R : Finset ℕ} {T d w : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A) :
    markedPairIndicator R T d w
        (insert p (insert q A)) p q =
      markedPairExpansion R T d w A p q
        hpq hpA hqA := by
  classical
  unfold markedPairIndicator markedPairExpansion
  let F : SupportNineMarking
      (insert p (insert q A)) → ℝ := fun m =>
    if SupportMarkSmallBall R T w
          (insert p (insert q A)) m ∧
        normalizedLogDepth T p.1 ≤ d ∧
        normalizedLogDepth T q.1 ≤ d ∧
        ¬NineMarkCollinear
          (supportMarkAt (insert p (insert q A)) m p)
          (supportMarkAt (insert p (insert q A)) m q)
    then (1 / 9 : ℝ) ^
      (insert p (insert q A)).card
    else 0
  calc
    (∑ m : SupportNineMarking (insert p (insert q A)),
        F m) =
      ∑ data :
          NineMark × (NineMark × SupportNineMarking A),
        F ((supportMarkingInsertTwoEquiv
          hpq hpA hqA).symm data) := by
      apply Fintype.sum_equiv
        (supportMarkingInsertTwoEquiv hpq hpA hqA)
      intro m
      have hleft :=
        (supportMarkingInsertTwoEquiv
          hpq hpA hqA).left_inv m
      exact (congrArg F hleft).symm
    _ = ∑ v : NineMark,
          ∑ data : NineMark × SupportNineMarking A,
            F ((supportMarkingInsertTwoEquiv
              hpq hpA hqA).symm (v, data)) := by
      exact Fintype.sum_prod_type _
    _ = ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            F ((supportMarkingInsertTwoEquiv
              hpq hpA hqA).symm (v, z, m)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact Fintype.sum_prod_type _
    _ = ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            F (insertTwoSupportMarking
              hpq hpA hqA v z m) := by
      apply Finset.sum_congr rfl
      intro v _hv
      apply Finset.sum_congr rfl
      intro z _hz
      apply Finset.sum_congr rfl
      intro m _hm
      exact congrArg F
        (supportMarkingInsertTwoEquiv_symm_apply
          hpq hpA hqA v z m)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _hv
      apply Finset.sum_congr rfl
      intro z _hz
      apply Finset.sum_congr rfl
      intro m _hm
      dsimp [F]
      rw [supportMarkAt_insertTwoSupportMarking_first,
        supportMarkAt_insertTwoSupportMarking_second]

def BackgroundTwoPivotEvent
    {R : Finset ℕ} (T d w : ℝ)
    (A : Finset ↥R) (v z : NineMark)
    (m : SupportNineMarking A) (p q : ↥R) : Prop :=
  normalizedLogDepth T p.1 ≤ d ∧
  normalizedLogDepth T q.1 ≤ d ∧
  ¬NineMarkCollinear v z ∧
  |nineMarkLinearFirst v z
        (normalizedLogWeight T p.1)
        (normalizedLogWeight T q.1) -
      (-supportMarkFirstNormalizedSum R T A m)| ≤ w ∧
  |nineMarkLinearSecond v z
        (normalizedLogWeight T p.1)
        (normalizedLogWeight T q.1) -
      (-supportMarkSecondNormalizedSum R T A m)| ≤ w

noncomputable def backgroundTwoPivotIndicator
    {R : Finset ℕ} (T d w : ℝ)
    (A : Finset ↥R) (v z : NineMark)
    (m : SupportNineMarking A) (p q : ↥R) : ℝ := by
  classical
  exact if BackgroundTwoPivotEvent T d w A v z m p q
    then 1 else 0

theorem supportMarkSmallBall_insert_two_iff
    {R : Finset ℕ} {T d w : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A)
    (v z : NineMark) (m : SupportNineMarking A) :
    SupportMarkSmallBall R T w
        (insert p (insert q A))
        (insertTwoSupportMarking hpq hpA hqA v z m) ∧
      normalizedLogDepth T p.1 ≤ d ∧
      normalizedLogDepth T q.1 ≤ d ∧
      ¬NineMarkCollinear v z ↔
    BackgroundTwoPivotEvent T d w A v z m p q := by
  unfold SupportMarkSmallBall BackgroundTwoPivotEvent
  rw [supportMarkFirstNormalizedSum_insert_two,
    supportMarkSecondNormalizedSum_insert_two]
  constructor
  · rintro ⟨⟨hfirst, hsecond⟩,
      hpDepth, hqDepth, hvz⟩
    exact ⟨hpDepth, hqDepth, hvz, by
      simpa only [sub_neg_eq_add] using hfirst, by
      simpa only [sub_neg_eq_add] using hsecond⟩
  · rintro ⟨hpDepth, hqDepth, hvz,
      hfirst, hsecond⟩
    exact ⟨⟨by
      simpa only [sub_neg_eq_add] using hfirst, by
      simpa only [sub_neg_eq_add] using hsecond⟩,
      hpDepth, hqDepth, hvz⟩

theorem markedPairExpansion_eq_backgroundIndicators
    {R : Finset ℕ} {T d w : ℝ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A) :
    markedPairExpansion R T d w A p q hpq hpA hqA =
      (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            backgroundTwoPivotIndicator
              T d w A v z m p q := by
  classical
  unfold markedPairExpansion
    backgroundTwoPivotIndicator
  have hcard :
      (insert p (insert q A)).card = A.card + 2 := by
    simp [hpq, hpA, hqA]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [hcard]
  by_cases hE :
      BackgroundTwoPivotEvent T d w A v z m p q
  · rw [if_pos hE, if_pos
      ((supportMarkSmallBall_insert_two_iff
        hpq hpA hqA v z m).mpr hE)]
    ring
  · rw [if_neg hE, if_neg]
    · ring
    · exact fun h => hE
        ((supportMarkSmallBall_insert_two_iff
          hpq hpA hqA v z m).mp h)

noncomputable def backgroundTwoPivotPairMass
    {R : Finset ℕ} (T d w : ℝ)
    (A : Finset ↥R) (v z : NineMark)
    (m : SupportNineMarking A) : ℝ := by
  classical
  exact
    ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
      (1 / (pq.1.1 : ℝ)) *
        (1 / (pq.2.1 : ℝ)) *
        backgroundTwoPivotIndicator
          T d w A v z m pq.1 pq.2

theorem backgroundTwoPivotPairMass_eq
    {R : Finset ℕ} (T d w : ℝ)
    (A : Finset ↥R) (v z : NineMark)
    (m : SupportNineMarking A) :
    backgroundTwoPivotPairMass T d w A v z m =
      if ¬NineMarkCollinear v z then
        twoPivotReciprocalMassAlong
          (Finset.univ \ A)
          (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight T p.1)
          (fun p : ↥R =>
            normalizedLogDepth T p.1 ≤ d)
          v z
          (-supportMarkFirstNormalizedSum R T A m)
          (-supportMarkSecondNormalizedSum R T A m)
          w
      else 0 := by
  classical
  by_cases hvz : ¬NineMarkCollinear v z
  · rw [if_pos hvz]
    unfold backgroundTwoPivotPairMass
      twoPivotReciprocalMassAlong
      orderedDistinctPairs
    rw [Finset.sum_filter, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p _hp
    apply Finset.sum_congr rfl
    intro q _hq
    unfold backgroundTwoPivotIndicator
      BackgroundTwoPivotEvent
    by_cases hpq : p ≠ q
    · simp [hpq, hvz]
    · simp [hpq]
  · rw [if_neg hvz]
    unfold backgroundTwoPivotPairMass
      backgroundTwoPivotIndicator
      BackgroundTwoPivotEvent
    apply Finset.sum_eq_zero
    intro pq _hpq
    rw [if_neg]
    · ring
    · intro h
      exact hvz h.2.2.1

theorem backgroundTwoPivotPairMass_le_sq_window
    {R : Finset ℕ} {T d w L : ℝ}
    (A : Finset ↥R) (v z : NineMark)
    (m : SupportNineMarking A)
    (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight T p.1)
          (fun p : ↥R =>
            normalizedLogDepth T p.1 ≤ d)
          x (4 * w) ≤ L) :
    backgroundTwoPivotPairMass T d w A v z m ≤
      L ^ 2 := by
  rw [backgroundTwoPivotPairMass_eq]
  by_cases hvz : ¬NineMarkCollinear v z
  · rw [if_pos hvz]
    apply twoPivotReciprocalMassAlong_le_sq_window
      (Finset.univ \ A)
      (fun p : ↥R => p.1)
      (fun p : ↥R =>
        normalizedLogWeight T p.1)
      (fun p : ↥R =>
        normalizedLogDepth T p.1 ≤ d)
      hvz
      (-supportMarkFirstNormalizedSum R T A m)
      (-supportMarkSecondNormalizedSum R T A m)
      w L hw hL
    intro x
    exact
      (reciprocalWindowMassAlong_mono
        Finset.sdiff_subset
        (fun p : ↥R => p.1)
        (fun p : ↥R =>
          normalizedLogWeight T p.1)
        (fun p : ↥R =>
          normalizedLogDepth T p.1 ≤ d)
        x (4 * w)).trans (hwindow x)
  · rw [if_neg hvz]
    exact sq_nonneg L

noncomputable def insertedMarkedPairSum
    (R : Finset ℕ) (T d w : ℝ)
    (A : Finset ↥R) : ℝ := by
  classical
  exact
    ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
      (1 / (pq.1.1 : ℝ)) *
        (1 / (pq.2.1 : ℝ)) *
        markedPairIndicator R T d w
          (insert pq.1 (insert pq.2 A))
          pq.1 pq.2

theorem insertedMarkedPairSum_eq_background
    (R : Finset ℕ) (T d w : ℝ)
    (A : Finset ↥R) :
    insertedMarkedPairSum R T d w A =
      (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            backgroundTwoPivotPairMass
              T d w A v z m := by
  classical
  unfold insertedMarkedPairSum
  let Q := orderedDistinctPairs (Finset.univ \ A)
  let weight : (↥R × ↥R) → ℝ := fun pq =>
    (1 / (pq.1.1 : ℝ)) *
      (1 / (pq.2.1 : ℝ))
  let I : (↥R × ↥R) → NineMark → NineMark →
      SupportNineMarking A → ℝ :=
    fun pq v z m =>
      backgroundTwoPivotIndicator
        T d w A v z m pq.1 pq.2
  have hexpand (pq : ↥R × ↥R) (hpqQ : pq ∈ Q) :
      markedPairIndicator R T d w
          (insert pq.1 (insert pq.2 A))
          pq.1 pq.2 =
        (1 / 9 : ℝ) ^ (A.card + 2) *
          ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              I pq v z m := by
    have hpqData :=
      mem_orderedDistinctPairs.mp hpqQ
    have hpA :
        pq.1 ∉ A :=
      (Finset.mem_sdiff.mp hpqData.1).2
    have hqA :
        pq.2 ∉ A :=
      (Finset.mem_sdiff.mp hpqData.2.1).2
    rw [markedPairIndicator_insert_eq
      hpqData.2.2 hpA hqA,
      markedPairExpansion_eq_backgroundIndicators
        hpqData.2.2 hpA hqA]
  have hswap :
      (∑ pq ∈ Q, ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            weight pq * I pq v z m) =
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            ∑ pq ∈ Q, weight pq * I pq v z m := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _hv
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _hz
    rw [Finset.sum_comm]
  calc
    (∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
        (1 / (pq.1.1 : ℝ)) *
          (1 / (pq.2.1 : ℝ)) *
          markedPairIndicator R T d w
            (insert pq.1 (insert pq.2 A))
            pq.1 pq.2) =
      ∑ pq ∈ Q,
        weight pq *
          ((1 / 9 : ℝ) ^ (A.card + 2) *
            ∑ v : NineMark, ∑ z : NineMark,
              ∑ m : SupportNineMarking A,
                I pq v z m) := by
      apply Finset.sum_congr rfl
      intro pq hpq
      rw [hexpand pq hpq]
    _ = ∑ pq ∈ Q,
        (1 / 9 : ℝ) ^ (A.card + 2) *
          (weight pq *
            ∑ v : NineMark, ∑ z : NineMark,
              ∑ m : SupportNineMarking A,
                I pq v z m) := by
      apply Finset.sum_congr rfl
      intro pq _hpq
      ring
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ pq ∈ Q,
          weight pq *
            ∑ v : NineMark, ∑ z : NineMark,
              ∑ m : SupportNineMarking A,
                I pq v z m := by
      rw [Finset.mul_sum]
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ pq ∈ Q, ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            weight pq * I pq v z m := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro pq _hpq
      calc
        weight pq *
              (∑ v : NineMark, ∑ z : NineMark,
                ∑ m : SupportNineMarking A,
                  I pq v z m) =
            ∑ v : NineMark,
              weight pq * (∑ z : NineMark,
                ∑ m : SupportNineMarking A,
                  I pq v z m) := by
          exact Finset.mul_sum
            (Finset.univ : Finset NineMark)
            (fun v : NineMark =>
              ∑ z : NineMark,
                ∑ m : SupportNineMarking A,
                  I pq v z m)
            (weight pq)
        _ = ∑ v : NineMark, ∑ z : NineMark,
              weight pq *
                (∑ m : SupportNineMarking A,
                  I pq v z m) := by
          apply Finset.sum_congr rfl
          intro v _hv
          exact Finset.mul_sum
            (Finset.univ : Finset NineMark)
            (fun z : NineMark =>
              ∑ m : SupportNineMarking A,
                I pq v z m)
            (weight pq)
        _ = ∑ v : NineMark, ∑ z : NineMark,
              ∑ m : SupportNineMarking A,
                weight pq * I pq v z m := by
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro z _hz
          exact Finset.mul_sum
            (Finset.univ :
              Finset (SupportNineMarking A))
            (fun m : SupportNineMarking A =>
              I pq v z m)
            (weight pq)
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            ∑ pq ∈ Q, weight pq * I pq v z m := by
      rw [hswap]
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            backgroundTwoPivotPairMass
              T d w A v z m := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro v _hv
      apply Finset.sum_congr rfl
      intro z _hz
      apply Finset.sum_congr rfl
      intro m _hm
      rfl

theorem card_supportNineMarking
    {R : Finset ℕ} (A : Finset ↥R) :
    Fintype.card (SupportNineMarking A) =
      9 ^ A.card := by
  simp only [SupportNineMarking, Fintype.card_fun,
    Fintype.card_coe]
  norm_num

theorem insertedMarkedPairSum_le_sq_window
    {R : Finset ℕ} {T d w L : ℝ}
    (A : Finset ↥R)
    (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight T p.1)
          (fun p : ↥R =>
            normalizedLogDepth T p.1 ≤ d)
          x (4 * w) ≤ L) :
    insertedMarkedPairSum R T d w A ≤ L ^ 2 := by
  rw [insertedMarkedPairSum_eq_background]
  calc
    (1 / 9 : ℝ) ^ (A.card + 2) *
          ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              backgroundTwoPivotPairMass
                T d w A v z m ≤
        (1 / 9 : ℝ) ^ (A.card + 2) *
          ∑ _v : NineMark, ∑ _z : NineMark,
            ∑ _m : SupportNineMarking A,
              L ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro v _hv
        apply Finset.sum_le_sum
        intro z _hz
        apply Finset.sum_le_sum
        intro m _hm
        exact backgroundTwoPivotPairMass_le_sq_window
          A v z m hw hL hwindow
      · positivity
    _ = L ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ,
        card_supportNineMarking]
      have hcardNine :
          Fintype.card NineMark = 9 := by
        norm_num [NineMark]
      rw [hcardNine]
      simp only [nsmul_eq_mul]
      have hpow :
          ((9 ^ A.card : ℕ) : ℝ) =
            (9 : ℝ) ^ A.card := by
        norm_num
      rw [hpow]
      norm_num [pow_add]
      have hcancel :
          (1 / 9 : ℝ) ^ A.card *
              (9 : ℝ) ^ A.card = 1 := by
        rw [← mul_pow]
        norm_num
      calc
        (1 / 9 : ℝ) ^ A.card * (1 / 81) *
              (9 * (9 * ((9 : ℝ) ^ A.card * L ^ 2))) =
            ((1 / 9 : ℝ) ^ A.card *
              (9 : ℝ) ^ A.card) * L ^ 2 := by
          ring
        _ = L ^ 2 := by rw [hcancel, one_mul]

theorem annealedEligibleRankTwoSmallBallMass_le_sq_window
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {T d w L : ℝ}
    (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight T p.1)
          (fun p : ↥R =>
            normalizedLogDepth T p.1 ≤ d)
          x (4 * w) ≤ L) :
    annealedEligibleRankTwoSmallBallMass
        R T d w ≤ L ^ 2 := by
  calc
    annealedEligibleRankTwoSmallBallMass R T d w ≤
        annealedMarkedPairSum R T d w :=
      annealedEligibleRankTwoSmallBallMass_le_pairSum
        R T d w
    _ = ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          insertedMarkedPairSum R T d w A := by
      rw [annealedMarkedPairSum_eq_insertions hR]
      rfl
    _ ≤ ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          L ^ 2 := by
      apply Finset.sum_le_sum
      intro A _hA
      apply mul_le_mul_of_nonneg_left
      · exact insertedMarkedPairSum_le_sq_window
          A hw hL hwindow
      · apply subtypeBernoulliWeight_nonneg
        · intro p _hp
          exact reciprocalBernoulli_nonneg p
        · intro p hp
          have hpOne : (1 : ℝ) ≤ p := by
            exact_mod_cast (hR p hp).one_le
          rw [reciprocalBernoulli]
          apply (div_le_one (by positivity)).mpr
          linarith
    _ = L ^ 2 := by
      rw [← Finset.sum_mul,
        sum_subtypeBernoulliWeight, one_mul]

/-- Ordered two-pivot reciprocal mass with a separate admissibility
condition for each canonical rank. -/
def twoPivotReciprocalMassAlongAsym
    {α : Type*} [DecidableEq α]
    (P : Finset α) (n : α → ℕ) (u : α → ℝ)
    (eligibleP eligibleQ : α → Prop)
    (v q : NineMark) (z₁ z₂ w : ℝ) : ℝ := by
  classical
  exact
    ∑ p ∈ P, ∑ r ∈ P,
      if p ≠ r ∧ eligibleP p ∧ eligibleQ r ∧
          |nineMarkLinearFirst v q (u p) (u r) - z₁| ≤ w ∧
          |nineMarkLinearSecond v q (u p) (u r) - z₂| ≤ w
      then (1 / (n p : ℝ)) * (1 / (n r : ℝ))
      else 0

/-- The determinant interval argument with distinct local-window bounds
for the first and second canonical ranks. -/
theorem twoPivotReciprocalMassAlongAsym_le_mul_window
    {α : Type*} [DecidableEq α]
    (P : Finset α) (n : α → ℕ) (u : α → ℝ)
    (eligibleP eligibleQ : α → Prop)
    [DecidablePred eligibleP] [DecidablePred eligibleQ]
    {v q : NineMark} (hvq : ¬NineMarkCollinear v q)
    (z₁ z₂ w LP LQ : ℝ)
    (hw : 0 ≤ w) (hLP : 0 ≤ LP)
    (hwindowP : ∀ x : ℝ,
      reciprocalWindowMassAlong
        P n u eligibleP x (4 * w) ≤ LP)
    (hwindowQ : ∀ x : ℝ,
      reciprocalWindowMassAlong
        P n u eligibleQ x (4 * w) ≤ LQ) :
    twoPivotReciprocalMassAlongAsym
        P n u eligibleP eligibleQ
        v q z₁ z₂ w ≤ LP * LQ := by
  classical
  let centerP :=
    (signedDigitReal q.2 * z₁ -
      signedDigitReal q.1 * z₂) /
        nineMarkDetReal v q
  let centerQ :=
    (-signedDigitReal v.2 * z₁ +
      signedDigitReal v.1 * z₂) /
        nineMarkDetReal v q
  let a := centerP - 2 * w
  let b := centerQ - 2 * w
  have hmassP :
      0 ≤ reciprocalWindowMassAlong
        P n u eligibleP a (4 * w) := by
    unfold reciprocalWindowMassAlong
    apply Finset.sum_nonneg
    intro p _hp
    split_ifs
    · positivity
    · exact le_rfl
  have hmassQ :
      0 ≤ reciprocalWindowMassAlong
        P n u eligibleQ b (4 * w) := by
    unfold reciprocalWindowMassAlong
    apply Finset.sum_nonneg
    intro p _hp
    split_ifs
    · positivity
    · exact le_rfl
  calc
    twoPivotReciprocalMassAlongAsym
        P n u eligibleP eligibleQ
        v q z₁ z₂ w ≤
      reciprocalWindowMassAlong P n u eligibleP a (4 * w) *
        reciprocalWindowMassAlong P n u eligibleQ b (4 * w) := by
      unfold twoPivotReciprocalMassAlongAsym
        reciprocalWindowMassAlong
      rw [Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      by_cases hevent :
          p ≠ r ∧ eligibleP p ∧ eligibleQ r ∧
            |nineMarkLinearFirst v q (u p) (u r) - z₁| ≤ w ∧
            |nineMarkLinearSecond v q (u p) (u r) - z₂| ≤ w
      · have hinterval :=
          noncollinear_twoPivot_forces_intervals
            hvq hw hevent.2.2.2.1 hevent.2.2.2.2
        have hpInterval :
            eligibleP p ∧ a ≤ u p ∧
              u p ≤ a + 4 * w := by
          exact ⟨hevent.2.1, by
            simpa only [a, centerP] using hinterval.1, by
            simpa only [a, centerP] using hinterval.2.1⟩
        have hrInterval :
            eligibleQ r ∧ b ≤ u r ∧
              u r ≤ b + 4 * w := by
          exact ⟨hevent.2.2.1, by
            simpa only [b, centerQ] using hinterval.2.2.1, by
            simpa only [b, centerQ] using hinterval.2.2.2⟩
        simp [hevent, hpInterval, hrInterval]
      · rw [if_neg hevent]
        apply mul_nonneg
        · split_ifs
          · exact div_nonneg zero_le_one
              (Nat.cast_nonneg (n p))
          · exact le_rfl
        · split_ifs
          · exact div_nonneg zero_le_one
              (Nat.cast_nonneg (n r))
          · exact le_rfl
    _ ≤ LP * LQ :=
      mul_le_mul (hwindowP a) (hwindowQ b)
        hmassQ hLP

end Erdos536
