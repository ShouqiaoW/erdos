import Erdos536.PrimeBandRootRankTwoResidual

/-!
# Fixed-rank annealed rank-two mass bound

This module combines canonical two-pivot deletion, the exact residual
marking count, and the asymmetric two-dimensional small-ball estimate.
The result is deliberately phrased with abstract eligibility predicates:
the delayed-profile specialization only has to provide a lower-weight
eligibility statement at each of the two canonical ranks.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

set_option maxHeartbeats 800000

/-- The structural conditions left on the background after deleting
canonical pivots of ranks `i < j`. -/
def RankTwoBackgroundStructural
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i j : ℕ) (v z : NineMark)
    (m : SupportNineMarking A) : Prop :=
  v ≠ zeroNineMark ∧
    ¬NineMarkCollinear v z ∧
    (∀ r ∈ supportRankPrefix T A i,
      m r = zeroNineMark) ∧
    ∀ r ∈ supportRankPrefix T A (j - 1),
      NineMarkCollinear v (m r)

/-- Once the two pivot marks are known to be nonzero/noncollinear, the
structural predicate on the background is precisely the residual
marking subtype. -/
def rankTwoBackgroundStructuralMarkingEquiv
    {R : Finset ℕ} {T : ℝ} {A : Finset ↥R}
    {i j : ℕ} {v z : NineMark}
    (hv : v ≠ zeroNineMark)
    (hz : ¬NineMarkCollinear v z) :
    {m : SupportNineMarking A //
      RankTwoBackgroundStructural T A i j v z m} ≃
      TruncatedTwoPivotResidualMarking T A i j v where
  toFun m :=
    ⟨m.1, m.2.2.2.1, m.2.2.2.2⟩
  invFun m :=
    ⟨m.1, hv, hz, m.2.1, m.2.2⟩
  left_inv m := by
    rfl
  right_inv m := by
    rfl

/-- Reciprocal mass of ordered inserted pairs satisfying the two
eligibility predicates and the two affine small-ball inequalities. -/
noncomputable def rankTwoAsymBackgroundPairMass
    {R : Finset ℕ} (T w : ℝ) (A : Finset ↥R)
    (eligibleP eligibleQ : ↥R → Prop)
    (v z : NineMark) (m : SupportNineMarking A) : ℝ := by
  classical
  exact
    ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
      if eligibleP pq.1 ∧ eligibleQ pq.2 ∧
          |nineMarkLinearFirst v z
              (normalizedLogWeight T pq.1.1)
              (normalizedLogWeight T pq.2.1) -
            (-supportMarkFirstNormalizedSum R T A m)| ≤ w ∧
          |nineMarkLinearSecond v z
              (normalizedLogWeight T pq.1.1)
              (normalizedLogWeight T pq.2.1) -
            (-supportMarkSecondNormalizedSum R T A m)| ≤ w
      then (1 / (pq.1.1 : ℝ)) *
        (1 / (pq.2.1 : ℝ))
      else 0

/-- Identification of the preceding ordered-pair sum with the generic
asymmetric reciprocal mass. -/
theorem rankTwoAsymBackgroundPairMass_eq
    {R : Finset ℕ} {T w : ℝ} (A : Finset ↥R)
    (eligibleP eligibleQ : ↥R → Prop)
    [DecidablePred eligibleP] [DecidablePred eligibleQ]
    (v z : NineMark) (m : SupportNineMarking A) :
    rankTwoAsymBackgroundPairMass
        T w A eligibleP eligibleQ v z m =
      twoPivotReciprocalMassAlongAsym
        (Finset.univ \ A)
        (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleP eligibleQ v z
        (-supportMarkFirstNormalizedSum R T A m)
        (-supportMarkSecondNormalizedSum R T A m) w := by
  classical
  unfold rankTwoAsymBackgroundPairMass
    twoPivotReciprocalMassAlongAsym
    orderedDistinctPairs
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p _hp
  apply Finset.sum_congr rfl
  intro q _hq
  by_cases hpq : p ≠ q
  · simp [hpq]
  · simp [hpq]

/-- Uniform asymmetric window bounds on the whole band also control
every deleted-background pair mass. -/
theorem rankTwoAsymBackgroundPairMass_le_mul_window
    {R : Finset ℕ} {T w LP LQ : ℝ}
    (A : Finset ↥R)
    (eligibleP eligibleQ : ↥R → Prop)
    [DecidablePred eligibleP] [DecidablePred eligibleQ]
    (v z : NineMark) (m : SupportNineMarking A)
    (hvz : ¬NineMarkCollinear v z)
    (hw : 0 ≤ w) (hLP : 0 ≤ LP)
    (hwindowP : ∀ x : ℝ,
      reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleP x (4 * w) ≤ LP)
    (hwindowQ : ∀ x : ℝ,
      reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleQ x (4 * w) ≤ LQ) :
    rankTwoAsymBackgroundPairMass
        T w A eligibleP eligibleQ v z m ≤
      LP * LQ := by
  rw [rankTwoAsymBackgroundPairMass_eq]
  apply twoPivotReciprocalMassAlongAsym_le_mul_window
    (Finset.univ \ A)
    (fun p : ↥R => p.1)
    (fun p : ↥R => normalizedLogWeight T p.1)
    eligibleP eligibleQ hvz
    (-supportMarkFirstNormalizedSum R T A m)
    (-supportMarkSecondNormalizedSum R T A m)
    w LP LQ hw hLP
  · intro x
    exact
      (reciprocalWindowMassAlong_mono
        Finset.sdiff_subset
        (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleP x (4 * w)).trans (hwindowP x)
  · intro x
    exact
      (reciprocalWindowMassAlong_mono
        Finset.sdiff_subset
        (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleQ x (4 * w)).trans (hwindowQ x)

/-- Indicator for an inserted pair to be the two advertised canonical
pivots of a root-good marking.  It is total on ambient pairs; outside
the distinct complement of the background it is zero. -/
noncomputable def rankTwoCanonicalBackgroundIndicator
    {R : Finset ℕ} (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i j : ℕ) (A : Finset ↥R)
    (v z : NineMark) (m : SupportNineMarking A)
    (p q : ↥R) : ℝ := by
  classical
  exact
    if h : p ≠ q ∧ p ∉ A ∧ q ∉ A then
      let inserted :=
        insertTwoSupportMarking h.1 h.2.1 h.2.2 v z m
      if PrimeBandRootGood R T w depths threshold s
            (insert p (insert q A),
              supportMarkRootFirst s
                (insert p (insert q A)) inserted,
              supportMarkRootSecond s
                (insert p (insert q A)) inserted) ∧
          CanonicalSupportMarkRankTwoPair
            T inserted i j p q
      then 1 else 0
    else 0

/-- Reindex the full marking in the canonical pair indicator into its
two inserted marks and its background marking. -/
theorem primeBandRootGoodRankTwoPairIndicator_insert_eq
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i j : ℕ}
    {A : Finset ↥R} {p q : ↥R}
    (hpq : p ≠ q) (hpA : p ∉ A) (hqA : q ∉ A) :
    primeBandRootGoodRankTwoPairIndicator
        R T w depths threshold s i j
        (insert p (insert q A)) p q =
      (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            rankTwoCanonicalBackgroundIndicator
              T w depths threshold s i j A
              v z m p q := by
  classical
  let S := insert p (insert q A)
  let F : SupportNineMarking S → ℝ := fun M =>
    if PrimeBandRootGood R T w depths threshold s
          (S, supportMarkRootFirst s S M,
            supportMarkRootSecond s S M) ∧
        CanonicalSupportMarkRankTwoPair
          T M i j p q
    then (1 / 9 : ℝ) ^ S.card else 0
  have hcard : S.card = A.card + 2 := by
    dsimp [S]
    simp [hpq, hpA, hqA]
  unfold primeBandRootGoodRankTwoPairIndicator
  change (∑ M : SupportNineMarking S, F M) = _
  calc
    (∑ M : SupportNineMarking S, F M) =
        ∑ data :
            NineMark × (NineMark × SupportNineMarking A),
          F ((supportMarkingInsertTwoEquiv
            hpq hpA hqA).symm data) := by
      apply Fintype.sum_equiv
        (supportMarkingInsertTwoEquiv hpq hpA hqA)
      intro M
      have hleft :=
        (supportMarkingInsertTwoEquiv
          hpq hpA hqA).left_inv M
      exact (congrArg F hleft).symm
    _ = ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            F (insertTwoSupportMarking
              hpq hpA hqA v z m) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro z _hz
      apply Finset.sum_congr rfl
      intro m _hm
      exact congrArg F
        (supportMarkingInsertTwoEquiv_symm_apply
          hpq hpA hqA v z m)
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
          ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              rankTwoCanonicalBackgroundIndicator
                T w depths threshold s i j A
                v z m p q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _hm
      dsimp [F]
      unfold rankTwoCanonicalBackgroundIndicator
      rw [dif_pos ⟨hpq, hpA, hqA⟩, hcard]
      by_cases hE :
          PrimeBandRootGood R T w depths threshold s
              (S, supportMarkRootFirst s S
                (insertTwoSupportMarking
                  hpq hpA hqA v z m),
                supportMarkRootSecond s S
                  (insertTwoSupportMarking
                    hpq hpA hqA v z m)) ∧
            CanonicalSupportMarkRankTwoPair T
              (insertTwoSupportMarking
                hpq hpA hqA v z m) i j p q
      · rw [if_pos hE, if_pos]
        · ring
        · simpa only [S] using hE
      · rw [if_neg hE, if_neg]
        · ring
        · simpa only [S] using hE

/-- Canonical-pair reciprocal mass for fixed inserted marks and a fixed
background marking. -/
noncomputable def rankTwoCanonicalBackgroundPairMass
    {R : Finset ℕ} (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i j : ℕ) (A : Finset ↥R)
    (v z : NineMark) (m : SupportNineMarking A) : ℝ := by
  classical
  exact
    ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
      (1 / (pq.1.1 : ℝ)) *
        (1 / (pq.2.1 : ℝ)) *
        rankTwoCanonicalBackgroundIndicator
          T w depths threshold s i j A
          v z m pq.1 pq.2

/-- After factorial deletion, commute the inserted prime pair past the
two marks and the background marking. -/
theorem insertedRankTwoPairSum_eq_background
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i j : ℕ} (A : Finset ↥R) :
    (∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
      (1 / (pq.1.1 : ℝ)) *
        (1 / (pq.2.1 : ℝ)) *
        primeBandRootGoodRankTwoPairIndicator
          R T w depths threshold s i j
          (insert pq.1 (insert pq.2 A))
          pq.1 pq.2) =
      (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            rankTwoCanonicalBackgroundPairMass
              T w depths threshold s i j A v z m := by
  classical
  let Q := orderedDistinctPairs (Finset.univ \ A)
  let odds : (↥R × ↥R) → ℝ := fun pq =>
    (1 / (pq.1.1 : ℝ)) * (1 / (pq.2.1 : ℝ))
  let I : (↥R × ↥R) → NineMark → NineMark →
      SupportNineMarking A → ℝ :=
    fun pq v z m =>
      rankTwoCanonicalBackgroundIndicator
        T w depths threshold s i j A v z m pq.1 pq.2
  have hexpand (pq : ↥R × ↥R) (hpqQ : pq ∈ Q) :
      primeBandRootGoodRankTwoPairIndicator
          R T w depths threshold s i j
          (insert pq.1 (insert pq.2 A))
          pq.1 pq.2 =
        (1 / 9 : ℝ) ^ (A.card + 2) *
          ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              I pq v z m := by
    have hpqData := mem_orderedDistinctPairs.mp hpqQ
    exact primeBandRootGoodRankTwoPairIndicator_insert_eq
      hpqData.2.2
      (Finset.mem_sdiff.mp hpqData.1).2
      (Finset.mem_sdiff.mp hpqData.2.1).2
  change
    (∑ pq ∈ Q, odds pq *
      primeBandRootGoodRankTwoPairIndicator
        R T w depths threshold s i j
        (insert pq.1 (insert pq.2 A)) pq.1 pq.2) = _
  calc
    (∑ pq ∈ Q, odds pq *
        primeBandRootGoodRankTwoPairIndicator
          R T w depths threshold s i j
          (insert pq.1 (insert pq.2 A)) pq.1 pq.2) =
      ∑ pq ∈ Q, odds pq *
        ((1 / 9 : ℝ) ^ (A.card + 2) *
          ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              I pq v z m) := by
        apply Finset.sum_congr rfl
        intro pq hpq
        rw [hexpand pq hpq]
    _ = ∑ pq ∈ Q,
        (1 / 9 : ℝ) ^ (A.card + 2) *
          (odds pq * ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              I pq v z m) := by
      apply Finset.sum_congr rfl
      intro pq _hpq
      ring
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ pq ∈ Q,
          odds pq * ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              I pq v z m := by
      rw [Finset.mul_sum]
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ pq ∈ Q, ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            odds pq * I pq v z m := by
      apply congrArg
      apply Finset.sum_congr rfl
      intro pq _hpq
      calc
        odds pq * (∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A, I pq v z m) =
          ∑ v : NineMark,
            odds pq * (∑ z : NineMark,
              ∑ m : SupportNineMarking A,
                I pq v z m) := by
            exact Finset.mul_sum _ _ _
        _ = ∑ v : NineMark, ∑ z : NineMark,
            odds pq * (∑ m : SupportNineMarking A,
              I pq v z m) := by
          apply Finset.sum_congr rfl
          intro v _hv
          exact Finset.mul_sum _ _ _
        _ = ∑ v : NineMark, ∑ z : NineMark,
            ∑ m : SupportNineMarking A,
              odds pq * I pq v z m := by
          apply Finset.sum_congr rfl
          intro v _hv
          apply Finset.sum_congr rfl
          intro z _hz
          exact Finset.mul_sum _ _ _
    _ = (1 / 9 : ℝ) ^ (A.card + 2) *
        ∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            ∑ pq ∈ Q, odds pq * I pq v z m := by
      apply congrArg
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _hz
      rw [Finset.sum_comm]
    _ = _ := by
      rfl

/-- The window-product allowance for one fixed background marking. -/
noncomputable def rankTwoStructuralPairBound
    {R : Finset ℕ} (T : ℝ) (A : Finset ↥R)
    (i j : ℕ) (v z : NineMark)
    (m : SupportNineMarking A) (LP LQ : ℝ) : ℝ := by
  classical
  exact
    if RankTwoBackgroundStructural T A i j v z m
    then LP * LQ else 0

/-- For fixed inserted marks and background marking, a canonical
root-good pair is dominated by the corresponding asymmetric small-ball
pair mass.  If the background is not structurally compatible with the
advertised canonical ranks, its mass is exactly zero. -/
theorem rankTwoCanonicalBackgroundPairMass_le
    {R : Finset ℕ} {T w LP LQ : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i j : ℕ} (A : Finset ↥R)
    (eligibleP eligibleQ : ↥R → Prop)
    [DecidablePred eligibleP] [DecidablePred eligibleQ]
    (v z : NineMark) (m : SupportNineMarking A)
    (hw : 0 ≤ w) (hLP : 0 ≤ LP)
    (hEligibleP :
      ∀ (S : Finset ↥R) (M : SupportNineMarking S)
          (p : ↥R) (_hp : p ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S M,
              supportMarkRootSecond s S M) →
          supportDepthRank T S p = i →
          eligibleP p)
    (hEligibleQ :
      ∀ (S : Finset ↥R) (M : SupportNineMarking S)
          (q : ↥R) (_hq : q ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S M,
              supportMarkRootSecond s S M) →
          supportDepthRank T S q = j →
          eligibleQ q)
    (hwindowP : ∀ x : ℝ,
      reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleP x (4 * w) ≤ LP)
    (hwindowQ : ∀ x : ℝ,
      reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleQ x (4 * w) ≤ LQ) :
    rankTwoCanonicalBackgroundPairMass
        T w depths threshold s i j A v z m ≤
      rankTwoStructuralPairBound
        T A i j v z m LP LQ := by
  classical
  unfold rankTwoStructuralPairBound
  have hleAsym :
      rankTwoCanonicalBackgroundPairMass
          T w depths threshold s i j A v z m ≤
        rankTwoAsymBackgroundPairMass
          T w A eligibleP eligibleQ v z m := by
    unfold rankTwoCanonicalBackgroundPairMass
      rankTwoAsymBackgroundPairMass
    apply Finset.sum_le_sum
    intro pq hpqMem
    have hpqData := mem_orderedDistinctPairs.mp hpqMem
    have hpA :
        pq.1 ∉ A :=
      (Finset.mem_sdiff.mp hpqData.1).2
    have hqA :
        pq.2 ∉ A :=
      (Finset.mem_sdiff.mp hpqData.2.1).2
    have hpq : pq.1 ≠ pq.2 := hpqData.2.2
    unfold rankTwoCanonicalBackgroundIndicator
    rw [dif_pos ⟨hpq, hpA, hqA⟩]
    let inserted :=
      insertTwoSupportMarking hpq hpA hqA v z m
    let S := insert pq.1 (insert pq.2 A)
    by_cases hE :
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S inserted,
              supportMarkRootSecond s S inserted) ∧
          CanonicalSupportMarkRankTwoPair
            T inserted i j pq.1 pq.2
    · rw [if_pos hE]
      obtain ⟨hpS, hqS, hpRank, hqRank,
        _hpFirst, _hqFirst⟩ := hE.2
      have hpEligible :
          eligibleP pq.1 :=
        hEligibleP S inserted pq.1 hpS hE.1 hpRank
      have hqEligible :
          eligibleQ pq.2 :=
        hEligibleQ S inserted pq.2 hqS hE.1 hqRank
      have hsmall :
          SupportMarkSmallBall R T w S inserted :=
        primeBandRootGood_supportMark_smallBall hE.1
      have hfirst :
          |nineMarkLinearFirst v z
                (normalizedLogWeight T pq.1.1)
                (normalizedLogWeight T pq.2.1) -
              (-supportMarkFirstNormalizedSum R T A m)| ≤ w := by
        have h := hsmall.1
        dsimp [S, inserted] at h
        rw [supportMarkFirstNormalizedSum_insert_two
          hpq hpA hqA] at h
        simpa only [sub_neg_eq_add] using h
      have hsecond :
          |nineMarkLinearSecond v z
                (normalizedLogWeight T pq.1.1)
                (normalizedLogWeight T pq.2.1) -
              (-supportMarkSecondNormalizedSum R T A m)| ≤ w := by
        have h := hsmall.2
        dsimp [S, inserted] at h
        rw [supportMarkSecondNormalizedSum_insert_two
          hpq hpA hqA] at h
        simpa only [sub_neg_eq_add] using h
      rw [if_pos
        ⟨hpEligible, hqEligible, hfirst, hsecond⟩]
      norm_num
    · rw [if_neg hE]
      split_ifs
      · simp only [mul_zero]
        positivity
      · norm_num
  by_cases hstruct :
      RankTwoBackgroundStructural T A i j v z m
  · rw [if_pos hstruct]
    exact hleAsym.trans
      (rankTwoAsymBackgroundPairMass_le_mul_window
        A eligibleP eligibleQ v z m hstruct.2.1
        hw hLP hwindowP hwindowQ)
  · rw [if_neg hstruct]
    have hzero :
        rankTwoCanonicalBackgroundPairMass
            T w depths threshold s i j A v z m = 0 := by
      unfold rankTwoCanonicalBackgroundPairMass
      apply Finset.sum_eq_zero
      intro pq hpqMem
      have hpqData := mem_orderedDistinctPairs.mp hpqMem
      have hpA :
          pq.1 ∉ A :=
        (Finset.mem_sdiff.mp hpqData.1).2
      have hqA :
          pq.2 ∉ A :=
        (Finset.mem_sdiff.mp hpqData.2.1).2
      have hpq : pq.1 ≠ pq.2 := hpqData.2.2
      unfold rankTwoCanonicalBackgroundIndicator
      rw [dif_pos ⟨hpq, hpA, hqA⟩, if_neg]
      · ring
      · intro hE
        apply hstruct
        unfold RankTwoBackgroundStructural
        have hbackground :=
          canonicalSupportMarkRankTwoPair_insert_background
            hpq hpA hqA v z m hE.2
        exact
          ⟨hbackground.1, hbackground.2.1,
            hbackground.2.2.2.2.1,
            hbackground.2.2.2.2.2⟩
    rw [hzero]

/-- Sum a constant over a decidable finite subtype. -/
theorem fintype_sum_ite_eq_card_subtype_mul
    {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] (C : ℝ) :
    (∑ a : α, if P a then C else 0) =
      (Fintype.card {a : α // P a} : ℝ) * C := by
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype]

/-- Exact number of structurally compatible triples, expressed through
the already-counted rank-two mark-data type. -/
theorem sum_rankTwoStructuralPairBound_eq
    {R : Finset ℕ} {T LP LQ : ℝ}
    (A : Finset ↥R) {i j K : ℕ}
    (hij : i < j) (hjK : j < K)
    (hK : K ≤ A.card + 2) :
    (∑ v : NineMark, ∑ z : NineMark,
      ∑ m : SupportNineMarking A,
        rankTwoStructuralPairBound
          T A i j v z m LP LQ) =
      (Fintype.card
        (TruncatedTwoPivotMarkData A i j) : ℝ) *
          (LP * LQ) := by
  classical
  let residualCount : ℕ :=
    3 ^ (j - 1 - i) * 9 ^ (A.card - (j - 1))
  have hm (v : NineMark) (hv : v ≠ zeroNineMark)
      (z : NineMark) (hz : ¬NineMarkCollinear v z) :
      (∑ m : SupportNineMarking A,
        rankTwoStructuralPairBound
          T A i j v z m LP LQ) =
        (residualCount : ℝ) * (LP * LQ) := by
    unfold rankTwoStructuralPairBound
    rw [fintype_sum_ite_eq_card_subtype_mul]
    rw [Fintype.card_congr
      (rankTwoBackgroundStructuralMarkingEquiv hv hz)]
    rw [card_truncatedTwoPivotResidualMarking
      hij hjK hK v hv]
  calc
    (∑ v : NineMark, ∑ z : NineMark,
        ∑ m : SupportNineMarking A,
          rankTwoStructuralPairBound
            T A i j v z m LP LQ) =
      ∑ v : NineMark,
        if v ≠ zeroNineMark then
          ∑ z : NineMark,
            if ¬NineMarkCollinear v z then
              (residualCount : ℝ) * (LP * LQ)
            else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hv : v ≠ zeroNineMark
      · rw [if_pos hv]
        apply Finset.sum_congr rfl
        intro z _hz
        by_cases hz : ¬NineMarkCollinear v z
        · rw [if_pos hz, hm v hv z hz]
        · rw [if_neg hz]
          unfold rankTwoStructuralPairBound
            RankTwoBackgroundStructural
          simp [hz]
      · rw [if_neg hv]
        apply Finset.sum_eq_zero
        intro z _hz
        apply Finset.sum_eq_zero
        intro m _hm
        unfold rankTwoStructuralPairBound
          RankTwoBackgroundStructural
        simp [hv]
    _ = ∑ v : NineMark,
        if v ≠ zeroNineMark then
          (6 : ℝ) *
            ((residualCount : ℝ) * (LP * LQ))
        else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hv : v ≠ zeroNineMark
      · rw [if_pos hv, if_pos hv,
          fintype_sum_ite_eq_card_subtype_mul,
          card_nineMarkNoncollinear v hv]
        norm_num
      · rw [if_neg hv, if_neg hv]
    _ = (8 : ℝ) *
        ((6 : ℝ) *
          ((residualCount : ℝ) * (LP * LQ))) := by
      rw [fintype_sum_ite_eq_card_subtype_mul,
        card_nonzeroNineMark]
      norm_num
    _ = (Fintype.card
          (TruncatedTwoPivotMarkData A i j) : ℝ) *
            (LP * LQ) := by
      rw [card_truncatedTwoPivotMarkData]
      dsimp [residualCount]
      norm_num only [Nat.cast_mul, Nat.cast_pow,
        Nat.cast_ofNat]
      ring

/-- Normalizing the preceding structural sum by the full `9`-marking
mass gives the exact pair of canonical rank decays. -/
theorem normalized_sum_rankTwoStructuralPairBound_eq
    {R : Finset ℕ} {T LP LQ : ℝ}
    (A : Finset ↥R) {i j K : ℕ}
    (hij : i < j) (hjK : j < K)
    (hK : K ≤ A.card + 2) :
    (1 / 9 : ℝ) ^ (A.card + 2) *
        (∑ v : NineMark, ∑ z : NineMark,
          ∑ m : SupportNineMarking A,
            rankTwoStructuralPairBound
              T A i j v z m LP LQ) =
      (16 * pivotRankDecay i * pivotRankDecay j) *
        (LP * LQ) := by
  rw [sum_rankTwoStructuralPairBound_eq
    A hij hjK hK]
  have hnormalized :=
    truncatedTwoPivotMarkData_normalized
      A hij hjK hK
  calc
    (1 / 9 : ℝ) ^ (A.card + 2) *
          ((Fintype.card
              (TruncatedTwoPivotMarkData A i j) : ℝ) *
            (LP * LQ)) =
        ((Fintype.card
            (TruncatedTwoPivotMarkData A i j) : ℝ) /
          (9 : ℝ) ^ (A.card + 2)) *
            (LP * LQ) := by
      rw [one_div_pow]
      ring
    _ = (16 * pivotRankDecay i *
          pivotRankDecay j) * (LP * LQ) := by
      rw [hnormalized]

/-- If root-good forces at least `K` support points, a background too
small to accommodate those points has zero canonical inserted-pair
mass. -/
theorem rankTwoCanonicalBackgroundPairMass_eq_zero_of_card_lt
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {i j K : ℕ} (A : Finset ↥R)
    (v z : NineMark) (m : SupportNineMarking A)
    (hK : ¬K ≤ A.card + 2)
    (hcard :
      ∀ (S : Finset ↥R) (M : SupportNineMarking S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S M,
              supportMarkRootSecond s S M) →
          K ≤ S.card) :
    rankTwoCanonicalBackgroundPairMass
        T w depths threshold s i j A v z m = 0 := by
  classical
  unfold rankTwoCanonicalBackgroundPairMass
  apply Finset.sum_eq_zero
  intro pq hpqMem
  have hpqData := mem_orderedDistinctPairs.mp hpqMem
  have hpA :
      pq.1 ∉ A :=
    (Finset.mem_sdiff.mp hpqData.1).2
  have hqA :
      pq.2 ∉ A :=
    (Finset.mem_sdiff.mp hpqData.2.1).2
  have hpq : pq.1 ≠ pq.2 := hpqData.2.2
  unfold rankTwoCanonicalBackgroundIndicator
  rw [dif_pos ⟨hpq, hpA, hqA⟩, if_neg]
  · ring
  · intro hE
    apply hK
    have hlarge :=
      hcard
        (insert pq.1 (insert pq.2 A))
        (insertTwoSupportMarking hpq hpA hqA v z m)
        hE.1
    simpa [hpq, hpA, hqA] using hlarge

/-- Generic fixed-rank annealed rank-two estimate.  The only
profile-specific inputs are the two eligibility implications and their
uniform reciprocal-window bounds. -/
theorem annealedPrimeBandRootGoodRankTwoMass_le_decay_mul_windows
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {T w LP LQ : ℝ}
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) {i j K : ℕ}
    (hij : i < j) (hjK : j < K)
    (hw : 0 ≤ w) (hLP : 0 ≤ LP) (hLQ : 0 ≤ LQ)
    (eligibleP eligibleQ : ↥R → Prop)
    [DecidablePred eligibleP] [DecidablePred eligibleQ]
    (hcard :
      ∀ (S : Finset ↥R) (M : SupportNineMarking S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S M,
              supportMarkRootSecond s S M) →
          K ≤ S.card)
    (hEligibleP :
      ∀ (S : Finset ↥R) (M : SupportNineMarking S)
          (p : ↥R) (_hp : p ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S M,
              supportMarkRootSecond s S M) →
          supportDepthRank T S p = i →
          eligibleP p)
    (hEligibleQ :
      ∀ (S : Finset ↥R) (M : SupportNineMarking S)
          (q : ↥R) (_hq : q ∈ S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S M,
              supportMarkRootSecond s S M) →
          supportDepthRank T S q = j →
          eligibleQ q)
    (hwindowP : ∀ x : ℝ,
      reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleP x (4 * w) ≤ LP)
    (hwindowQ : ∀ x : ℝ,
      reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight T p.1)
        eligibleQ x (4 * w) ≤ LQ) :
    annealedPrimeBandRootGoodRankTwoMass
        R T w depths threshold s i j ≤
      (16 * pivotRankDecay i * pivotRankDecay j) *
        (LP * LQ) := by
  classical
  let C :=
    (16 * pivotRankDecay i * pivotRankDecay j) *
      (LP * LQ)
  have hC : 0 ≤ C := by
    dsimp [C]
    have hdecayI : 0 ≤ pivotRankDecay i := by
      unfold pivotRankDecay
      positivity
    have hdecayJ : 0 ≤ pivotRankDecay j := by
      unfold pivotRankDecay
      positivity
    positivity
  calc
    annealedPrimeBandRootGoodRankTwoMass
        R T w depths threshold s i j ≤
      annealedPrimeBandRootGoodRankTwoPairSum
        R T w depths threshold s i j :=
      annealedPrimeBandRootGoodRankTwoMass_le_pairSum
        R T w depths threshold s i j
    _ = ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
            (1 / (pq.1.1 : ℝ)) *
              (1 / (pq.2.1 : ℝ)) *
              primeBandRootGoodRankTwoPairIndicator
                R T w depths threshold s i j
                (insert pq.1 (insert pq.2 A))
                pq.1 pq.2 := by
      unfold annealedPrimeBandRootGoodRankTwoPairSum
      exact annealedOrderedPairSum_eq_insertions hR
        (primeBandRootGoodRankTwoPairIndicator
          R T w depths threshold s i j)
    _ = ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ((1 / 9 : ℝ) ^ (A.card + 2) *
            ∑ v : NineMark, ∑ z : NineMark,
              ∑ m : SupportNineMarking A,
                rankTwoCanonicalBackgroundPairMass
                  T w depths threshold s i j
                  A v z m) := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [insertedRankTwoPairSum_eq_background]
    _ ≤ ∑ _A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli _A *
          C := by
      apply Finset.sum_le_sum
      intro A _hA
      apply mul_le_mul_of_nonneg_left
      · by_cases hKA : K ≤ A.card + 2
        · calc
            (1 / 9 : ℝ) ^ (A.card + 2) *
                  (∑ v : NineMark, ∑ z : NineMark,
                    ∑ m : SupportNineMarking A,
                      rankTwoCanonicalBackgroundPairMass
                        T w depths threshold s i j
                        A v z m) ≤
                (1 / 9 : ℝ) ^ (A.card + 2) *
                  (∑ v : NineMark, ∑ z : NineMark,
                    ∑ m : SupportNineMarking A,
                      rankTwoStructuralPairBound
                        T A i j v z m LP LQ) := by
              apply mul_le_mul_of_nonneg_left
              · apply Finset.sum_le_sum
                intro v _hv
                apply Finset.sum_le_sum
                intro z _hz
                apply Finset.sum_le_sum
                intro m _hm
                exact rankTwoCanonicalBackgroundPairMass_le
                  A eligibleP eligibleQ v z m
                  hw hLP hEligibleP hEligibleQ
                  hwindowP hwindowQ
              · positivity
            _ = C := by
              dsimp [C]
              exact normalized_sum_rankTwoStructuralPairBound_eq
                A hij hjK hKA
        · have hzero (v z : NineMark)
              (m : SupportNineMarking A) :
              rankTwoCanonicalBackgroundPairMass
                  T w depths threshold s i j A v z m = 0 :=
            rankTwoCanonicalBackgroundPairMass_eq_zero_of_card_lt
              A v z m hKA hcard
          have hsumZero :
              (∑ v : NineMark, ∑ z : NineMark,
                ∑ m : SupportNineMarking A,
                  rankTwoCanonicalBackgroundPairMass
                    T w depths threshold s i j
                    A v z m) = 0 := by
            apply Finset.sum_eq_zero
            intro v _hv
            apply Finset.sum_eq_zero
            intro z _hz
            apply Finset.sum_eq_zero
            intro m _hm
            exact hzero v z m
          rw [hsumZero, mul_zero]
          exact hC
      · apply subtypeBernoulliWeight_nonneg
        · intro p _hp
          exact reciprocalBernoulli_nonneg p
        · intro p _hp
          rw [reciprocalBernoulli]
          apply (div_le_one (by positivity)).mpr
          have hpNonneg : (0 : ℝ) ≤ p := by
            positivity
          linarith
    _ = C := by
      rw [← Finset.sum_mul,
        sum_subtypeBernoulliWeight, one_mul]
    _ = (16 * pivotRankDecay i * pivotRankDecay j) *
        (LP * LQ) := by
      rfl

end Erdos536
