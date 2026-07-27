import Erdos536.PrimeBandRootRankCombinatorics

/-!
# Annealed canonical-rank mass decomposition

This module performs factorial deletion at the canonical support pivots.
The Bernoulli support law is retained until after deletion, so every
inserted prime contributes its exact reciprocal odds.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-- Two-point factorial insertion under the annealed reciprocal
Bernoulli support law, for an arbitrary ordered-pair integrand. -/
theorem annealedOrderedPairSum_eq_insertions
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (F : Finset ↥R → ↥R → ↥R → ℝ) :
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ pq ∈ orderedDistinctPairs S,
            F S pq.1 pq.2) =
      ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ∑ pq ∈ orderedDistinctPairs (Finset.univ \ A),
            (1 / (pq.1.1 : ℝ)) *
              (1 / (pq.2.1 : ℝ)) *
              F (insert pq.1 (insert pq.2 A))
                pq.1 pq.2 := by
  classical
  have hpow :
      (Finset.univ : Finset (Finset ↥R)) =
        (Finset.univ : Finset ↥R).powerset := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_powerset, true_iff]
    exact Finset.subset_univ S
  calc
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ pq ∈ orderedDistinctPairs S,
            F S pq.1 pq.2) =
        ∑ S ∈ (Finset.univ : Finset ↥R).powerset,
          ∑ pq ∈ orderedDistinctPairs S,
            subsetWeight Finset.univ
                (fun p : ↥R => reciprocalBernoulli p.1) S *
              F S pq.1 pq.2 := by
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
              F (insert pq.1 (insert pq.2 A))
                pq.1 pq.2 := by
      exact factorialInsertion_two_odds
        Finset.univ
        (fun p : ↥R => reciprocalBernoulli p.1)
        F
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
                F (insert pq.1 (insert pq.2 A))
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

/-- One-point version of `annealedOrderedPairSum_eq_insertions`. -/
theorem annealedPointSum_eq_insertions
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (F : Finset ↥R → ↥R → ℝ) :
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ p ∈ S, F S p) =
      ∑ A : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli A *
          ∑ p ∈ Finset.univ \ A,
            (1 / (p.1 : ℝ)) * F (insert p A) p := by
  classical
  have hpow :
      (Finset.univ : Finset (Finset ↥R)) =
        (Finset.univ : Finset ↥R).powerset := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_powerset, true_iff]
    exact Finset.subset_univ S
  calc
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ p ∈ S, F S p) =
        ∑ S ∈ (Finset.univ : Finset ↥R).powerset,
          ∑ p ∈ S,
            subsetWeight Finset.univ
                (fun q : ↥R => reciprocalBernoulli q.1) S *
              F S p := by
      rw [← hpow]
      simp [subtypeBernoulliWeight_eq_subsetWeight,
        Finset.mul_sum]
    _ = ∑ A ∈ (Finset.univ : Finset ↥R).powerset,
          ∑ p ∈ Finset.univ \ A,
            subsetWeight Finset.univ
                (fun q : ↥R => reciprocalBernoulli q.1) A *
              (reciprocalBernoulli p.1 /
                (1 - reciprocalBernoulli p.1)) *
              F (insert p A) p := by
      exact factorialInsertion_one_odds
        Finset.univ
        (fun p : ↥R => reciprocalBernoulli p.1)
        F
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
            ∑ p ∈ Finset.univ \ A,
              (1 / (p.1 : ℝ)) * F (insert p A) p := by
      rw [← hpow]
      simp only [subtypeBernoulliWeight_eq_subsetWeight]
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos := (hR p.1 p.2).pos
      rw [reciprocalBernoulli_odds_eq_reciprocal hpPos]
      ring

/-- Background markings with a forced-zero initial block and a larger
forced-collinear block.  The two blocks will be the canonical rank
prefixes left after deleting the pivots. -/
abbrev ZeroCollinearBackgroundMarking
    {α : Type*} [Fintype α] [DecidableEq α]
    (B C : Finset α) (v : NineMark) :=
  {m : α → NineMark //
    (∀ r ∈ B, m r = zeroNineMark) ∧
      ∀ r ∈ C, NineMarkCollinear v (m r)}

@[simp]
theorem nineMarkCollinear_zero_right (v : NineMark) :
    NineMarkCollinear v zeroNineMark := by
  rcases v with ⟨v₁, v₂⟩
  norm_num [NineMarkCollinear, nineMarkDet,
    zeroNineMark, signedDigitValue]

/-- Split an admissible background marking into the collinear middle
block and the unrestricted tail; the forced-zero block has no data. -/
noncomputable def zeroCollinearBackgroundMarkingEquiv
    {α : Type*} [Fintype α] [DecidableEq α]
    (B C : Finset α) (hBC : B ⊆ C) (v : NineMark) :
    ZeroCollinearBackgroundMarking B C v ≃
      ({r : α // r ∈ C \ B} →
        {z : NineMark // NineMarkCollinear v z}) ×
      ({r : α // r ∉ C} → NineMark) where
  toFun m :=
    (fun r => ⟨m.1 r.1, m.2.2 r.1
      (Finset.mem_sdiff.mp r.2).1⟩,
    fun r => m.1 r.1)
  invFun data :=
    ⟨fun r =>
      if hrB : r ∈ B then zeroNineMark
      else if hrC : r ∈ C
      then (data.1 ⟨r, Finset.mem_sdiff.mpr
        ⟨hrC, hrB⟩⟩).1
      else data.2 ⟨r, hrC⟩,
    by
      constructor
      · intro r hrB
        dsimp
        simp [hrB]
      · intro r hrC
        dsimp
        by_cases hrB : r ∈ B
        · simp [hrB]
        · simp [hrB, hrC]
          exact (data.1 ⟨r, Finset.mem_sdiff.mpr
            ⟨hrC, hrB⟩⟩).2⟩
  left_inv m := by
    apply Subtype.ext
    funext r
    by_cases hrB : r ∈ B
    · simp [hrB, m.2.1 r hrB]
    · by_cases hrC : r ∈ C
      · simp [hrB, hrC]
      · simp [hrB, hrC]
  right_inv data := by
    apply Prod.ext
    · funext r
      apply Subtype.ext
      have hr := Finset.mem_sdiff.mp r.2
      simp [hr.1, hr.2]
    · funext r
      have hrB : r.1 ∉ B := fun hr =>
        r.2 (hBC hr)
      simp [r.2, hrB]

/-- Exact independent-coordinate count for a zero/collinear/background
three-block marking. -/
theorem card_zeroCollinearBackgroundMarking
    {α : Type*} [Fintype α] [DecidableEq α]
    (B C : Finset α) (hBC : B ⊆ C)
    (v : NineMark) (hv : v ≠ zeroNineMark) :
    Fintype.card (ZeroCollinearBackgroundMarking B C v) =
      3 ^ (C.card - B.card) *
        9 ^ (Fintype.card α - C.card) := by
  classical
  rw [Fintype.card_congr
    (zeroCollinearBackgroundMarkingEquiv B C hBC v),
    Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fun, card_nineMarkCollinear v hv]
  have hdiff :
      Fintype.card {r : α // r ∈ C \ B} =
        C.card - B.card := by
    rw [Fintype.card_coe]
    exact Finset.card_sdiff_of_subset hBC
  have hcompl :
      Fintype.card {r : α // r ∉ C} =
        Fintype.card α - C.card := by
    have hmem :
        Fintype.card {r : α // r ∈ C} = C.card := by
      rw [Fintype.card_coe]
    rw [Fintype.card_subtype_compl, hmem]
  rw [hdiff, hcompl]
  norm_num

/-- Annealed mass of the actual root-good support markings. -/
noncomputable def annealedPrimeBandRootGoodMarkMass
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S,
          if PrimeBandRootGood R T w depths threshold s
              (S, supportMarkRootFirst s S m,
                supportMarkRootSecond s S m)
          then (1 / 9 : ℝ) ^ S.card else 0

/-- The observation-level root-good mass is exactly the annealed
nine-mark mass. -/
theorem primeBandRootGoodMass_eq_annealedMarkMass
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)] :
    (∑ o : FiveRootObservation R,
      if PrimeBandRootGood R T w depths threshold s o
      then
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o (fun _ => True)
      else 0) =
      annealedPrimeBandRootGoodMarkMass
        R T w depths threshold s := by
  rw [primeBandRootGoodMass_eq_sum_supportColorMass
    hR T w depths threshold s]
  unfold annealedPrimeBandRootGoodMarkMass
  apply Finset.sum_congr rfl
  intro S _hS
  rw [primeBandRootColorMass_eq_sum_supportMarking
    R T w depths threshold s S]
  apply congrArg
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hgood :
      PrimeBandRootGood R T w depths threshold s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m)
  · simp [hgood]
  · simp [hgood]

/-- Rank-two portion of the actual root-good marked mass. -/
noncomputable def annealedPrimeBandRootGoodRankTwoMass
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i j : ℕ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S,
          if PrimeBandRootGood R T w depths threshold s
                (S, supportMarkRootFirst s S m,
                  supportMarkRootSecond s S m) ∧
              CanonicalSupportMarkRankTwo T m i j
          then (1 / 9 : ℝ) ^ S.card else 0

/-- Truncated rank-one portion: marks at ranks at least `K` remain
unrestricted. -/
noncomputable def annealedPrimeBandRootGoodRankOneBeforeMass
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i K : ℕ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S,
          if PrimeBandRootGood R T w depths threshold s
                (S, supportMarkRootFirst s S m,
                  supportMarkRootSecond s S m) ∧
              CanonicalSupportMarkRankOneBefore T m i K
          then (1 / 9 : ℝ) ^ S.card else 0

/-- Truncated rank-zero portion: only ranks below `K` are forced to
carry the zero mark. -/
noncomputable def annealedPrimeBandRootGoodRankZeroBeforeMass
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (K : ℕ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S,
          if PrimeBandRootGood R T w depths threshold s
                (S, supportMarkRootFirst s S m,
                  supportMarkRootSecond s S m) ∧
              SupportMarkRankZeroBefore T m K
          then (1 / 9 : ℝ) ^ S.card else 0

/-- Sum over a strict ordered pair of ranks below `K`. -/
def strictRankPairSum (K : ℕ)
    (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range K,
    ∑ j ∈ Finset.range K,
      if i < j then F i j else 0

/-- Sum over one rank below `K`. -/
def rankSum (K : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range K, F i

theorem strictRankPairSum_fintype_sum
    {α : Type*} [Fintype α]
    (K : ℕ) (F : ℕ → ℕ → α → ℝ) :
    strictRankPairSum K
        (fun i j => ∑ a : α, F i j a) =
      ∑ a : α, strictRankPairSum K
        (fun i j => F i j a) := by
  classical
  unfold strictRankPairSum
  calc
    (∑ i ∈ Finset.range K,
        ∑ j ∈ Finset.range K,
          if i < j then ∑ a : α, F i j a else 0) =
        ∑ i ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            ∑ a : α,
              if i < j then F i j a else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hij : i < j <;> simp [hij]
    _ = ∑ i ∈ Finset.range K,
          ∑ a : α,
            ∑ j ∈ Finset.range K,
              if i < j then F i j a else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.sum_comm]
    _ = ∑ a : α,
          ∑ i ∈ Finset.range K,
            ∑ j ∈ Finset.range K,
              if i < j then F i j a else 0 := by
      rw [Finset.sum_comm]

theorem rankSum_fintype_sum
    {α : Type*} [Fintype α]
    (K : ℕ) (F : ℕ → α → ℝ) :
    rankSum K (fun i => ∑ a : α, F i a) =
      ∑ a : α, rankSum K (fun i => F i a) := by
  classical
  unfold rankSum
  rw [Finset.sum_comm]

theorem strictRankPairSum_mul
    (K : ℕ) (a : ℝ) (F : ℕ → ℕ → ℝ) :
    strictRankPairSum K (fun i j => a * F i j) =
      a * strictRankPairSum K F := by
  classical
  unfold strictRankPairSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hij : i < j <;> simp [hij]

theorem rankSum_mul
    (K : ℕ) (a : ℝ) (F : ℕ → ℝ) :
    rankSum K (fun i => a * F i) =
      a * rankSum K F := by
  classical
  unfold rankSum
  rw [Finset.mul_sum]

theorem annealedPrimeBandRootGoodMarkMass_le_rankDecomposition
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (K : ℕ) :
    annealedPrimeBandRootGoodMarkMass
        R T w depths threshold s ≤
      (∑ i ∈ Finset.range K,
        ∑ j ∈ Finset.range K,
          if i < j then
            annealedPrimeBandRootGoodRankTwoMass
              R T w depths threshold s i j
          else 0) +
      (∑ i ∈ Finset.range K,
        annealedPrimeBandRootGoodRankOneBeforeMass
          R T w depths threshold s i K) +
      annealedPrimeBandRootGoodRankZeroBeforeMass
        R T w depths threshold s K := by
  classical
  let rootAtom :=
    fun (S : Finset ↥R) (m : SupportNineMarking S) =>
      if PrimeBandRootGood R T w depths threshold s
          (S, supportMarkRootFirst s S m,
            supportMarkRootSecond s S m)
      then (1 / 9 : ℝ) ^ S.card else 0
  let twoAtom :=
    fun (i j : ℕ) (S : Finset ↥R)
        (m : SupportNineMarking S) =>
      if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) ∧
          CanonicalSupportMarkRankTwo T m i j
      then (1 / 9 : ℝ) ^ S.card else 0
  let oneAtom :=
    fun (i : ℕ) (S : Finset ↥R)
        (m : SupportNineMarking S) =>
      if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) ∧
          CanonicalSupportMarkRankOneBefore T m i K
      then (1 / 9 : ℝ) ^ S.card else 0
  let zeroAtom :=
    fun (S : Finset ↥R) (m : SupportNineMarking S) =>
      if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) ∧
          SupportMarkRankZeroBefore T m K
      then (1 / 9 : ℝ) ^ S.card else 0
  change
    (∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S, rootAtom S m) ≤
      strictRankPairSum K (fun i j =>
        ∑ S : Finset ↥R,
          subtypeBernoulliWeight R reciprocalBernoulli S *
            ∑ m : SupportNineMarking S,
              twoAtom i j S m) +
      rankSum K (fun i =>
        ∑ S : Finset ↥R,
          subtypeBernoulliWeight R reciprocalBernoulli S *
            ∑ m : SupportNineMarking S,
              oneAtom i S m) +
      ∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ m : SupportNineMarking S, zeroAtom S m
  rw [strictRankPairSum_fintype_sum,
    rankSum_fintype_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _hS
  have hsupportWeight :
      0 ≤ subtypeBernoulliWeight R reciprocalBernoulli S := by
    apply subtypeBernoulliWeight_nonneg
    · intro p _hp
      exact reciprocalBernoulli_nonneg p
    · intro p _hp
      rw [reciprocalBernoulli]
      apply (div_le_one (by positivity)).mpr
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith
  rw [strictRankPairSum_mul, rankSum_mul]
  rw [← mul_add, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ hsupportWeight
  rw [strictRankPairSum_fintype_sum,
    rankSum_fintype_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro m _hm
  dsimp only [rootAtom, twoAtom, oneAtom, zeroAtom]
  unfold strictRankPairSum rankSum
  have htwoNonneg :
      0 ≤
        ∑ i ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            if i < j then
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankTwo T m i j
              then (1 / 9 : ℝ) ^ S.card else 0
            else 0 := by
    apply Finset.sum_nonneg
    intro i _hi
    apply Finset.sum_nonneg
    intro j _hj
    split_ifs <;> positivity
  have honeNonneg :
      0 ≤
        ∑ i ∈ Finset.range K,
          if PrimeBandRootGood R T w depths threshold s
                (S, supportMarkRootFirst s S m,
                  supportMarkRootSecond s S m) ∧
              CanonicalSupportMarkRankOneBefore T m i K
          then (1 / 9 : ℝ) ^ S.card else 0 := by
    apply Finset.sum_nonneg
    intro i _hi
    split_ifs <;> positivity
  have hzeroNonneg :
      0 ≤
        if PrimeBandRootGood R T w depths threshold s
              (S, supportMarkRootFirst s S m,
                supportMarkRootSecond s S m) ∧
            SupportMarkRankZeroBefore T m K
        then (1 / 9 : ℝ) ^ S.card else 0 := by
    split_ifs <;> positivity
  by_cases hgood :
      PrimeBandRootGood R T w depths threshold s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m)
  · rw [if_pos hgood]
    rcases supportMark_rank_trichotomy_before m K with
        htwo | hone | hzero
    · obtain ⟨i, j, hij, hjK, hcanonical⟩ := htwo
      have hiK : i < K := hij.trans hjK
      have hiMem : i ∈ Finset.range K :=
        Finset.mem_range.mpr hiK
      have hjMem : j ∈ Finset.range K :=
        Finset.mem_range.mpr hjK
      have hpair :
          (1 / 9 : ℝ) ^ S.card ≤
            ∑ a ∈ Finset.range K,
              ∑ b ∈ Finset.range K,
                if a < b then
                  if PrimeBandRootGood R T w depths threshold s
                        (S, supportMarkRootFirst s S m,
                          supportMarkRootSecond s S m) ∧
                      CanonicalSupportMarkRankTwo T m a b
                  then (1 / 9 : ℝ) ^ S.card else 0
                else 0 := by
        calc
        (1 / 9 : ℝ) ^ S.card =
            (if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankTwo T m i j
              then (1 / 9 : ℝ) ^ S.card else 0) := by
          rw [if_pos ⟨hgood, hcanonical⟩]
        _ ≤
            ∑ b ∈ Finset.range K,
                if i < b then
                  if PrimeBandRootGood R T w depths threshold s
                        (S, supportMarkRootFirst s S m,
                          supportMarkRootSecond s S m) ∧
                      CanonicalSupportMarkRankTwo T m i b
                  then (1 / 9 : ℝ) ^ S.card else 0
                else 0 := by
          have hsingle :=
            Finset.single_le_sum
              (s := Finset.range K)
              (f := fun b =>
                if i < b then
                  if PrimeBandRootGood R T w depths threshold s
                        (S, supportMarkRootFirst s S m,
                          supportMarkRootSecond s S m) ∧
                      CanonicalSupportMarkRankTwo T m i b
                  then (1 / 9 : ℝ) ^ S.card else 0
                else 0)
              (by
                intro b _hb
                dsimp
                split_ifs <;> positivity)
              hjMem
          simpa [hij] using hsingle
        _ ≤ _ := by
          refine Finset.single_le_sum
            (s := Finset.range K)
            (f := fun a =>
              ∑ b ∈ Finset.range K,
                if a < b then
                  if PrimeBandRootGood R T w depths threshold s
                        (S, supportMarkRootFirst s S m,
                          supportMarkRootSecond s S m) ∧
                      CanonicalSupportMarkRankTwo T m a b
                  then (1 / 9 : ℝ) ^ S.card else 0
                else 0) ?_ hiMem
          intro a _ha
          apply Finset.sum_nonneg
          intro b _hb
          split_ifs <;> positivity
      linarith
    · obtain ⟨i, hiK, hcanonical⟩ := hone
      have hiMem : i ∈ Finset.range K :=
        Finset.mem_range.mpr hiK
      have honeTerm :
          (1 / 9 : ℝ) ^ S.card ≤
            ∑ i ∈ Finset.range K,
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankOneBefore T m i K
              then (1 / 9 : ℝ) ^ S.card else 0 := by
        calc
          (1 / 9 : ℝ) ^ S.card =
              (if PrimeBandRootGood R T w depths threshold s
                      (S, supportMarkRootFirst s S m,
                        supportMarkRootSecond s S m) ∧
                    CanonicalSupportMarkRankOneBefore T m i K
                then (1 / 9 : ℝ) ^ S.card else 0) := by
            rw [if_pos ⟨hgood, hcanonical⟩]
          _ ≤ _ := by
            refine Finset.single_le_sum
              (s := Finset.range K)
              (f := fun a =>
                if PrimeBandRootGood R T w depths threshold s
                      (S, supportMarkRootFirst s S m,
                        supportMarkRootSecond s S m) ∧
                    CanonicalSupportMarkRankOneBefore T m a K
                then (1 / 9 : ℝ) ^ S.card else 0) ?_ hiMem
            intro a ha
            dsimp
            split_ifs <;> positivity
      linarith
    · have hzeroTerm :
          (1 / 9 : ℝ) ^ S.card =
            (if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  SupportMarkRankZeroBefore T m K
              then (1 / 9 : ℝ) ^ S.card else 0) := by
        rw [if_pos ⟨hgood, hzero⟩]
      calc
        (1 / 9 : ℝ) ^ S.card =
            (if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  SupportMarkRankZeroBefore T m K
              then (1 / 9 : ℝ) ^ S.card else 0) :=
          hzeroTerm
        _ ≤ _ := by linarith
  · rw [if_neg hgood]
    linarith

/-- Ambient-point form of the canonical two-pivot witness, convenient
for factorial deletion. -/
def CanonicalSupportMarkRankTwoPair
    {R : Finset ℕ} (T : ℝ)
    {S : Finset ↥R} (m : SupportNineMarking S)
    (i j : ℕ) (p q : ↥R) : Prop :=
  ∃ hp : p ∈ S, ∃ hq : q ∈ S,
    supportDepthRank T S p = i ∧
    supportDepthRank T S q = j ∧
    IsFirstNonzeroSupportPivot T m ⟨p, hp⟩ ∧
    IsFirstNoncollinearSupportPivot T m
      ⟨p, hp⟩ ⟨q, hq⟩

noncomputable def primeBandRootGoodRankTwoPairIndicator
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i j : ℕ)
    (S : Finset ↥R) (p q : ↥R) : ℝ := by
  classical
  exact
    ∑ m : SupportNineMarking S,
      if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) ∧
          CanonicalSupportMarkRankTwoPair
            T m i j p q
      then (1 / 9 : ℝ) ^ S.card else 0

noncomputable def annealedPrimeBandRootGoodRankTwoPairSum
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i j : ℕ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ pq ∈ orderedDistinctPairs S,
          primeBandRootGoodRankTwoPairIndicator
            R T w depths threshold s i j
            S pq.1 pq.2

theorem annealedPrimeBandRootGoodRankTwoMass_le_pairSum
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (i j : ℕ) :
    annealedPrimeBandRootGoodRankTwoMass
        R T w depths threshold s i j ≤
      annealedPrimeBandRootGoodRankTwoPairSum
        R T w depths threshold s i j := by
  classical
  unfold annealedPrimeBandRootGoodRankTwoMass
    annealedPrimeBandRootGoodRankTwoPairSum
  apply Finset.sum_le_sum
  intro S _hS
  apply mul_le_mul_of_nonneg_left
  · unfold primeBandRootGoodRankTwoPairIndicator
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro m _hm
    by_cases hE :
        PrimeBandRootGood R T w depths threshold s
              (S, supportMarkRootFirst s S m,
                supportMarkRootSecond s S m) ∧
            CanonicalSupportMarkRankTwo T m i j
    · rw [if_pos hE]
      obtain ⟨p, q, hpRank, hqRank,
        hpFirst, hqFirst⟩ := hE.2
      have hpqNe : p.1 ≠ q.1 := by
        intro hpq
        have hpqSubtype : p = q := Subtype.ext hpq
        subst q
        exact (lt_irrefl (supportDepthKey T p.1))
          hqFirst.1
      have hpqMem :
          (p.1, q.1) ∈ orderedDistinctPairs S := by
        exact mem_orderedDistinctPairs.mpr
          ⟨p.2, q.2, hpqNe⟩
      calc
        (1 / 9 : ℝ) ^ S.card =
            (if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankTwoPair
                    T m i j p.1 q.1
              then (1 / 9 : ℝ) ^ S.card else 0) := by
          rw [if_pos]
          exact ⟨hE.1, p.2, q.2, hpRank,
            hqRank, hpFirst, hqFirst⟩
        _ ≤
            ∑ pq ∈ orderedDistinctPairs S,
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankTwoPair
                    T m i j pq.1 pq.2
              then (1 / 9 : ℝ) ^ S.card else 0 := by
          refine Finset.single_le_sum
            (s := orderedDistinctPairs S)
            (f := fun pq =>
              if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  CanonicalSupportMarkRankTwoPair
                    T m i j pq.1 pq.2
              then (1 / 9 : ℝ) ^ S.card else 0)
            ?_ hpqMem
          intro pq hpq
          dsimp
          split_ifs
          · positivity
          · exact le_rfl
    · rw [if_neg hE]
      apply Finset.sum_nonneg
      intro pq hpq
      split_ifs
      · positivity
      · exact le_rfl
  · apply subtypeBernoulliWeight_nonneg
    · intro p _hp
      exact reciprocalBernoulli_nonneg p
    · intro p _hp
      rw [reciprocalBernoulli]
      apply (div_le_one (by positivity)).mpr
      have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
      linarith

/-- Assemble fixed-rank estimates into the exact three terms expected by
`rootSmallBall_le_explicit_constant`. -/
theorem annealedPrimeBandRootGoodMarkMass_le_rankContributions
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (ell : ℕ → ℝ) (K : ℕ)
    (Ctwo Cone Ezero : ℝ)
    (htwo : ∀ i < K, ∀ j < K, i < j →
      annealedPrimeBandRootGoodRankTwoMass
          R T w depths threshold s i j ≤
        16 * Ctwo * w ^ 2 *
          ((pivotRankDecay i / ell i) *
            (pivotRankDecay j / ell j)))
    (hone : ∀ i < K,
      annealedPrimeBandRootGoodRankOneBeforeMass
          R T w depths threshold s i K ≤
        8 * Cone * w * (1 / 3 : ℝ) ^ K *
          (pivotRankDecay i / ell i))
    (hzero :
      annealedPrimeBandRootGoodRankZeroBeforeMass
          R T w depths threshold s K ≤
        Ezero * w ^ 2) :
    annealedPrimeBandRootGoodMarkMass
        R T w depths threshold s ≤
      twoPivotRankContribution ell K Ctwo w +
        onePivotRankContribution ell K Cone w +
        Ezero * w ^ 2 := by
  calc
    annealedPrimeBandRootGoodMarkMass
          R T w depths threshold s ≤
        (∑ i ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            if i < j then
              annealedPrimeBandRootGoodRankTwoMass
                R T w depths threshold s i j
            else 0) +
        (∑ i ∈ Finset.range K,
          annealedPrimeBandRootGoodRankOneBeforeMass
            R T w depths threshold s i K) +
        annealedPrimeBandRootGoodRankZeroBeforeMass
          R T w depths threshold s K :=
      annealedPrimeBandRootGoodMarkMass_le_rankDecomposition
        R T w depths threshold s K
    _ ≤
        (∑ i ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            if i < j then
              16 * Ctwo * w ^ 2 *
                ((pivotRankDecay i / ell i) *
                  (pivotRankDecay j / ell j))
            else 0) +
        (∑ i ∈ Finset.range K,
          8 * Cone * w * (1 / 3 : ℝ) ^ K *
            (pivotRankDecay i / ell i)) +
        Ezero * w ^ 2 := by
      apply add_le_add
      · apply add_le_add
        · apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          by_cases hij : i < j
          · rw [if_pos hij, if_pos hij]
            exact htwo i (Finset.mem_range.mp hi)
              j (Finset.mem_range.mp hj) hij
          · rw [if_neg hij, if_neg hij]
        · apply Finset.sum_le_sum
          intro i hi
          exact hone i (Finset.mem_range.mp hi)
      · exact hzero
    _ = twoPivotRankContribution ell K Ctwo w +
          onePivotRankContribution ell K Cone w +
          Ezero * w ^ 2 := by
      unfold twoPivotRankContribution
        onePivotRankContribution pivotRankSeries
      congr 2
      rw [Finset.mul_sum]

/-- Observation-level version of the canonical rank-contribution
assembly. -/
theorem primeBandRootGoodMass_le_rankContributions
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (ell : ℕ → ℝ) (K : ℕ)
    (Ctwo Cone Ezero : ℝ)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)]
    (htwo : ∀ i < K, ∀ j < K, i < j →
      annealedPrimeBandRootGoodRankTwoMass
          R T w depths threshold s i j ≤
        16 * Ctwo * w ^ 2 *
          ((pivotRankDecay i / ell i) *
            (pivotRankDecay j / ell j)))
    (hone : ∀ i < K,
      annealedPrimeBandRootGoodRankOneBeforeMass
          R T w depths threshold s i K ≤
        8 * Cone * w * (1 / 3 : ℝ) ^ K *
          (pivotRankDecay i / ell i))
    (hzero :
      annealedPrimeBandRootGoodRankZeroBeforeMass
          R T w depths threshold s K ≤
        Ezero * w ^ 2) :
    (∑ o : FiveRootObservation R,
      if PrimeBandRootGood R T w depths threshold s o
      then
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o (fun _ => True)
      else 0) ≤
      twoPivotRankContribution ell K Ctwo w +
        onePivotRankContribution ell K Cone w +
        Ezero * w ^ 2 := by
  rw [primeBandRootGoodMass_eq_annealedMarkMass
    hR T w depths threshold s]
  exact
    annealedPrimeBandRootGoodMarkMass_le_rankContributions
      R T w depths threshold s ell K
      Ctwo Cone Ezero htwo hone hzero

end Erdos536
