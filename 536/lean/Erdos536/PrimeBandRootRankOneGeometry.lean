import Erdos536.PrimeBandRootRankTwo

/-!
# Rank-one nine-mark geometry

This file records only cutoff-independent finite geometry and marking
counts.  A final prime-band estimate must apply these lemmas rank by rank;
using one moving endpoint for both decay and a local-window bound is not
uniform at quadratic scale.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

def EligibleSupportMarkRankZero
    {R : Finset ℕ} (T d : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) : Prop :=
  ∀ p : ↥S, normalizedLogDepth T p.1.1 ≤ d →
    m p = zeroNineMark

def EligibleSupportMarkRankOne
    {R : Finset ℕ} (T d : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) : Prop :=
  ¬EligibleSupportMarkRankTwo T d S m ∧
    ∃ p : ↥S, normalizedLogDepth T p.1.1 ≤ d ∧
      m p ≠ zeroNineMark

theorem eligibleSupportMark_rank_trichotomy
    {R : Finset ℕ} (T d : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) :
    EligibleSupportMarkRankTwo T d S m ∨
      EligibleSupportMarkRankOne T d S m ∨
      EligibleSupportMarkRankZero T d S m := by
  classical
  by_cases htwo : EligibleSupportMarkRankTwo T d S m
  · exact Or.inl htwo
  · by_cases hzero : EligibleSupportMarkRankZero T d S m
    · exact Or.inr (Or.inr hzero)
    · apply Or.inr
      apply Or.inl
      refine ⟨htwo, ?_⟩
      unfold EligibleSupportMarkRankZero at hzero
      push_neg at hzero
      exact hzero

theorem eligibleRankOne_collinear
    {R : Finset ℕ} {T d : ℝ}
    {S : Finset ↥R} {m : SupportNineMarking S}
    (hone : EligibleSupportMarkRankOne T d S m)
    {p q : ↥S}
    (hp : normalizedLogDepth T p.1.1 ≤ d)
    (hq : normalizedLogDepth T q.1.1 ≤ d) :
    NineMarkCollinear (m p) (m q) := by
  by_cases hpq : p.1 = q.1
  · have hpqSubtype : p = q := Subtype.ext hpq
    subst q
    unfold NineMarkCollinear nineMarkDet
    ring
  · apply Classical.not_not.mp
    intro hnon
    apply hone.1
    refine ⟨(p.1, q.1), ?_, hp, hq, ?_⟩
    · apply mem_orderedDistinctPairs.mpr
      exact ⟨p.2, q.2, hpq⟩
    · simpa [supportMarkAt, p.2, q.2] using hnon

theorem nonzero_onePivot_forces_interval
    {v : NineMark} (hv : v ≠ zeroNineMark)
    {x z₁ z₂ w : ℝ}
    (hfirst :
      |signedDigitReal v.1 * x - z₁| ≤ w)
    (hsecond :
      |signedDigitReal v.2 * x - z₂| ≤ w) :
    ∃ a : ℝ, a ≤ x ∧ x ≤ a + 2 * w := by
  rcases v with ⟨v₁, v₂⟩
  fin_cases v₁ <;> fin_cases v₂ <;>
    simp [zeroNineMark, signedDigitReal,
      signedDigitValue] at hv hfirst hsecond ⊢
  · exact ⟨-z₁ - w, by
      rw [abs_le] at hfirst
      linarith, by
      rw [abs_le] at hfirst
      linarith⟩
  · exact ⟨-z₁ - w, by
      rw [abs_le] at hfirst
      linarith, by
      rw [abs_le] at hfirst
      linarith⟩
  · exact ⟨-z₁ - w, by
      rw [abs_le] at hfirst
      linarith, by
      rw [abs_le] at hfirst
      linarith⟩
  · exact ⟨-z₂ - w, by
      rw [abs_le] at hsecond
      linarith, by
      rw [abs_le] at hsecond
      linarith⟩
  · exact ⟨z₂ - w, by
      rw [abs_le] at hsecond
      linarith, by
      rw [abs_le] at hsecond
      linarith⟩
  · exact ⟨z₁ - w, by
      rw [abs_le] at hfirst
      linarith, by
      rw [abs_le] at hfirst
      linarith⟩
  · exact ⟨z₁ - w, by
      rw [abs_le] at hfirst
      linarith, by
      rw [abs_le] at hfirst
      linarith⟩
  · exact ⟨z₁ - w, by
      rw [abs_le] at hfirst
      linarith, by
      rw [abs_le] at hfirst
      linarith⟩

noncomputable def eligibleSupportCard
    {R : Finset ℕ} (T d : ℝ)
    (S : Finset ↥R) : ℕ :=
  (S.filter fun p =>
    normalizedLogDepth T p.1 ≤ d).card

abbrev EligibleCollinearSupportMarking
    {R : Finset ℕ} (T d : ℝ)
    (A : Finset ↥R) (v : NineMark) :=
  {m : SupportNineMarking A //
    ∀ q : ↥A, normalizedLogDepth T q.1.1 ≤ d →
      NineMarkCollinear v (m q)}

noncomputable def eligibleCollinearSupportMarkingEquiv
    {R : Finset ℕ} (T d : ℝ)
    (A : Finset ↥R) (v : NineMark) :
    EligibleCollinearSupportMarking T d A v ≃
      ({q : ↥A //
          normalizedLogDepth T q.1.1 ≤ d} →
        {z : NineMark // NineMarkCollinear v z}) ×
      ({q : ↥A //
          ¬normalizedLogDepth T q.1.1 ≤ d} →
        NineMark) where
  toFun m :=
    (fun q => ⟨m.1 q.1, m.2 q.1 q.2⟩,
      fun q => m.1 q.1)
  invFun data :=
    ⟨fun q =>
      if hq : normalizedLogDepth T q.1.1 ≤ d
      then (data.1 ⟨q, hq⟩).1
      else data.2 ⟨q, hq⟩,
    by
      intro q hq
      dsimp
      rw [dif_pos hq]
      exact (data.1 ⟨q, hq⟩).2⟩
  left_inv m := by
    apply Subtype.ext
    funext q
    by_cases hq : normalizedLogDepth T q.1.1 ≤ d
    · simp [hq]
    · simp [hq]
  right_inv data := by
    apply Prod.ext
    · funext q
      apply Subtype.ext
      dsimp
      rw [dif_pos q.2]
    · funext q
      dsimp
      rw [dif_neg q.2]

theorem card_eligibleDepthSubtype
    {R : Finset ℕ} (T d : ℝ)
    (A : Finset ↥R) :
    Fintype.card
        {q : ↥A //
          normalizedLogDepth T q.1.1 ≤ d} =
      eligibleSupportCard T d A := by
  classical
  let e :
      {q : ↥A //
        normalizedLogDepth T q.1.1 ≤ d} ≃
      ↥(A.filter fun p =>
        normalizedLogDepth T p.1 ≤ d) := {
    toFun := fun q =>
      ⟨q.1.1, Finset.mem_filter.mpr
        ⟨q.1.2, q.2⟩⟩
    invFun := fun q =>
      ⟨⟨q.1, (Finset.mem_filter.mp q.2).1⟩,
        (Finset.mem_filter.mp q.2).2⟩
    left_inv := fun q => by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := fun q => by
      apply Subtype.ext
      rfl }
  rw [Fintype.card_congr e, Fintype.card_coe]
  rfl

theorem card_eligibleCollinearSupportMarking
    {R : Finset ℕ} (T d : ℝ)
    (A : Finset ↥R) (v : NineMark)
    (hv : v ≠ zeroNineMark) :
    Fintype.card
        (EligibleCollinearSupportMarking T d A v) =
      3 ^ eligibleSupportCard T d A *
        9 ^ (A.card - eligibleSupportCard T d A) := by
  classical
  rw [Fintype.card_congr
    (eligibleCollinearSupportMarkingEquiv T d A v),
    Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fun, card_nineMarkCollinear v hv,
    card_eligibleDepthSubtype]
  have hcardA :
      Fintype.card ↥A = A.card := Fintype.card_coe A
  rw [Fintype.card_subtype_compl, hcardA,
    card_eligibleDepthSubtype]
  norm_num

end Erdos536
