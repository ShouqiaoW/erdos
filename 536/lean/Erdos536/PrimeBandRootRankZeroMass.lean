import Erdos536.PrimeBandRootRankMass
import Erdos536.PrimeBandRootTruncatedMarkCounts

/-!
# Annealed truncated rank-zero mass

The first `K` canonical support ranks must all carry the zero nine-mark.
Their exact uniform marking probability is therefore `9⁻ᴷ`, independently
of the represented support.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-- Prefix-rank-zero markings are exactly the zero-block markings counted
by `TruncatedZeroPrefixMarking`. -/
noncomputable def supportMarkRankZeroBeforeEquiv
    {R : Finset ℕ} (T : ℝ) (S : Finset ↥R) (K : ℕ) :
    {m : SupportNineMarking S //
      SupportMarkRankZeroBefore T m K} ≃
      TruncatedZeroPrefixMarking T S K where
  toFun m :=
    ⟨m.1, by
      intro p hp
      exact m.2 p (mem_supportRankPrefix.mp hp)⟩
  invFun m :=
    ⟨m.1, by
      intro p hp
      exact m.2 p (mem_supportRankPrefix.mpr hp)⟩
  left_inv m := by
    rfl
  right_inv m := by
    rfl

theorem card_supportMarkRankZeroBefore
    {R : Finset ℕ} {T : ℝ} {S : Finset ↥R}
    {K : ℕ} (hK : K ≤ S.card) :
    Fintype.card
        {m : SupportNineMarking S //
          SupportMarkRankZeroBefore T m K} =
      9 ^ (S.card - K) := by
  rw [Fintype.card_congr
    (supportMarkRankZeroBeforeEquiv T S K),
    card_truncatedZeroPrefixMarking hK]

/-- On a fixed represented support, the root-good rank-zero marking
mass is bounded by the exact zero-prefix probability. -/
theorem primeBandRootGoodRankZeroBeforeMarkMass_le
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {S : Finset ↥R} {K : ℕ}
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)]
    [DecidablePred
      (fun m : SupportNineMarking S =>
        SupportMarkRankZeroBefore T m K)]
    (hcard :
      ∀ m : SupportNineMarking S,
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) →
          K ≤ S.card) :
    (∑ m : SupportNineMarking S,
      if PrimeBandRootGood R T w depths threshold s
              (S, supportMarkRootFirst s S m,
                supportMarkRootSecond s S m) ∧
            SupportMarkRankZeroBefore T m K
      then (1 / 9 : ℝ) ^ S.card else 0) ≤
      (1 / 9 : ℝ) ^ K := by
  classical
  by_cases hK : K ≤ S.card
  · calc
      (∑ m : SupportNineMarking S,
          if PrimeBandRootGood R T w depths threshold s
                  (S, supportMarkRootFirst s S m,
                    supportMarkRootSecond s S m) ∧
                SupportMarkRankZeroBefore T m K
          then (1 / 9 : ℝ) ^ S.card else 0) ≤
          ∑ m : SupportNineMarking S,
            if SupportMarkRankZeroBefore T m K
            then (1 / 9 : ℝ) ^ S.card else 0 := by
        apply Finset.sum_le_sum
        intro m _hm
        by_cases hgood :
            PrimeBandRootGood R T w depths threshold s
                (S, supportMarkRootFirst s S m,
                  supportMarkRootSecond s S m)
        · by_cases hzero :
              SupportMarkRankZeroBefore T m K
          · simp [hgood, hzero]
          · simp [hzero]
        · by_cases hzero :
              SupportMarkRankZeroBefore T m K
          · simp [hgood, hzero]
          · simp [hgood, hzero]
      _ =
          (Fintype.card
              {m : SupportNineMarking S //
                SupportMarkRankZeroBefore T m K} : ℝ) *
            (1 / 9 : ℝ) ^ S.card := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Fintype.card_subtype]
      _ =
          (Fintype.card
              (TruncatedZeroPrefixMarking T S K) : ℝ) /
            (9 : ℝ) ^ S.card := by
        rw [Fintype.card_congr
          (supportMarkRankZeroBeforeEquiv T S K),
          one_div_pow]
        ring
      _ = (1 / 9 : ℝ) ^ K :=
        truncatedZeroPrefixMarking_normalized S hK
  · have hsumZero :
        (∑ m : SupportNineMarking S,
          if PrimeBandRootGood R T w depths threshold s
                  (S, supportMarkRootFirst s S m,
                    supportMarkRootSecond s S m) ∧
                SupportMarkRankZeroBefore T m K
          then (1 / 9 : ℝ) ^ S.card else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro m _hm
      rw [if_neg]
      intro h
      exact hK (hcard m h.1)
    rw [hsumZero]
    positivity

/-- Averaging the fixed-support estimate under the reciprocal Bernoulli
support law preserves the bound `9⁻ᴷ`. -/
theorem annealedPrimeBandRootGoodRankZeroBeforeMass_le
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (K : ℕ)
    (hcard :
      ∀ (S : Finset ↥R) (m : SupportNineMarking S),
        PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m) →
          K ≤ S.card) :
    annealedPrimeBandRootGoodRankZeroBeforeMass
        R T w depths threshold s K ≤
      (1 / 9 : ℝ) ^ K := by
  classical
  unfold annealedPrimeBandRootGoodRankZeroBeforeMass
  calc
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          ∑ m : SupportNineMarking S,
            if PrimeBandRootGood R T w depths threshold s
                    (S, supportMarkRootFirst s S m,
                      supportMarkRootSecond s S m) ∧
                  SupportMarkRankZeroBefore T m K
            then (1 / 9 : ℝ) ^ S.card else 0) ≤
        ∑ S : Finset ↥R,
          subtypeBernoulliWeight R reciprocalBernoulli S *
            (1 / 9 : ℝ) ^ K := by
      apply Finset.sum_le_sum
      intro S _hS
      apply mul_le_mul_of_nonneg_left
      · exact primeBandRootGoodRankZeroBeforeMarkMass_le
          (fun m hm => hcard S m hm)
      · apply subtypeBernoulliWeight_nonneg
        · intro p _hp
          exact reciprocalBernoulli_nonneg p
        · intro p hp
          rw [reciprocalBernoulli]
          apply (div_le_one (by positivity)).mpr
          have hpOne : (1 : ℝ) ≤ p := by
            exact_mod_cast (hR p hp).one_le
          linarith
    _ = (1 / 9 : ℝ) ^ K := by
      rw [← Finset.sum_mul,
        sum_subtypeBernoulliWeight, one_mul]

end Erdos536
