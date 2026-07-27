import Erdos536.PrimeBandRootRanks

/-!
# Ordered support weights forced by a delayed root profile

This module turns the three visible-label prefix inequalities in
`PrimeBandRootGood` into the lower bound on every canonical support rank
used by the collision summation.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

open PrimeBandTimeChange

/-- Zero-based rank of `p` among `S`, with larger normalized logarithmic
weights placed first. -/
def supportNormalizedWeightRank
    {R : Finset ℕ} (N : ℝ) (S : Finset ↥R) (p : ↥R) : ℕ :=
  (S.filter fun q ↦
    normalizedLogWeight N p.1 <
      normalizedLogWeight N q.1).card

/-- The represented prefix of a root reconstructed from nine-marks is
exactly the corresponding depth-filtered support. -/
theorem fiveStateDepthPrefix_supportMarkRootFirst_eq
    {R : Finset ℕ} (N : ℝ) (s : Fin 3)
    (S : Finset ↥R) (m : SupportNineMarking S) (d : ℝ) :
    fiveStateDepthPrefix R N s
        (supportMarkRootFirst s S m) d =
      S.filter fun p ↦ normalizedLogDepth N p.1 ≤ d := by
  classical
  ext p
  by_cases hp : p ∈ S
  · simp [fiveStateDepthPrefix, supportMarkRootFirst, hp]
  · simp [fiveStateDepthPrefix, supportMarkRootFirst, hp,
      fiveLabelIncluded]

/-- The analogous identity for the second exposed root. -/
theorem fiveStateDepthPrefix_supportMarkRootSecond_eq
    {R : Finset ℕ} (N : ℝ) (s : Fin 3)
    (S : Finset ↥R) (m : SupportNineMarking S) (d : ℝ) :
    fiveStateDepthPrefix R N s
        (supportMarkRootSecond s S m) d =
      S.filter fun p ↦ normalizedLogDepth N p.1 ≤ d := by
  classical
  ext p
  by_cases hp : p ∈ S
  · simp [fiveStateDepthPrefix, supportMarkRootSecond, hp]
  · simp [fiveStateDepthPrefix, supportMarkRootSecond, hp,
      fiveLabelIncluded]

/-- Three disjoint visible-label lower bounds give the combined
represented-prefix cardinal lower bound. -/
theorem rootVisibleProfile_card_le
    {R : Finset ℕ} {N d : ℝ} {s : Fin 3}
    {c : FiveConfiguration R} {k : ℕ}
    (hprofile :
      ∀ l : ↥(representedActiveLabels s),
        k ≤ fiveLabelPrefixCount R N c l.1 d) :
    3 * k ≤ (fiveStateDepthPrefix R N s c d).card := by
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(representedActiveLabels s) : Set ActiveFiveLabel)
        (fun l ↦ fiveLabelDepthPrefix R N c l d) := by
    intro l _hl q _hq hlq
    exact fiveLabelDepthPrefix_disjoint hlq
  have hsum :
      (∑ l ∈ representedActiveLabels s, k) ≤
        ∑ l ∈ representedActiveLabels s,
          (fiveLabelDepthPrefix R N c l d).card := by
    apply Finset.sum_le_sum
    intro l hl
    exact hprofile ⟨l, hl⟩
  rw [← Finset.card_biUnion hdisjoint,
    ← fiveStateDepthPrefix_eq_biUnion] at hsum
  simpa [card_representedActiveLabels, mul_comm] using hsum

/-- A root-good marked observation has at least three times the requested
threshold many represented support points in every checked prefix. -/
theorem primeBandRootGood_supportPrefix_card
    {R : Finset ℕ} {N w d : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {S : Finset ↥R}
    {m : SupportNineMarking S}
    (hgood :
      PrimeBandRootGood R N w depths threshold s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m))
    (hd : d ∈ depths) :
    3 * threshold d ≤
      (S.filter fun p ↦ normalizedLogDepth N p.1 ≤ d).card := by
  rw [← fiveStateDepthPrefix_supportMarkRootFirst_eq N s S m d]
  apply rootVisibleProfile_card_le
  intro l
  exact hgood.1 l ⟨d, hd⟩

/-- If a support contains more than `i` points above a depth cutoff, then
its zero-based rank-`i` point has normalized weight at least the cutoff
coordinate. -/
theorem normalizedWeight_lower_of_prefix_card_and_rank
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N d : ℝ} (hN : 0 < N)
    {S : Finset ↥R} {p : ↥R} {i : ℕ}
    (hrank : supportNormalizedWeightRank N S p = i)
    (hcard :
      i < (S.filter fun q ↦
        normalizedLogDepth N q.1 ≤ d).card) :
    Real.exp (-d) ≤ normalizedLogWeight N p.1 := by
  by_contra hnot
  have hpLt :
      normalizedLogWeight N p.1 < Real.exp (-d) :=
    lt_of_not_ge hnot
  have hsubset :
      (S.filter fun q ↦ normalizedLogDepth N q.1 ≤ d) ⊆
        S.filter fun q ↦
          normalizedLogWeight N p.1 <
            normalizedLogWeight N q.1 := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨hqData.1, hpLt.trans_le ?_⟩
    apply normalizedLogWeight_lower_of_depth_le
    · unfold normalizedLogWeight
      exact div_pos
        (Real.log_pos (by
          exact_mod_cast (hR q.1 q.2).one_lt))
        hN
    · exact hqData.2
  have hle :=
    Finset.card_le_card hsubset
  change
    (S.filter fun q ↦ normalizedLogDepth N q.1 ≤ d).card ≤
      supportNormalizedWeightRank N S p at hle
  rw [hrank] at hle
  omega

/-- Version of the preceding lemma for the canonical depth-lexicographic
rank used by the rooted-collision decomposition. -/
theorem normalizedWeight_lower_of_prefix_card_and_depthRank
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N d : ℝ} (hN : 0 < N)
    {S : Finset ↥R} {p : ↥R} {i : ℕ}
    (hrank : supportDepthRank N S p = i)
    (hcard :
      i < (S.filter fun q ↦
        normalizedLogDepth N q.1 ≤ d).card) :
    Real.exp (-d) ≤ normalizedLogWeight N p.1 := by
  by_contra hnot
  have hpWeightPos :
      0 < normalizedLogWeight N p.1 := by
    unfold normalizedLogWeight
    exact div_pos
      (Real.log_pos (by
        exact_mod_cast (hR p.1 p.2).one_lt))
      hN
  have hpLt :
      normalizedLogWeight N p.1 < Real.exp (-d) :=
    lt_of_not_ge hnot
  have hlogLt :
      Real.log (normalizedLogWeight N p.1) < -d := by
    have h :=
      Real.log_lt_log hpWeightPos hpLt
    simpa only [Real.log_exp] using h
  have hpDepth :
      d < normalizedLogDepth N p.1 := by
    unfold normalizedLogDepth
    linarith
  have hsubset :
      (S.filter fun q ↦ normalizedLogDepth N q.1 ≤ d) ⊆
        S.filter fun q ↦
          supportDepthKey N q < supportDepthKey N p := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨hqData.1, ?_⟩
    unfold supportDepthKey
    rw [Prod.Lex.toLex_lt_toLex]
    exact Or.inl (hqData.2.trans_lt hpDepth)
  have hle := Finset.card_le_card hsubset
  change
    (S.filter fun q ↦ normalizedLogDepth N q.1 ≤ d).card ≤
      supportDepthRank N S p at hle
  rw [hrank] at hle
  omega

/-- Concrete delayed-profile ordering theorem.  Every rank below the
forced endpoint count has the deterministic lower weight
`quadraticDelayedPivotLower`. -/
theorem quadraticRootGood_rank_weight_lower
    {T H : ℕ} {w : ℝ} (hT : 0 < T)
    (hchecks :
      ∀ k ≤ H,
        k ∈ quadraticDelayedProfileChecks T H)
    {s : Fin 3} {S : Finset ↥(quadraticProfilePrimeBand T)}
    {m : SupportNineMarking S}
    (hgood :
      PrimeBandRootGood
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ) w
        (quadraticDelayedProfileDepths T H)
        quadraticDelayedProfileThresholdAtDepth s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m))
    {p : ↥(quadraticProfilePrimeBand T)}
    {i : ℕ}
    (hrank :
      supportNormalizedWeightRank
        ((T ^ 2 : ℕ) : ℝ) S p = i)
    (hi : i < quadraticDelayedPivotCount H) :
    quadraticDelayedPivotLower i ≤
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 := by
  let k := quadraticDelayedPivotCheck i
  let d := quadraticDelayedProfileDepth k
  have hkH : k ≤ H :=
    quadraticDelayedPivotCheck_le_of_lt_count hi
  have hk : k ∈ quadraticDelayedProfileChecks T H :=
    hchecks k hkH
  have hd :
      d ∈ quadraticDelayedProfileDepths T H := by
    rw [mem_quadraticDelayedProfileDepths]
    exact ⟨k, hk, rfl⟩
  have hprefix :=
    primeBandRootGood_supportPrefix_card hgood hd
  have hforce :
      i <
        3 * quadraticDelayedProfileThresholdAtDepth d := by
    dsimp only [d]
    rw [quadraticDelayedProfileThresholdAtDepth_eq]
    exact quadraticDelayedPivotCheck_forces_rank i
  have hcard :
      i <
        (S.filter fun q ↦
          normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) q.1 ≤ d).card :=
    hforce.trans_le hprefix
  have hN : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    positivity
  simpa only [quadraticDelayedPivotLower, d, k] using
    normalizedWeight_lower_of_prefix_card_and_rank
      (quadraticPrimeBand_prime T 1) hN hrank hcard

/-- The exact collision-facing ordering bridge, stated using
`supportDepthRank`. -/
theorem quadraticRootGood_depthRank_weight_lower
    {T H : ℕ} {w : ℝ} (hT : 0 < T)
    (hchecks :
      ∀ k ≤ H,
        k ∈ quadraticDelayedProfileChecks T H)
    {s : Fin 3} {S : Finset ↥(quadraticProfilePrimeBand T)}
    {m : SupportNineMarking S}
    (hgood :
      PrimeBandRootGood
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ) w
        (quadraticDelayedProfileDepths T H)
        quadraticDelayedProfileThresholdAtDepth s
        (S, supportMarkRootFirst s S m,
          supportMarkRootSecond s S m))
    {p : ↥(quadraticProfilePrimeBand T)}
    {i : ℕ}
    (hrank :
      supportDepthRank ((T ^ 2 : ℕ) : ℝ) S p = i)
    (hi : i < quadraticDelayedPivotCount H) :
    quadraticDelayedPivotLower i ≤
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 := by
  let k := quadraticDelayedPivotCheck i
  let d := quadraticDelayedProfileDepth k
  have hkH : k ≤ H :=
    quadraticDelayedPivotCheck_le_of_lt_count hi
  have hk : k ∈ quadraticDelayedProfileChecks T H :=
    hchecks k hkH
  have hd :
      d ∈ quadraticDelayedProfileDepths T H := by
    rw [mem_quadraticDelayedProfileDepths]
    exact ⟨k, hk, rfl⟩
  have hprefix :=
    primeBandRootGood_supportPrefix_card hgood hd
  have hforce :
      i <
        3 * quadraticDelayedProfileThresholdAtDepth d := by
    dsimp only [d]
    rw [quadraticDelayedProfileThresholdAtDepth_eq]
    exact quadraticDelayedPivotCheck_forces_rank i
  have hcard :
      i <
        (S.filter fun q ↦
          normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) q.1 ≤ d).card :=
    hforce.trans_le hprefix
  have hN : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    positivity
  simpa only [quadraticDelayedPivotLower, d, k] using
    normalizedWeight_lower_of_prefix_card_and_depthRank
      (quadraticPrimeBand_prime T 1) hN hrank hcard

end Erdos536
