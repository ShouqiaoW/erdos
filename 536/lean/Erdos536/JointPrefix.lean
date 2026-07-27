import Erdos536.CubeSaving
import Erdos536.SquarefreeCapacity

/-!
# Finite joint-prefix transference

The moving-prefix argument is entirely finite.  Its canonical cutoff space
is the integer interval from `1` through `primeProduct R`.  The points below
the top carry the exact step weights `1 / n - 1 / (n + 1)`; the top point
carries the remaining tail weight `1 / primeProduct R`.

A finite cube law is compared, word by word, with the resulting joint law on
`(support, cutoff)`.  If every sampled cutoff contains every word of its cube,
then an arbitrary cube-occupancy saving transfers directly to the normalized
squarefree capacity.  This formulation avoids measure theory and is suitable
for laws produced by finite prime-band constructions.
-/

open scoped BigOperators
open Finset Nat

namespace Erdos536

/-- The finite cutoff space, including the point representing the tail. -/
def squarefreeCutoffs (R : Finset ℕ) : Finset ℕ :=
  Icc 1 (primeProduct R)

/-- The mass of a cutoff point.  At the top point this is the entire tail
mass, and at every earlier point it is the reciprocal step mass. -/
noncomputable def squarefreeCutoffWeight (R : Finset ℕ) (n : ℕ) : ℝ :=
  if n = primeProduct R then (primeProduct R : ℝ)⁻¹
  else reciprocalStep n

/-- A fixed choice of a maximum admissible family in each finite prefix. -/
noncomputable def squarefreeExtremizerFamily
    (R : Finset ℕ) (n : ℕ) : Finset (Finset ℕ) :=
  Classical.choose (exists_squarefreeExtremal R n)

theorem squarefreeExtremizerFamily_subset (R : Finset ℕ) (n : ℕ) :
    squarefreeExtremizerFamily R n ⊆ squarefreePrefix R n :=
  (Classical.choose_spec (exists_squarefreeExtremal R n)).1

theorem squarefreeExtremizerFamily_admissible (R : Finset ℕ) (n : ℕ) :
    Admissible (squarefreeExtremizerFamily R n) :=
  (Classical.choose_spec (exists_squarefreeExtremal R n)).2.1

theorem squarefreeExtremizerFamily_card (R : Finset ℕ) (n : ℕ) :
    (squarefreeExtremizerFamily R n).card = squarefreeExtremal R n :=
  (Classical.choose_spec (exists_squarefreeExtremal R n)).2.2

/-- The canonical joint mass of a support and an integer cutoff.  It is
understood that callers sum this over `R.powerset × squarefreeCutoffs R`. -/
noncomputable def canonicalPrefixMass
    (R S : Finset ℕ) (n : ℕ) : ℝ :=
  if S ∈ squarefreePrefix R n then
    squarefreeCutoffWeight R n / squarefreeZ R
  else 0

/-- A genuinely finite probability law on pair-product cubes equipped with a
common integer cutoff. -/
structure FiniteCubeCutoffLaw (α : Type*) [DecidableEq α]
    (H : ℕ) (R : Finset ℕ) where
  samples : Finset α
  mass : α → ℝ
  cube : α → PairProductCube H
  cutoff : α → ℕ
  mass_nonneg : ∀ a ∈ samples, 0 ≤ mass a
  mass_sum : ∑ a ∈ samples, mass a = 1
  cutoff_mem : ∀ a ∈ samples, cutoff a ∈ squarefreeCutoffs R
  word_mem_prefix :
    ∀ a ∈ samples, ∀ ω : Fin H → ZMod 3,
      (cube a).wordSupport ω ∈ squarefreePrefix R (cutoff a)

/-- The `(support, cutoff)` marginal of one word in a finite cube law. -/
noncomputable def FiniteCubeCutoffLaw.wordMarginal
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (ω : Fin H → ZMod 3)
    (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ a ∈ L.samples,
    if (L.cube a).wordSupport ω = S ∧ L.cutoff a = n
    then L.mass a else 0

/-- Exact finite `L¹` distance from the canonical support-prefix law. -/
noncomputable def FiniteCubeCutoffLaw.wordPrefixDistance
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (ω : Fin H → ZMod 3) : ℝ :=
  ∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
    |L.wordMarginal ω S n - canonicalPrefixMass R S n|

private theorem primeProduct_one_le (R : Finset ℕ) (hR : IsPrimeSupport R) :
    1 ≤ primeProduct R := by
  exact primeProduct_pos hR

theorem squarefreeCutoffWeight_nonneg
    (R : Finset ℕ)
    {n : ℕ} (hn : n ∈ squarefreeCutoffs R) :
    0 ≤ squarefreeCutoffWeight R n := by
  rw [squarefreeCutoffWeight]
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact reciprocalStep_nonneg (mem_Icc.mp hn).1

theorem squarefreeExtremizerFamily_subset_powerset
    (R : Finset ℕ) (n : ℕ) :
    squarefreeExtremizerFamily R n ⊆ R.powerset := by
  intro S hS
  exact mem_powerset.mpr
    (mem_squarefreePrefix_iff.mp
      (squarefreeExtremizerFamily_subset R n hS)).1

theorem squarefreePrefix_subset_powerset (R : Finset ℕ) (n : ℕ) :
    squarefreePrefix R n ⊆ R.powerset := by
  intro S hS
  exact mem_powerset.mpr (mem_squarefreePrefix_iff.mp hS).1

/-- The support marginal of the canonical law at one cutoff has the
expected prefix-cardinality mass. -/
theorem canonicalPrefixMass_sum_support (R : Finset ℕ) (n : ℕ) :
    (∑ S ∈ R.powerset, canonicalPrefixMass R S n) =
      ((squarefreePrefix R n).card : ℝ) *
        squarefreeCutoffWeight R n / squarefreeZ R := by
  classical
  simp only [canonicalPrefixMass]
  rw [← Finset.sum_filter,
    Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr (squarefreePrefix_subset_powerset R n)]
  simp [mul_div_assoc]

/-- The canonical finite support-prefix masses sum to one. -/
theorem sum_canonicalPrefixMass
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    (∑ n ∈ squarefreeCutoffs R,
      ∑ S ∈ R.powerset, canonicalPrefixMass R S n) = 1 := by
  classical
  let D := primeProduct R
  have hD : 1 ≤ D := primeProduct_one_le R hR
  rw [squarefreeCutoffs, Finset.Icc_eq_cons_Ico hD, Finset.sum_cons]
  simp_rw [canonicalPrefixMass_sum_support]
  have hsum :
      (∑ n ∈ Ico 1 D,
        ((squarefreePrefix R n).card : ℝ) *
          squarefreeCutoffWeight R n / squarefreeZ R) =
      ∑ n ∈ Ico 1 D,
        ((squarefreePrefix R n).card : ℝ) *
          reciprocalStep n / squarefreeZ R := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnD : n ≠ D := _root_.ne_of_lt (mem_Ico.mp hn).2
    simp [squarefreeCutoffWeight, D, hnD]
  rw [hsum]
  have hZ :
      (∑ n ∈ Ico 1 D,
        ((squarefreePrefix R n).card : ℝ) * reciprocalStep n) +
          ((squarefreePrefix R D).card : ℝ) / (D : ℝ) =
        squarefreeZ R := by
    simpa [D] using prefix_card_step_sum_eq_Z R hR
  rw [← Finset.sum_div]
  rw [squarefreeCutoffWeight, if_pos (show D = primeProduct R from rfl)]
  simp only [div_eq_mul_inv]
  calc
    ((squarefreePrefix R D).card : ℝ) * (D : ℝ)⁻¹ *
          (squarefreeZ R)⁻¹ +
        (∑ n ∈ Ico 1 D,
          ((squarefreePrefix R n).card : ℝ) * reciprocalStep n) *
            (squarefreeZ R)⁻¹ =
        ((∑ n ∈ Ico 1 D,
          ((squarefreePrefix R n).card : ℝ) * reciprocalStep n) +
            ((squarefreePrefix R D).card : ℝ) / (D : ℝ)) /
              squarefreeZ R := by
          rw [div_eq_mul_inv]
          ring
    _ = squarefreeZ R / squarefreeZ R := by rw [hZ]
    _ = 1 := div_self (ne_of_gt (squarefreeZ_pos R hR))

/-- At one fixed cutoff the canonical mass of the chosen extremizer is its
cardinality times the cutoff weight, divided by `Z`. -/
theorem canonicalPrefixMass_extremizer_sum
    (R : Finset ℕ) (n : ℕ) :
    (∑ S ∈ R.powerset,
        if S ∈ squarefreeExtremizerFamily R n
        then canonicalPrefixMass R S n else 0) =
      (squarefreeExtremal R n : ℝ) *
        squarefreeCutoffWeight R n / squarefreeZ R := by
  classical
  let 𝓕 := squarefreeExtremizerFamily R n
  have h𝓕pow : 𝓕 ⊆ R.powerset :=
    squarefreeExtremizerFamily_subset_powerset R n
  have h𝓕pre : 𝓕 ⊆ squarefreePrefix R n :=
    squarefreeExtremizerFamily_subset R n
  calc
    (∑ S ∈ R.powerset,
        if S ∈ 𝓕 then canonicalPrefixMass R S n else 0) =
        ∑ S ∈ 𝓕, canonicalPrefixMass R S n := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.mpr h𝓕pow]
    _ = ∑ _S ∈ 𝓕, squarefreeCutoffWeight R n / squarefreeZ R := by
          apply Finset.sum_congr rfl
          intro S hS
          simp [canonicalPrefixMass, h𝓕pre hS]
    _ = (𝓕.card : ℝ) *
        squarefreeCutoffWeight R n / squarefreeZ R := by
          simp [mul_div_assoc]
    _ = (squarefreeExtremal R n : ℝ) *
        squarefreeCutoffWeight R n / squarefreeZ R := by
          rw [squarefreeExtremizerFamily_card]

/-- Summing the canonical occupancy of the moving extremizer over the finite
cutoff space gives exactly the normalized squarefree capacity. -/
theorem canonicalPrefixMass_extremizer_total
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    (∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
        if S ∈ squarefreeExtremizerFamily R n
        then canonicalPrefixMass R S n else 0) =
      squarefreeI R / squarefreeZ R := by
  classical
  let D := primeProduct R
  have hD : 1 ≤ D := primeProduct_one_le R hR
  rw [squarefreeCutoffs, Finset.Icc_eq_cons_Ico hD, Finset.sum_cons]
  · simp_rw [canonicalPrefixMass_extremizer_sum]
    have hsum :
        (∑ n ∈ Ico 1 D,
          (squarefreeExtremal R n : ℝ) *
            squarefreeCutoffWeight R n / squarefreeZ R) =
        ∑ n ∈ Ico 1 D,
          (squarefreeExtremal R n : ℝ) *
            reciprocalStep n / squarefreeZ R := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnD : n ≠ D := _root_.ne_of_lt (mem_Ico.mp hn).2
      simp [squarefreeCutoffWeight, D, hnD]
    rw [hsum, squarefreeI, add_div]
    simp only [Finset.sum_div]
    simp [squarefreeCutoffWeight, D, div_eq_mul_inv]
    ring

/-- The probability, under one word marginal of `L`, of lying in the
chosen extremizer at the sampled cutoff. -/
noncomputable def FiniteCubeCutoffLaw.wordExtremizerOccupancy
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (ω : Fin H → ZMod 3) : ℝ :=
  ∑ a ∈ L.samples,
    L.mass a *
      if (L.cube a).wordSupport ω ∈
          squarefreeExtremizerFamily R (L.cutoff a)
      then 1 else 0

private theorem sum_pair_delta
    {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (B : Finset β) (C : Finset γ) (b : β) (c : γ)
    (hb : b ∈ B) (hc : c ∈ C) (m : ℝ) (e : β → γ → ℝ) :
    (∑ y ∈ C, ∑ x ∈ B,
        (if b = x ∧ c = y then m else 0) * e x y) =
      m * e b c := by
  rw [Finset.sum_eq_single c]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro x _hx hxb
      rw [if_neg (fun h ↦ hxb h.1.symm)]
      simp
    · exact fun hbB ↦ (hbB hb).elim
  · intro y _hy hyc
    apply Finset.sum_eq_zero
    intro x _hx
    have hcy : ¬c = y := fun h ↦ hyc h.symm
    simp [hcy]
  · exact fun hcC ↦ (hcC hc).elim

/-- Regrouping the sampled law by `(support, cutoff)` recovers the direct
word occupancy. -/
theorem FiniteCubeCutoffLaw.wordExtremizerOccupancy_eq_marginal_sum
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (ω : Fin H → ZMod 3) :
    L.wordExtremizerOccupancy ω =
      ∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
        L.wordMarginal ω S n *
          if S ∈ squarefreeExtremizerFamily R n then 1 else 0 := by
  classical
  rw [FiniteCubeCutoffLaw.wordExtremizerOccupancy]
  simp_rw [FiniteCubeCutoffLaw.wordMarginal, Finset.sum_mul]
  conv_rhs =>
    enter [2, n]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_pair_delta]
  · exact mem_powerset.mpr
      (mem_squarefreePrefix_iff.mp (L.word_mem_prefix a ha ω)).1
  · exact L.cutoff_mem a ha

/-- `L¹` comparison of the word marginal with the canonical law controls
the moving-prefix occupancy event. -/
theorem FiniteCubeCutoffLaw.capacity_le_wordOccupancy_add_distance
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (hR : IsPrimeSupport R)
    (ω : Fin H → ZMod 3) :
    squarefreeI R / squarefreeZ R ≤
      L.wordExtremizerOccupancy ω + L.wordPrefixDistance ω := by
  classical
  rw [← canonicalPrefixMass_extremizer_total R hR,
    L.wordExtremizerOccupancy_eq_marginal_sum,
    FiniteCubeCutoffLaw.wordPrefixDistance]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _hn
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _hS
  by_cases hmem : S ∈ squarefreeExtremizerFamily R n
  · simp only [hmem, if_true, mul_one]
    have habs :=
      neg_le_abs (L.wordMarginal ω S n - canonicalPrefixMass R S n)
    linarith
  · simp [hmem, abs_nonneg]

/-- The words of one sampled cube which fall in a specified family. -/
def FiniteCubeCutoffLaw.occupiedWords
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (a : α)
    (𝓕 : Finset (Finset ℕ)) : Finset (Fin H → ZMod 3) :=
  Finset.univ.filter fun ω => (L.cube a).wordSupport ω ∈ 𝓕

theorem FiniteCubeCutoffLaw.sum_wordExtremizerOccupancy
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) :
    (∑ ω : Fin H → ZMod 3, L.wordExtremizerOccupancy ω) =
      ∑ a ∈ L.samples, L.mass a *
        (L.occupiedWords a
          (squarefreeExtremizerFamily R (L.cutoff a))).card := by
  classical
  simp_rw [FiniteCubeCutoffLaw.wordExtremizerOccupancy]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.mul_sum]
  simp [FiniteCubeCutoffLaw.occupiedWords]

/-- Fully finite joint-prefix transference.

The first hypothesis is an exact finite-sum `L¹` comparison of every word's
joint `(support, cutoff)` marginal with `canonicalPrefixMass`.  The second is
the cube saving, deliberately exposed as an interface: later modules may
instantiate it with a quantitative or qualitative cap-set theorem. -/
theorem finite_jointPrefix_transference
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (hR : IsPrimeSupport R)
    {ε κ : ℝ}
    (hclose : ∀ ω : Fin H → ZMod 3,
      L.wordPrefixDistance ω ≤ ε)
    (hcube : ∀ a ∈ L.samples, ∀ 𝓕 : Finset (Finset ℕ),
      Admissible 𝓕 →
      ((L.occupiedWords a 𝓕).card : ℝ) ≤
        κ * (Fintype.card (Fin H → ZMod 3) : ℝ)) :
    squarefreeI R / squarefreeZ R ≤ κ + ε := by
  classical
  let Q : ℝ := Fintype.card (Fin H → ZMod 3)
  have hQ : 0 < Q := by
    change (0 : ℝ) < (Fintype.card (Fin H → ZMod 3) : ℝ)
    exact_mod_cast
      (Fintype.card_pos_iff.mpr
        ⟨(fun _i : Fin H => (0 : ZMod 3))⟩)
  have hlower :
      Q * (squarefreeI R / squarefreeZ R - ε) ≤
        ∑ ω : Fin H → ZMod 3, L.wordExtremizerOccupancy ω := by
    calc
      Q * (squarefreeI R / squarefreeZ R - ε) =
          ∑ _ω : Fin H → ZMod 3,
            (squarefreeI R / squarefreeZ R - ε) := by
              simp [Q]
              ring
      _ ≤ ∑ ω : Fin H → ZMod 3, L.wordExtremizerOccupancy ω := by
        apply Finset.sum_le_sum
        intro ω _hω
        have hcanonical :=
          L.capacity_le_wordOccupancy_add_distance hR ω
        have hdist := hclose ω
        linarith
  have hupper :
      (∑ ω : Fin H → ZMod 3, L.wordExtremizerOccupancy ω) ≤
        κ * Q := by
    rw [L.sum_wordExtremizerOccupancy]
    calc
      (∑ a ∈ L.samples, L.mass a *
          (L.occupiedWords a
            (squarefreeExtremizerFamily R (L.cutoff a))).card) ≤
          ∑ a ∈ L.samples, L.mass a * (κ * Q) := by
            apply Finset.sum_le_sum
            intro a ha
            apply mul_le_mul_of_nonneg_left
            · simpa [Q] using
                hcube a ha (squarefreeExtremizerFamily R (L.cutoff a))
                  (squarefreeExtremizerFamily_admissible R (L.cutoff a))
            · exact L.mass_nonneg a ha
      _ = κ * Q := by
        rw [← Finset.sum_mul, L.mass_sum]
        ring
  have hcombined :
      Q * (squarefreeI R / squarefreeZ R - ε) ≤ κ * Q :=
    hlower.trans hupper
  nlinarith

/-- Interface variant phrased using `PairProductCube.familyWords`. -/
theorem finite_jointPrefix_transference_of_familyWords
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeCutoffLaw α H R) (hR : IsPrimeSupport R)
    {ε κ : ℝ}
    (hclose : ∀ ω : Fin H → ZMod 3,
      L.wordPrefixDistance ω ≤ ε)
    (hcube : ∀ (c : PairProductCube H) (𝓕 : Finset (Finset ℕ)),
      Admissible 𝓕 →
      ((c.familyWords 𝓕).card : ℝ) ≤ κ * (3 : ℝ) ^ H) :
    squarefreeI R / squarefreeZ R ≤ κ + ε := by
  apply finite_jointPrefix_transference L hR hclose
  intro a _ha 𝓕 h𝓕
  simpa [FiniteCubeCutoffLaw.occupiedWords,
    PairProductCube.familyWords, Fintype.card_pi_const, ZMod.card] using
    hcube (L.cube a) 𝓕 h𝓕

/-- Combining finite joint-prefix transference with the qualitative cap-set
input: for every requested cube saving there is a dimension in which every
finite joint law satisfying the word-marginal comparison transfers that
saving to squarefree capacity. -/
theorem exists_dimension_finite_jointPrefix_transference
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ H : ℕ, ∀ (α : Type*) [DecidableEq α] (R : Finset ℕ)
      (L : FiniteCubeCutoffLaw α H R), IsPrimeSupport R →
      ∀ {ε : ℝ},
        (∀ ω : Fin H → ZMod 3, L.wordPrefixDistance ω ≤ ε) →
        squarefreeI R / squarefreeZ R ≤ κ + ε := by
  obtain ⟨H, hH⟩ := exists_dimension_cubeSaving_card_le κ hκ
  refine ⟨H, ?_⟩
  intro α _inst R L hR ε hclose
  exact finite_jointPrefix_transference_of_familyWords L hR hclose hH

end Erdos536
