import Erdos536.CubeLawMixture
import Erdos536.FinitePiProbability
import Erdos536.FinitePushforward
import Erdos536.FiveStateBalance
import Erdos536.FiveStateMarginal
import Erdos536.BernoulliSquarefree

/-!
# One-coordinate cubes from alternative prime bands

Fix finitely many pairwise-disjoint prime bands.  A component sample first
chooses one band to be active.  Its five-state configuration is conditioned
on the prescribed event, while every other band carries an independent,
unconditioned five-state configuration.  The active common part and petals
give the unique cube coordinate; the state-zero represented supports on all
inactive bands are adjoined to the common part.

The component masses and the outer choice of active band are both normalized
exactly.  The word-support decomposition is literal, and multiplicative (or
petal-log) balance is inherited solely from the active event.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- The union of all bands. -/
def allBandSupport {M : ℕ} (R : Fin M → Finset ℕ) : Finset ℕ :=
  Finset.univ.biUnion R

/-- The union of all bands other than `j`. -/
def inactiveBandSupport {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) : Finset ℕ :=
  (Finset.univ : Finset {k : Fin M // k ≠ j}).biUnion
    fun k ↦ R k.1

/-- A convenient explicit formulation of pairwise disjointness of bands. -/
def PairwiseDisjointBands {M : ℕ} (R : Fin M → Finset ℕ) : Prop :=
  ∀ ⦃i j : Fin M⦄, i ≠ j → Disjoint (R i) (R j)

theorem band_subset_allBandSupport
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M) :
    R j ⊆ allBandSupport R := by
  intro p hp
  rw [allBandSupport, mem_biUnion]
  exact ⟨j, Finset.mem_univ j, hp⟩

theorem inactiveBandSupport_subset_allBandSupport
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M) :
    inactiveBandSupport R j ⊆ allBandSupport R := by
  intro p hp
  rw [inactiveBandSupport, mem_biUnion] at hp
  obtain ⟨k, _hk, hpR⟩ := hp
  exact band_subset_allBandSupport R k.1 hpR

theorem band_disjoint_inactiveBandSupport
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hdisj : PairwiseDisjointBands R) (j : Fin M) :
    Disjoint (R j) (inactiveBandSupport R j) := by
  rw [Finset.disjoint_left]
  intro p hpj hp
  rw [inactiveBandSupport, mem_biUnion] at hp
  obtain ⟨k, _hk, hpk⟩ := hp
  exact Finset.disjoint_left.mp (hdisj k.property.symm) hpj hpk

theorem isPrimeSupport_allBandSupport
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j)) :
    IsPrimeSupport (allBandSupport R) := by
  intro p hp
  rw [allBandSupport, mem_biUnion] at hp
  obtain ⟨j, _hj, hpR⟩ := hp
  exact hprime j p hpR

/-- A tuple containing one unconditioned five-state configuration on every
inactive band. -/
abbrev InactiveBandConfigurations
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M) :=
  (k : {k : Fin M // k ≠ j}) → FiveConfiguration (R k.1)

/-- The represented state-zero supports on all inactive bands. -/
noncomputable def inactiveRepresentedSupport
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M)
    (c : InactiveBandConfigurations R j) : Finset ℕ :=
  (Finset.univ : Finset {k : Fin M // k ≠ j}).biUnion fun k ↦
    underlyingValues (fiveStateSupport (R k.1) 0 (c k))

theorem inactiveRepresentedSupport_subset
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M)
    (c : InactiveBandConfigurations R j) :
    inactiveRepresentedSupport R j c ⊆ inactiveBandSupport R j := by
  intro p hp
  rw [inactiveRepresentedSupport, mem_biUnion] at hp
  obtain ⟨k, _hk, hpk⟩ := hp
  rw [inactiveBandSupport, mem_biUnion]
  exact ⟨k, Finset.mem_univ k, underlyingValues_subset _ hpk⟩

/-- Product mass of all unconditioned inactive configurations. -/
noncomputable def inactiveConfigurationMass
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M)
    (c : InactiveBandConfigurations R j) : ℝ :=
  ∏ k, fiveConfigurationWeight (R k.1) reciprocalBernoulli (c k)

theorem sum_inactiveConfigurationMass
    {M : ℕ} (R : Fin M → Finset ℕ) (j : Fin M) :
    ∑ c : InactiveBandConfigurations R j,
        inactiveConfigurationMass R j c = 1 := by
  unfold inactiveConfigurationMass
  rw [← Fintype.prod_sum]
  simp only [sum_fiveConfigurationWeight, Finset.prod_const_one]

theorem inactiveConfigurationMass_nonneg
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j)) (j : Fin M)
    (c : InactiveBandConfigurations R j) :
    0 ≤ inactiveConfigurationMass R j c := by
  rw [inactiveConfigurationMass]
  apply Finset.prod_nonneg
  intro k _hk
  rw [fiveConfigurationWeight]
  apply Finset.prod_nonneg
  intro p _hp
  exact fiveLabelWeight_nonneg
    (reciprocalBernoulli_nonneg p.1)
    (reciprocalBernoulli_le_three_quarters
      ((hprime k.1 p.1 p.2).pos)) (c k p)

/-- A component sample consists of the accepted active configuration and
one unconditioned configuration on every inactive band. -/
abbrev AlternativeBandComponentSample
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M) :=
  AcceptedFiveConfiguration (R j) (B j) ×
    InactiveBandConfigurations R j

/-- The one-coordinate cube carried by a component sample. -/
noncomputable def alternativeBandCube
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hdisj : PairwiseDisjointBands R) (j : Fin M)
    (x : AlternativeBandComponentSample R B j) :
    PairProductCube 1 where
  common :=
    (fiveConfigurationCube (R j) (B j) (hpetals j) x.1).common ∪
      inactiveRepresentedSupport R j x.2
  petal :=
    (fiveConfigurationCube (R j) (B j) (hpetals j) x.1).petal
  petal_nonempty :=
    (fiveConfigurationCube (R j) (B j) (hpetals j) x.1).petal_nonempty
  common_disjoint := by
    intro i s
    rw [Finset.disjoint_union_left]
    refine ⟨
      (fiveConfigurationCube (R j) (B j) (hpetals j) x.1
        |>.common_disjoint i s), ?_⟩
    rw [Finset.disjoint_left]
    intro p hpInactive hpPetal
    have hpInactive' :
        p ∈ inactiveBandSupport R j :=
      inactiveRepresentedSupport_subset R j x.2 hpInactive
    have hpPetal' : p ∈ R j := by
      change p ∈ fivePetalValues (R j) x.1.1 (zmodThreeToFin s)
        at hpPetal
      exact underlyingValues_subset _ hpPetal
    exact Finset.disjoint_left.mp
      (band_disjoint_inactiveBandSupport hdisj j) hpPetal' hpInactive'
  petal_disjoint :=
    (fiveConfigurationCube (R j) (B j) (hpetals j) x.1).petal_disjoint

/-- Every word is the active represented support together with the
state-zero represented supports from all inactive bands. -/
theorem alternativeBandCube_wordSupport
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hdisj : PairwiseDisjointBands R) (j : Fin M)
    (x : AlternativeBandComponentSample R B j)
    (ω : Fin 1 → ZMod 3) :
    (alternativeBandCube R B hpetals hdisj j x).wordSupport ω =
      (fiveConfigurationCube (R j) (B j) (hpetals j) x.1).wordSupport ω ∪
        inactiveRepresentedSupport R j x.2 := by
  rw [PairProductCube.wordSupport, PairProductCube.wordSupport]
  change
    ((fiveConfigurationCube
          (R j) (B j) (hpetals j) x.1).common ∪
        inactiveRepresentedSupport R j x.2) ∪
      Finset.univ.biUnion
        ((fiveConfigurationCube
          (R j) (B j) (hpetals j) x.1).coordinateSupport ω) =
    ((fiveConfigurationCube
          (R j) (B j) (hpetals j) x.1).common ∪
      Finset.univ.biUnion
        ((fiveConfigurationCube
          (R j) (B j) (hpetals j) x.1).coordinateSupport ω)) ∪
      inactiveRepresentedSupport R j x.2
  ext p
  simp only [mem_union]
  tauto

/-- Specialized exact decomposition in the state indexing used by the
five-state coupling. -/
theorem alternativeBandCube_fiveStateWordSupport
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hdisj : PairwiseDisjointBands R) (j : Fin M)
    (x : AlternativeBandComponentSample R B j) (s : Fin 3) :
    (alternativeBandCube R B hpetals hdisj j x).wordSupport
        (fiveStateWord s) =
      underlyingValues (fiveStateSupport (R j) s x.1.1) ∪
        inactiveRepresentedSupport R j x.2 := by
  rw [alternativeBandCube_wordSupport,
    fiveConfigurationCube_wordSupport]

/-- The product law on a component sample. -/
noncomputable def alternativeBandComponentMass
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M)
    (x : AlternativeBandComponentSample R B j) : ℝ :=
  conditionedFiveConfigurationMass
      (R j) reciprocalBernoulli (B j) x.1 *
    inactiveConfigurationMass R j x.2

theorem sum_alternativeBandComponentMass
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (j : Fin M) :
    ∑ x : AlternativeBandComponentSample R B j,
        alternativeBandComponentMass R B j x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [alternativeBandComponentMass, ← Finset.mul_sum]
  rw [sum_inactiveConfigurationMass]
  simp only [mul_one]
  exact sum_conditionedFiveConfigurationMass
    (R j) reciprocalBernoulli (B j) (hB j).ne'

/-- The normalized law obtained with a fixed active band. -/
noncomputable def alternativeBandComponentLaw
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R) (j : Fin M) :
    FiniteCubeLaw (AlternativeBandComponentSample R B j) 1
      (allBandSupport R) where
  samples := Finset.univ
  mass := alternativeBandComponentMass R B j
  cube := alternativeBandCube R B hpetals hdisj j
  mass_nonneg := by
    intro x _hx
    apply mul_nonneg
    · apply div_nonneg
      · rw [fiveConfigurationWeight]
        apply Finset.prod_nonneg
        intro p _hp
        exact fiveLabelWeight_nonneg
          (reciprocalBernoulli_nonneg p.1)
          (reciprocalBernoulli_le_three_quarters
            ((hprime j p.1 p.2).pos)) (x.1.1 p)
      · exact (hB j).le
    · exact inactiveConfigurationMass_nonneg hprime j x.2
  mass_sum := by
    simpa using sum_alternativeBandComponentMass R B hB j
  wordSupport_subset := by
    intro x _hx ω
    rw [alternativeBandCube_wordSupport]
    apply Finset.union_subset
    · have hactive :=
        (conditionedFiveCubeLaw (R j) reciprocalBernoulli (B j)
          (hpetals j)
          (fun p _hp ↦ reciprocalBernoulli_nonneg p)
          (fun p hp ↦ reciprocalBernoulli_le_three_quarters
            ((hprime j p hp).pos))
          (hB j)).wordSupport_subset x.1 (Finset.mem_univ x.1) ω
      exact hactive.trans (band_subset_allBandSupport R j)
    · exact (inactiveRepresentedSupport_subset R j x.2).trans
        (inactiveBandSupport_subset_allBandSupport R j)

private theorem primeProduct_union_cast
    {A C : Finset ℕ} (hAC : Disjoint A C) :
    (primeProduct (A ∪ C) : ℝ) =
      (primeProduct A : ℝ) * (primeProduct C : ℝ) := by
  unfold primeProduct
  rw [Finset.prod_union hAC, Nat.cast_mul]

/-- Product balance of the active event is unchanged after adjoining the
same inactive common support to all three words. -/
theorem alternativeBandComponentLaw_multiplicativelyBalanced
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R) {δ : ℝ}
    (hbalance : ∀ j, FiveEventMultiplicativelyBalanced (R j) (B j) δ)
    (j : Fin M) :
    (alternativeBandComponentLaw
      R B hprime hpetals hB hdisj j).MultiplicativelyBalanced δ := by
  intro x _hx ω τ
  have hactive :=
    conditionedFiveCubeLaw_multiplicativelyBalanced
      (hpetals j)
      (fun p _hp ↦ reciprocalBernoulli_nonneg p)
      (fun p hp ↦ reciprocalBernoulli_le_three_quarters
        ((hprime j p hp).pos))
      (hB j) (hbalance j) x.1 (Finset.mem_univ x.1) ω τ
  have hactiveSubset :
      ∀ w : Fin 1 → ZMod 3,
        (fiveConfigurationCube
          (R j) (B j) (hpetals j) x.1).wordSupport w ⊆ R j := by
    intro w
    exact
      (conditionedFiveCubeLaw (R j) reciprocalBernoulli (B j)
        (hpetals j)
        (fun p _hp ↦ reciprocalBernoulli_nonneg p)
        (fun p hp ↦ reciprocalBernoulli_le_three_quarters
          ((hprime j p hp).pos))
        (hB j)).wordSupport_subset x.1 (Finset.mem_univ x.1) w
  have hinactiveSubset :
      inactiveRepresentedSupport R j x.2 ⊆ inactiveBandSupport R j :=
    inactiveRepresentedSupport_subset R j x.2
  have hdisjointWord :
      ∀ w : Fin 1 → ZMod 3,
        Disjoint
          ((fiveConfigurationCube
            (R j) (B j) (hpetals j) x.1).wordSupport w)
          (inactiveRepresentedSupport R j x.2) := by
    intro w
    rw [Finset.disjoint_left]
    intro p hpw hpi
    exact Finset.disjoint_left.mp
      (band_disjoint_inactiveBandSupport hdisj j)
      (hactiveSubset w hpw) (hinactiveSubset hpi)
  change
    (primeProduct
        ((alternativeBandCube R B hpetals hdisj j x).wordSupport τ) : ℝ) ≤
      (1 + δ) *
        (primeProduct
          ((alternativeBandCube R B hpetals hdisj j x).wordSupport ω) : ℝ)
  rw [alternativeBandCube_wordSupport,
    alternativeBandCube_wordSupport,
    primeProduct_union_cast (hdisjointWord τ),
    primeProduct_union_cast (hdisjointWord ω)]
  calc
    (primeProduct
          ((fiveConfigurationCube
            (R j) (B j) (hpetals j) x.1).wordSupport τ) : ℝ) *
        (primeProduct (inactiveRepresentedSupport R j x.2) : ℝ) ≤
      ((1 + δ) *
          (primeProduct
            ((fiveConfigurationCube
              (R j) (B j) (hpetals j) x.1).wordSupport ω) : ℝ)) *
        (primeProduct (inactiveRepresentedSupport R j x.2) : ℝ) :=
      mul_le_mul_of_nonneg_right hactive (Nat.cast_nonneg _)
    _ = (1 + δ) *
        ((primeProduct
            ((fiveConfigurationCube
              (R j) (B j) (hpetals j) x.1).wordSupport ω) : ℝ) *
          (primeProduct (inactiveRepresentedSupport R j x.2) : ℝ)) := by
      ring

/-- A complete sample records the uniformly chosen active band and all of
its active and inactive configurations. -/
abbrev AlternativeBandSample
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) :=
  Σ j, AlternativeBandComponentSample R B j

noncomputable instance alternativeBandSampleDecidableEq
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) :
    DecidableEq (AlternativeBandSample R B) :=
  Classical.decEq _

/-- Mass of a complete alternative-band sample. -/
noncomputable def alternativeBandMass
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (x : AlternativeBandSample R B) : ℝ :=
  (M : ℝ)⁻¹ * alternativeBandComponentMass R B x.1 x.2

/-- Choose the active band uniformly and then sample its component law. -/
noncomputable def alternativeBandCubeLaw
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R) :
    FiniteCubeLaw (AlternativeBandSample R B) 1 (allBandSupport R) where
  samples := Finset.univ
  mass := alternativeBandMass R B
  cube := fun x ↦ alternativeBandCube R B hpetals hdisj x.1 x.2
  mass_nonneg := by
    intro x _hx
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg M))
    exact
      (alternativeBandComponentLaw
        R B hprime hpetals hB hdisj x.1).mass_nonneg
          x.2 (Finset.mem_univ x.2)
  mass_sum := by
    change
      (∑ x : AlternativeBandSample R B,
        alternativeBandMass R B x) = 1
    rw [Fintype.sum_sigma]
    calc
      (∑ j, ∑ x : AlternativeBandComponentSample R B j,
          alternativeBandMass R B ⟨j, x⟩) =
        ∑ j, (M : ℝ)⁻¹ *
          ∑ x : AlternativeBandComponentSample R B j,
            alternativeBandComponentMass R B j x := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.mul_sum]
          rfl
      _ = ∑ _j : Fin M, (M : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [sum_alternativeBandComponentMass R B hB j, mul_one]
      _ = 1 := by
          simp only [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          rw [mul_inv_cancel₀]
          exact_mod_cast hM.ne'
  wordSupport_subset := by
    intro x _hx ω
    exact
      (alternativeBandComponentLaw
        R B hprime hpetals hB hdisj x.1).wordSupport_subset
          x.2 (Finset.mem_univ x.2) ω

/-- The complete law has total mass one. -/
theorem alternativeBandCubeLaw_mass_sum
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R) :
    ∑ x ∈ (alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).samples,
      (alternativeBandCubeLaw
        hM R B hprime hpetals hB hdisj).mass x = 1 :=
  (alternativeBandCubeLaw
    hM R B hprime hpetals hB hdisj).mass_sum

/-- The complete law is supported inside the union of all bands. -/
theorem alternativeBandCubeLaw_wordSupport_subset
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (x : AlternativeBandSample R B)
    (ω : Fin 1 → ZMod 3) :
    ((alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).cube x).wordSupport ω ⊆
        allBandSupport R :=
  (alternativeBandCubeLaw
    hM R B hprime hpetals hB hdisj).wordSupport_subset
      x (Finset.mem_univ x) ω

/-- Exact word-support decomposition for a sample of the complete law. -/
theorem alternativeBandCubeLaw_wordSupport
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (x : AlternativeBandSample R B) (ω : Fin 1 → ZMod 3) :
    ((alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).cube x).wordSupport ω =
      (fiveConfigurationCube
        (R x.1) (B x.1) (hpetals x.1) x.2.1).wordSupport ω ∪
        inactiveRepresentedSupport R x.1 x.2.2 := by
  exact alternativeBandCube_wordSupport
    R B hpetals hdisj x.1 x.2 ω

/-- A uniform mixture inherits the common active-event product balance. -/
theorem alternativeBandCubeLaw_multiplicativelyBalanced
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R) {δ : ℝ}
    (hbalance : ∀ j, FiveEventMultiplicativelyBalanced (R j) (B j) δ) :
    (alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).MultiplicativelyBalanced δ := by
  intro x _hx ω τ
  exact alternativeBandComponentLaw_multiplicativelyBalanced
    R B hprime hpetals hB hdisj hbalance x.1
      x.2 (Finset.mem_univ x.2) ω τ

/-- Petal-log balance on every possible active event gives balance with
error `exp η - 1` for the complete alternative-band law. -/
theorem alternativeBandCubeLaw_multiplicativelyBalanced_exp_sub_one
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R) {η : ℝ}
    (hlog : ∀ j, FiveEventPetalLogBalanced (R j) (B j) η) :
    (alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).MultiplicativelyBalanced
        (Real.exp η - 1) := by
  apply alternativeBandCubeLaw_multiplicativelyBalanced
    hM R B hprime hpetals hB hdisj
  intro j
  exact fiveEventMultiplicativelyBalanced_exp_sub_one
    (hprime j) (hlog j)

/-! ## The root-space density of the alternative-band marginal -/

/-- One represented support on every band. -/
abbrev AlternativeBandRoots
    {M : ℕ} (R : Fin M → Finset ℕ) :=
  (j : Fin M) → Finset ↥(R j)

/-- The reciprocal product mass on the tuple of band roots. -/
noncomputable def alternativeBandRootWeight
    {M : ℕ} (R : Fin M → Finset ℕ)
    (A : AlternativeBandRoots R) : ℝ :=
  finitePiWeight
    (fun j ↦ subtypeBernoulliWeight (R j) reciprocalBernoulli) A

/-- Forget subtype proofs and unite all represented band supports. -/
noncomputable def alternativeBandRootUnion
    {M : ℕ} (R : Fin M → Finset ℕ)
    (A : AlternativeBandRoots R) : Finset ℕ :=
  Finset.univ.biUnion fun j ↦ underlyingValues (A j)

/-- The Bayes density contributed when `j` is the active band. -/
noncomputable def alternativeBandCoordinateDensity
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (s : Fin 3) (j : Fin M) (A : AlternativeBandRoots R) : ℝ :=
  rootedBayesDensity
    (fiveEventMass (R j) reciprocalBernoulli (B j))
    (fiveRootLikelihood (R j) reciprocalBernoulli (B j) s) (A j)

/-- The density of the uniform alternative-band mixture on root tuples. -/
noncomputable def alternativeBandRootDensity
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (s : Fin 3) (A : AlternativeBandRoots R) : ℝ :=
  uniformAlternativeAverage
    (fun j ↦ alternativeBandCoordinateDensity R B s j) A

/-- Pushforward commutes with forming a finite dependent product. -/
theorem finitePiPushforwardMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω ρ : ι → Type*}
    [(i : ι) → Fintype (Ω i)] [(i : ι) → DecidableEq (Ω i)]
    [(i : ι) → Fintype (ρ i)] [(i : ι) → DecidableEq (ρ i)]
    (μ : (i : ι) → Ω i → ℝ) (f : (i : ι) → Ω i → ρ i)
    (r : (i : ι) → ρ i) :
    finitePushforwardMass Finset.univ (finitePiWeight μ)
        (fun x i ↦ f i (x i)) r =
      finitePiWeight
        (fun i y ↦ finitePushforwardMass Finset.univ (μ i) (f i) y) r := by
  classical
  rw [finitePushforwardMass, finitePiWeight]
  change
    (∑ x : ((i : ι) → Ω i),
      if (fun i ↦ f i (x i)) = r then ∏ i, μ i (x i) else 0) =
      ∏ i, ∑ x : Ω i, if f i x = r i then μ i x else 0
  calc
    (∑ x : ((i : ι) → Ω i),
        if (fun i ↦ f i (x i)) = r then ∏ i, μ i (x i) else 0) =
      ∑ x : ((i : ι) → Ω i),
        ∏ i, if f i (x i) = r i then μ i (x i) else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          by_cases h : (fun i ↦ f i (x i)) = r
          · rw [if_pos h]
            apply Finset.prod_congr rfl
            intro i _hi
            rw [if_pos (congrFun h i)]
          · rw [if_neg h]
            have hexists : ∃ i, f i (x i) ≠ r i := by
              by_contra hnone
              push_neg at hnone
              exact h (funext hnone)
            obtain ⟨i, hi⟩ := hexists
            symm
            apply Finset.prod_eq_zero (i := i) (Finset.mem_univ i)
            rw [if_neg hi]
    _ = ∏ i, ∑ x : Ω i,
        if f i x = r i then μ i x else 0 :=
      (Fintype.prod_sum
        (fun i x ↦ if f i x = r i then μ i x else 0)).symm

/-- A second pushforward may be performed after the first one. -/
theorem finitePushforwardMass_comp
    {Ω ρ V : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype ρ] [DecidableEq ρ] [DecidableEq V]
    (w : Ω → ℝ) (f : Ω → ρ) (g : ρ → V) (v : V) :
    finitePushforwardMass Finset.univ w (fun x ↦ g (f x)) v =
      finitePushforwardMass Finset.univ
        (finitePushforwardMass Finset.univ w f) g v := by
  classical
  rw [finitePushforwardMass, finitePushforwardMass]
  change
    (∑ x : Ω, if g (f x) = v then w x else 0) =
      ∑ r : ρ,
        if g r = v then
          ∑ x : Ω, if f x = r then w x else 0
        else 0
  calc
    (∑ x : Ω, if g (f x) = v then w x else 0) =
        ∑ x : Ω, ∑ r : ρ,
          if f x = r ∧ g r = v then w x else 0 := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [Finset.sum_eq_single (f x)]
            · simp
            · intro r _hr hr
              simp [hr.symm]
            · simp
    _ = ∑ r : ρ, ∑ x : Ω,
          if f x = r ∧ g r = v then w x else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ r : ρ,
          if g r = v then
            ∑ x : Ω, if f x = r then w x else 0
          else 0 := by
            apply Finset.sum_congr rfl
            intro r _hr
            by_cases hr : g r = v <;> simp [hr]

/-- Data processing for a density relative to a nonnegative finite base
law. -/
theorem finitePushforward_density_l1_le
    {Ω V : Type*} [DecidableEq Ω] [DecidableEq V]
    (P : Finset Ω) (Q : Finset V)
    (w X : Ω → ℝ) (f : Ω → V)
    (hw : ∀ x ∈ P, 0 ≤ w x)
    (hf : ∀ x ∈ P, f x ∈ Q) :
    (∑ v ∈ Q,
        |finitePushforwardMass P (fun x ↦ w x * X x) f v -
          finitePushforwardMass P w f v|) ≤
      finiteL1Error P w X := by
  have h :=
    finitePushforward_l1_le P Q
      (fun x ↦ w x * X x) w f hf
  calc
    (∑ v ∈ Q,
        |finitePushforwardMass P (fun x ↦ w x * X x) f v -
          finitePushforwardMass P w f v|) ≤
      ∑ x ∈ P, |w x * X x - w x| := h
    _ = finiteL1Error P w X := by
      rw [finiteL1Error, finiteExpectation]
      apply Finset.sum_congr rfl
      intro x hx
      rw [show w x * X x - w x = w x * (X x - 1) by ring,
        abs_mul, abs_of_nonneg (hw x hx)]

theorem alternativeBandRootWeight_nonneg
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j))
    (A : AlternativeBandRoots R) :
    0 ≤ alternativeBandRootWeight R A := by
  apply finitePiWeight_nonneg
  intro j S
  apply subtypeBernoulliWeight_nonneg
  · intro p _hp
    exact reciprocalBernoulli_nonneg p
  · intro p hp
    have hthree :=
      reciprocalBernoulli_le_three_quarters ((hprime j p hp).pos)
    linarith

theorem sum_alternativeBandRootWeight
    {M : ℕ} (R : Fin M → Finset ℕ) :
    ∑ A : AlternativeBandRoots R,
        alternativeBandRootWeight R A = 1 := by
  apply sum_finitePiWeight
  intro j
  exact sum_subtypeBernoulliWeight (R j) reciprocalBernoulli

private theorem alternativeBandRootMass_pos
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j))
    (j : Fin M) (S : Finset ↥(R j)) :
    0 < subtypeBernoulliWeight (R j) reciprocalBernoulli S := by
  apply subtypeBernoulliWeight_pos
  · intro p _hp
    exact reciprocalBernoulli_pos
  · intro p hp
    exact reciprocalBernoulli_lt_one ((hprime j p hp).pos)

/-- Each active-coordinate Bayes density has mean one under its local
reciprocal root law. -/
theorem alternativeBandLocalDensity_mean
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (s : Fin 3) (j : Fin M) :
    (∑ S : Finset ↥(R j),
        subtypeBernoulliWeight (R j) reciprocalBernoulli S *
          rootedBayesDensity
            (fiveEventMass (R j) reciprocalBernoulli (B j))
            (fiveRootLikelihood
              (R j) reciprocalBernoulli (B j) s) S) = 1 := by
  have hrootLaw :
      IsFiniteRootLaw Finset.univ
        (subtypeBernoulliWeight (R j) reciprocalBernoulli) := by
    refine ⟨?_, ?_⟩
    · intro S _hS
      exact (alternativeBandRootMass_pos hprime j S).le
    · simpa using
        sum_subtypeBernoulliWeight (R j) reciprocalBernoulli
  have hμ :
      ∀ S : Finset ↥(R j),
        subtypeBernoulliWeight (R j) reciprocalBernoulli S ≠ 0 :=
    fun S ↦ (alternativeBandRootMass_pos hprime j S).ne'
  have hevent :=
    fiveRootLikelihood_eventMass
      (R j) reciprocalBernoulli (B j) s hμ
  have hmean :=
    rootedBayesDensity_mean_one hrootLaw hevent (hB j)
  simpa [rootedExpectation] using hmean

theorem alternativeBandCoordinateDensity_nonneg
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (s : Fin 3) (j : Fin M) (A : AlternativeBandRoots R) :
    0 ≤ alternativeBandCoordinateDensity R B s j A := by
  have hμpos :=
    alternativeBandRootMass_pos hprime j (A j)
  have heventNonneg :
      0 ≤ fiveEventSupportMass
        (R j) reciprocalBernoulli (B j) s (A j) := by
    rw [fiveEventSupportMass]
    apply Finset.sum_nonneg
    intro c _hc
    split_ifs
    · rw [fiveConfigurationWeight]
      apply Finset.prod_nonneg
      intro p _hp
      exact fiveLabelWeight_nonneg
        (reciprocalBernoulli_nonneg p.1)
        (reciprocalBernoulli_le_three_quarters
          ((hprime j p.1 p.2).pos)) (c p)
    · exact le_rfl
  rw [alternativeBandCoordinateDensity, rootedBayesDensity,
    fiveRootLikelihood]
  exact div_nonneg (div_nonneg heventNonneg hμpos.le) (hB j).le

theorem alternativeBandCoordinateDensity_mean
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (s : Fin 3) (j : Fin M) :
    finiteExpectation Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandCoordinateDensity R B s j) = 1 := by
  let μ :=
    fun k ↦ subtypeBernoulliWeight (R k) reciprocalBernoulli
  let g := fun k S ↦
    rootedBayesDensity
      (fiveEventMass (R k) reciprocalBernoulli (B k))
      (fiveRootLikelihood (R k) reciprocalBernoulli (B k) s) S
  have hmass : ∀ k, ∑ S, μ k S = 1 := by
    intro k
    exact sum_subtypeBernoulliWeight (R k) reciprocalBernoulli
  have hmean : ∀ k, ∑ S, μ k S * g k S = 1 := by
    intro k
    exact alternativeBandLocalDensity_mean
      R B hprime hB s k
  have h :=
    finitePiCoordinateDensity_mean μ g hmass hmean j
  simpa [alternativeBandRootWeight, alternativeBandCoordinateDensity,
    finitePiCoordinateDensity, μ, g] using h

theorem alternativeBandCoordinateDensity_pairwiseFactorizes
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (s : Fin 3) :
    PairwiseFactorizesUnder Finset.univ
      (alternativeBandRootWeight R)
      (alternativeBandCoordinateDensity R B s) := by
  let μ :=
    fun k ↦ subtypeBernoulliWeight (R k) reciprocalBernoulli
  let g := fun k S ↦
    rootedBayesDensity
      (fiveEventMass (R k) reciprocalBernoulli (B k))
      (fiveRootLikelihood (R k) reciprocalBernoulli (B k) s) S
  have hmass : ∀ k, ∑ S, μ k S = 1 := by
    intro k
    exact sum_subtypeBernoulliWeight (R k) reciprocalBernoulli
  have hmean : ∀ k, ∑ S, μ k S * g k S = 1 := by
    intro k
    exact alternativeBandLocalDensity_mean
      R B hprime hB s k
  have h :=
    finitePiCoordinateDensity_pairwiseFactorizes μ g hmass hmean
  simpa [alternativeBandRootWeight, alternativeBandCoordinateDensity,
    finitePiCoordinateDensity, μ, g] using h

theorem alternativeBandCoordinateDensity_secondMoment
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (s : Fin 3) (j : Fin M) :
    finiteSecondMoment Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandCoordinateDensity R B s j) =
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight (R j) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass (R j) reciprocalBernoulli (B j))
          (fiveRootLikelihood
            (R j) reciprocalBernoulli (B j) s)) := by
  let μ :=
    fun k ↦ subtypeBernoulliWeight (R k) reciprocalBernoulli
  let g := fun k S ↦
    rootedBayesDensity
      (fiveEventMass (R k) reciprocalBernoulli (B k))
      (fiveRootLikelihood (R k) reciprocalBernoulli (B k) s) S
  have hmass : ∀ k, ∑ S, μ k S = 1 := by
    intro k
    exact sum_subtypeBernoulliWeight (R k) reciprocalBernoulli
  have h :=
    finitePiCoordinateDensity_secondMoment μ g hmass j
  simpa [alternativeBandRootWeight, alternativeBandCoordinateDensity,
    finitePiCoordinateDensity, rootedSecondMoment, rootedExpectation,
    μ, g] using h

/-- The variance gain from choosing one of `M` independent alternative
bands, stated directly on the root product space. -/
theorem alternativeBandRootDensity_l1_le
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (s : Fin 3) {K : ℝ} (hK : 0 ≤ K)
    (hsecond : ∀ j,
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight (R j) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass (R j) reciprocalBernoulli (B j))
          (fiveRootLikelihood
            (R j) reciprocalBernoulli (B j) s)) ≤ K) :
    finiteL1Error Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandRootDensity R B s) ≤
      Real.sqrt (K / (M : ℝ)) := by
  apply uniformAlternativeAverage_l1_le_of_uniform_secondMoment
    hM
  · intro A _hA
    exact alternativeBandRootWeight_nonneg hprime A
  · simpa using sum_alternativeBandRootWeight R
  · intro j A _hA
    exact alternativeBandCoordinateDensity_nonneg
      R B hprime hB s j A
  · intro j
    exact alternativeBandCoordinateDensity_mean
      R B hprime hB s j
  · exact alternativeBandCoordinateDensity_pairwiseFactorizes
      R B hprime hB s
  · exact hK
  · intro j
    rw [alternativeBandCoordinateDensity_secondMoment]
    exact hsecond j

theorem alternativeBandRootUnion_subset
    {M : ℕ} (R : Fin M → Finset ℕ)
    (A : AlternativeBandRoots R) :
    alternativeBandRootUnion R A ⊆ allBandSupport R := by
  intro p hp
  rw [alternativeBandRootUnion, mem_biUnion] at hp
  obtain ⟨j, _hj, hpA⟩ := hp
  exact band_subset_allBandSupport R j (underlyingValues_subset _ hpA)

/-- The root-space variance estimate survives the final union
pushforward.  This is the exact data-processing endpoint used by the
alternative-band construction. -/
theorem alternativeBandRootPushforward_l1_le
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (s : Fin 3) {K : ℝ} (hK : 0 ≤ K)
    (hsecond : ∀ j,
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight (R j) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass (R j) reciprocalBernoulli (B j))
          (fiveRootLikelihood
            (R j) reciprocalBernoulli (B j) s)) ≤ K) :
    (∑ S ∈ (allBandSupport R).powerset,
        |finitePushforwardMass Finset.univ
            (fun A ↦ alternativeBandRootWeight R A *
              alternativeBandRootDensity R B s A)
            (alternativeBandRootUnion R) S -
          finitePushforwardMass Finset.univ
            (alternativeBandRootWeight R)
            (alternativeBandRootUnion R) S|) ≤
      Real.sqrt (K / (M : ℝ)) := by
  have hdata :=
    finitePushforward_density_l1_le
      (Finset.univ : Finset (AlternativeBandRoots R))
      (allBandSupport R).powerset
      (alternativeBandRootWeight R)
      (alternativeBandRootDensity R B s)
      (alternativeBandRootUnion R)
      (fun A _hA ↦ alternativeBandRootWeight_nonneg hprime A)
      (fun A _hA ↦
        Finset.mem_powerset.mpr
          (alternativeBandRootUnion_subset R A))
  exact hdata.trans
    (alternativeBandRootDensity_l1_le
      hM R B hprime hB s hK hsecond)

private theorem pairwiseDisjointBands_on_univ
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hdisj : PairwiseDisjointBands R) :
    (↑(Finset.univ : Finset (Fin M)) : Set (Fin M)).PairwiseDisjoint R := by
  intro i _hi j _hj hij
  exact hdisj hij

theorem squarefreeZ_allBandSupport
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hdisj : PairwiseDisjointBands R) :
    squarefreeZ (allBandSupport R) =
      ∏ j, squarefreeZ (R j) := by
  rw [squarefreeZ_eq_prod, allBandSupport,
    Finset.prod_biUnion (pairwiseDisjointBands_on_univ hdisj)]
  apply Finset.prod_congr rfl
  intro j _hj
  rw [squarefreeZ_eq_prod]

theorem primeProduct_alternativeBandRootUnion
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hdisj : PairwiseDisjointBands R)
    (A : AlternativeBandRoots R) :
    primeProduct (alternativeBandRootUnion R A) =
      ∏ j, primeProduct (underlyingValues (A j)) := by
  have hpair :
      (↑(Finset.univ : Finset (Fin M)) :
          Set (Fin M)).PairwiseDisjoint
        (fun j ↦ underlyingValues (A j)) := by
    intro i _hi j _hj hij
    change Disjoint (underlyingValues (A i)) (underlyingValues (A j))
    rw [Finset.disjoint_left]
    intro p hpi hpj
    exact Finset.disjoint_left.mp (hdisj hij)
      (underlyingValues_subset _ hpi)
      (underlyingValues_subset _ hpj)
  unfold primeProduct alternativeBandRootUnion
  exact Finset.prod_biUnion hpair

/-- The independent tuple of reciprocal band roots pushes forward to the
canonical reciprocal mass on their union. -/
theorem alternativeBandRootWeight_eq_canonical
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hdisj : PairwiseDisjointBands R)
    (A : AlternativeBandRoots R) :
    alternativeBandRootWeight R A =
      1 / (squarefreeZ (allBandSupport R) *
        (primeProduct (alternativeBandRootUnion R A) : ℝ)) := by
  rw [alternativeBandRootWeight, finitePiWeight]
  have hlocal :
      ∀ j, subtypeBernoulliWeight (R j) reciprocalBernoulli (A j) =
        1 / (squarefreeZ (R j) *
          (primeProduct (underlyingValues (A j)) : ℝ)) := by
    intro j
    exact subtypeBernoulliWeight_reciprocal_underlying
      (hprime j) (A j)
  simp_rw [hlocal]
  rw [squarefreeZ_allBandSupport hdisj,
    primeProduct_alternativeBandRootUnion hdisj]
  push_cast
  simp only [one_div, mul_inv_rev, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]

theorem alternativeBandRootUnion_injective
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hdisj : PairwiseDisjointBands R) :
    Function.Injective (alternativeBandRootUnion R) := by
  intro A C hAC
  funext j
  apply underlyingValues_injective
  ext p
  constructor
  · intro hp
    have hpUnion :
        p ∈ alternativeBandRootUnion R A := by
      rw [alternativeBandRootUnion, mem_biUnion]
      exact ⟨j, Finset.mem_univ j, hp⟩
    have hpUnionC :
        p ∈ alternativeBandRootUnion R C := hAC ▸ hpUnion
    rw [alternativeBandRootUnion, mem_biUnion] at hpUnionC
    obtain ⟨k, _hk, hpk⟩ := hpUnionC
    have hpRj : p ∈ R j := underlyingValues_subset _ hp
    have hkj : k = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj hne)
        (underlyingValues_subset _ hpk) hpRj
    subst k
    exact hpk
  · intro hp
    have hpUnion :
        p ∈ alternativeBandRootUnion R C := by
      rw [alternativeBandRootUnion, mem_biUnion]
      exact ⟨j, Finset.mem_univ j, hp⟩
    have hpUnionA :
        p ∈ alternativeBandRootUnion R A := hAC.symm ▸ hpUnion
    rw [alternativeBandRootUnion, mem_biUnion] at hpUnionA
    obtain ⟨k, _hk, hpk⟩ := hpUnionA
    have hpRj : p ∈ R j := underlyingValues_subset _ hp
    have hkj : k = j := by
      by_contra hne
      exact Finset.disjoint_left.mp (hdisj hne)
        (underlyingValues_subset _ hpk) hpRj
    subst k
    exact hpk

/-- At every support in the image, the unconditioned root pushforward is
exactly the canonical reciprocal support mass. -/
theorem alternativeBandRootPushforward_eq_canonical
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hdisj : PairwiseDisjointBands R)
    (A : AlternativeBandRoots R) :
    finitePushforwardMass Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandRootUnion R)
        (alternativeBandRootUnion R A) =
      1 / (squarefreeZ (allBandSupport R) *
        (primeProduct (alternativeBandRootUnion R A) : ℝ)) := by
  rw [finitePushforwardMass]
  rw [Finset.sum_eq_single A]
  · simp [alternativeBandRootWeight_eq_canonical hprime hdisj]
  · intro C _hC hCA
    have hne :
        alternativeBandRootUnion R C ≠
          alternativeBandRootUnion R A := by
      intro h
      exact hCA (alternativeBandRootUnion_injective hdisj h)
    simp [hne]
  · simp

/-! ### Identification with the concrete cube samples -/

/-- One five-state configuration on every band. -/
abbrev AlternativeBandConfigurations
    {M : ℕ} (R : Fin M → Finset ℕ) :=
  (j : Fin M) → FiveConfiguration (R j)

/-- Full band configurations whose active coordinate satisfies its event. -/
abbrev AcceptedAlternativeBandConfigurations
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M) :=
  {c : AlternativeBandConfigurations R // B j (c j)}

/-- Splitting a full accepted tuple at its active coordinate gives exactly
the component sample type used above. -/
noncomputable def acceptedAlternativeBandSplitEquiv
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M) :
    AcceptedAlternativeBandConfigurations R B j ≃
      AlternativeBandComponentSample R B j := by
  let e :=
    Equiv.piSplitAt j (fun k ↦ FiveConfiguration (R k))
  let eAccepted :
      AcceptedAlternativeBandConfigurations R B j ≃
        {x : FiveConfiguration (R j) ×
            InactiveBandConfigurations R j // B j x.1} :=
    e.subtypeEquiv (fun c ↦ by
      rw [Equiv.piSplitAt_apply])
  exact eAccepted.trans
    (Equiv.prodSubtypeFstEquivSubtypeProd
      (p := fun a : FiveConfiguration (R j) ↦ B j a = true))

@[simp]
theorem acceptedAlternativeBandSplitEquiv_active
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M)
    (c : AcceptedAlternativeBandConfigurations R B j) :
    (acceptedAlternativeBandSplitEquiv R B j c).1.1 = c.1 j := by
  change c.1 j = c.1 j
  rfl

@[simp]
theorem acceptedAlternativeBandSplitEquiv_inactive
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M)
    (c : AcceptedAlternativeBandConfigurations R B j)
    (k : {k : Fin M // k ≠ j}) :
    (acceptedAlternativeBandSplitEquiv R B j c).2 k = c.1 k.1 := by
  change c.1 k.1 = c.1 k.1
  rfl

/-- The root tuple represented by a full configuration when `j` is active:
state `s` on `j`, and state zero elsewhere. -/
noncomputable def alternativeBandConfigurationRoot
    {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) (s : Fin 3)
    (c : AlternativeBandConfigurations R) :
    AlternativeBandRoots R :=
  fun k ↦ if h : k = j then
    by
      subst k
      exact fiveStateSupport (R j) s (c j)
  else fiveStateSupport (R k) 0 (c k)

@[simp]
theorem alternativeBandConfigurationRoot_active
    {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) (s : Fin 3)
    (c : AlternativeBandConfigurations R) :
    alternativeBandConfigurationRoot R j s c j =
      fiveStateSupport (R j) s (c j) := by
  simp [alternativeBandConfigurationRoot]

@[simp]
theorem alternativeBandConfigurationRoot_inactive
    {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) (s : Fin 3)
    (c : AlternativeBandConfigurations R)
    (k : {k : Fin M // k ≠ j}) :
    alternativeBandConfigurationRoot R j s c k.1 =
      fiveStateSupport (R k.1) 0 (c k.1) := by
  simp [alternativeBandConfigurationRoot, k.2]

theorem alternativeBandConfigurationRoot_union
    {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) (s : Fin 3)
    (c : AlternativeBandConfigurations R) :
    alternativeBandRootUnion R
        (alternativeBandConfigurationRoot R j s c) =
      underlyingValues (fiveStateSupport (R j) s (c j)) ∪
        inactiveRepresentedSupport R j (fun k ↦ c k.1) := by
  ext p
  constructor
  · intro hp
    rw [alternativeBandRootUnion, mem_biUnion] at hp
    obtain ⟨k, _hk, hpk⟩ := hp
    by_cases hkj : k = j
    · subst k
      exact Finset.mem_union_left _
        (by simpa using hpk)
    · apply Finset.mem_union_right
      rw [alternativeBandConfigurationRoot_inactive
        R j s c ⟨k, hkj⟩] at hpk
      rw [inactiveRepresentedSupport, mem_biUnion]
      exact ⟨⟨k, hkj⟩, Finset.mem_univ _, hpk⟩
  · intro hp
    rw [Finset.mem_union] at hp
    rw [alternativeBandRootUnion, mem_biUnion]
    rcases hp with hpActive | hpInactive
    · exact ⟨j, Finset.mem_univ _, by simpa using hpActive⟩
    · rw [inactiveRepresentedSupport, mem_biUnion] at hpInactive
      obtain ⟨k, _hk, hpk⟩ := hpInactive
      exact ⟨k.1, Finset.mem_univ _,
        by simpa [alternativeBandConfigurationRoot, k.2] using hpk⟩

/-- Local full-configuration weight: the active coordinate is conditioned,
and every other coordinate is unconditioned. -/
noncomputable def alternativeBandLocalConfigurationMass
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (j k : Fin M) (c : FiveConfiguration (R k)) : ℝ :=
  if k = j then
    if B k c then
      fiveConfigurationWeight (R k) reciprocalBernoulli c /
        fiveEventMass (R k) reciprocalBernoulli (B k)
    else 0
  else fiveConfigurationWeight (R k) reciprocalBernoulli c

/-- Product form of the fixed-active-band law on full configurations. -/
noncomputable def alternativeBandFullConfigurationMass
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (j : Fin M) (c : AlternativeBandConfigurations R) : ℝ :=
  finitePiWeight
    (alternativeBandLocalConfigurationMass R B j) c

theorem alternativeBandFullConfigurationMass_accepted
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M)
    (c : AcceptedAlternativeBandConfigurations R B j) :
    alternativeBandFullConfigurationMass R B j c.1 =
      alternativeBandComponentMass R B j
        (acceptedAlternativeBandSplitEquiv R B j c) := by
  rw [alternativeBandFullConfigurationMass, finitePiWeight,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun k ↦
        alternativeBandLocalConfigurationMass R B j k (c.1 k)) j]
  rw [alternativeBandComponentMass,
    conditionedFiveConfigurationMass, inactiveConfigurationMass,
    acceptedAlternativeBandSplitEquiv_active]
  simp_rw [acceptedAlternativeBandSplitEquiv_inactive]
  rw [alternativeBandLocalConfigurationMass, if_pos rfl, if_pos c.2]
  congr 1
  apply Finset.prod_congr rfl
  intro k _hk
  rw [alternativeBandLocalConfigurationMass, if_neg k.2]

theorem alternativeBandFullConfigurationMass_rejected
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool) (j : Fin M)
    (c : AlternativeBandConfigurations R) (hc : ¬B j (c j)) :
    alternativeBandFullConfigurationMass R B j c = 0 := by
  rw [alternativeBandFullConfigurationMass, finitePiWeight,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun k ↦
        alternativeBandLocalConfigurationMass R B j k (c k)) j]
  simp [alternativeBandLocalConfigurationMass, hc]

theorem acceptedAlternativeBandCube_wordSupport
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hdisj : PairwiseDisjointBands R)
    (j : Fin M) (s : Fin 3)
    (c : AcceptedAlternativeBandConfigurations R B j) :
    (alternativeBandCube R B hpetals hdisj j
        (acceptedAlternativeBandSplitEquiv R B j c)).wordSupport
          (fiveStateWord s) =
      alternativeBandRootUnion R
        (alternativeBandConfigurationRoot R j s c.1) := by
  rw [alternativeBandCube_fiveStateWordSupport,
    acceptedAlternativeBandSplitEquiv_active]
  have hinactive :
      (acceptedAlternativeBandSplitEquiv R B j c).2 =
        fun k : {k : Fin M // k ≠ j} ↦ c.1 k.1 := by
    funext k
    exact acceptedAlternativeBandSplitEquiv_inactive R B j c k
  rw [hinactive, alternativeBandConfigurationRoot_union]

/-- A component cube marginal is the pushforward of its full product
configuration law through the represented-root union. -/
theorem alternativeBandComponent_wordSupportMass_eq_configurationPushforward
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (j : Fin M) (s : Fin 3) (S : Finset ℕ) :
    (alternativeBandComponentLaw
      R B hprime hpetals hB hdisj j).wordSupportMass
        (fiveStateWord s) S =
      finitePushforwardMass Finset.univ
        (alternativeBandFullConfigurationMass R B j)
        (fun c ↦ alternativeBandRootUnion R
          (alternativeBandConfigurationRoot R j s c)) S := by
  classical
  rw [FiniteCubeLaw.wordSupportMass]
  change
    (∑ x : AlternativeBandComponentSample R B j,
      if (alternativeBandCube R B hpetals hdisj j x).wordSupport
          (fiveStateWord s) = S then
        alternativeBandComponentMass R B j x
      else 0) =
    finitePushforwardMass Finset.univ
      (alternativeBandFullConfigurationMass R B j)
      (fun c ↦ alternativeBandRootUnion R
        (alternativeBandConfigurationRoot R j s c)) S
  let e := acceptedAlternativeBandSplitEquiv R B j
  let F : AlternativeBandConfigurations R → ℝ :=
    fun c ↦
      if alternativeBandRootUnion R
          (alternativeBandConfigurationRoot R j s c) = S then
        alternativeBandFullConfigurationMass R B j c
      else 0
  calc
    (∑ x : AlternativeBandComponentSample R B j,
        if (alternativeBandCube R B hpetals hdisj j x).wordSupport
            (fiveStateWord s) = S then
          alternativeBandComponentMass R B j x
        else 0) =
      ∑ c : AcceptedAlternativeBandConfigurations R B j, F c.1 := by
        symm
        apply Fintype.sum_equiv e
        intro c
        dsimp only [F]
        rw [acceptedAlternativeBandCube_wordSupport,
          alternativeBandFullConfigurationMass_accepted]
    _ = ∑ c : AlternativeBandConfigurations R, F c := by
        calc
          (∑ c : AcceptedAlternativeBandConfigurations R B j, F c.1) =
              ∑ c ∈ (Finset.univ :
                  Finset (AlternativeBandConfigurations R)).filter
                    (fun c ↦ B j (c j)), F c := by
                symm
                apply Finset.sum_subtype
                intro c
                simp
          _ = ∑ c : AlternativeBandConfigurations R, F c := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro c _hc
                by_cases hcB : B j (c j)
                · simp [hcB]
                · have hzero :=
                    alternativeBandFullConfigurationMass_rejected
                      R B j c hcB
                  by_cases hs :
                      alternativeBandRootUnion R
                        (alternativeBandConfigurationRoot R j s c) = S
                  <;> simp [F, hcB, hs, hzero]
    _ = finitePushforwardMass Finset.univ
        (alternativeBandFullConfigurationMass R B j)
        (fun c ↦ alternativeBandRootUnion R
          (alternativeBandConfigurationRoot R j s c)) S := by
      rw [finitePushforwardMass]

/-- The represented root of a single local configuration, with state `s`
on the active coordinate and state zero elsewhere. -/
noncomputable def alternativeBandLocalConfigurationRoot
    {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) (s : Fin 3) (k : Fin M)
    (c : FiveConfiguration (R k)) : Finset ↥(R k) :=
  if h : k = j then
    by
      subst k
      exact fiveStateSupport (R j) s c
  else fiveStateSupport (R k) 0 c

theorem alternativeBandConfigurationRoot_eq_local
    {M : ℕ} (R : Fin M → Finset ℕ)
    (j : Fin M) (s : Fin 3)
    (c : AlternativeBandConfigurations R) :
    alternativeBandConfigurationRoot R j s c =
      fun k ↦ alternativeBandLocalConfigurationRoot R j s k (c k) := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [alternativeBandConfigurationRoot,
      alternativeBandLocalConfigurationRoot]
  · simp [alternativeBandConfigurationRoot,
      alternativeBandLocalConfigurationRoot, hkj]

theorem alternativeBandLocalConfigurationPushforward_active
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (j : Fin M) (s : Fin 3) (S : Finset ↥(R j)) :
    finitePushforwardMass Finset.univ
        (alternativeBandLocalConfigurationMass R B j j)
        (alternativeBandLocalConfigurationRoot R j s j) S =
      subtypeBernoulliWeight (R j) reciprocalBernoulli S *
        rootedBayesDensity
          (fiveEventMass (R j) reciprocalBernoulli (B j))
          (fiveRootLikelihood
            (R j) reciprocalBernoulli (B j) s) S := by
  have hμ :
      subtypeBernoulliWeight (R j) reciprocalBernoulli S ≠ 0 :=
    (alternativeBandRootMass_pos hprime j S).ne'
  rw [← conditionedFiveSupportMass_eq_density (R j) (B j) s S hμ]
  rw [conditionedFiveSupportMass, fiveEventSupportMass,
    finitePushforwardMass, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hcB : B j c
  · by_cases hcS : fiveStateSupport (R j) s c = S <;>
      simp [alternativeBandLocalConfigurationMass,
        alternativeBandLocalConfigurationRoot, hcB, hcS]
  · simp [alternativeBandLocalConfigurationMass,
      alternativeBandLocalConfigurationRoot, hcB]

theorem alternativeBandLocalConfigurationPushforward_inactive
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (j : Fin M) (s : Fin 3) (k : {k : Fin M // k ≠ j})
    (S : Finset ↥(R k.1)) :
    finitePushforwardMass Finset.univ
        (alternativeBandLocalConfigurationMass R B j k.1)
        (alternativeBandLocalConfigurationRoot R j s k.1) S =
      subtypeBernoulliWeight (R k.1) reciprocalBernoulli S := by
  simpa [alternativeBandLocalConfigurationMass,
    alternativeBandLocalConfigurationRoot, finitePushforwardMass,
    k.2] using
      fiveStateSupport_marginal_eq_subtypeBernoulliWeight
        (R k.1) reciprocalBernoulli 0 S

/-- Pushing a fixed-active full configuration law to all represented roots
gives the reciprocal root product law times the active Bayes density. -/
theorem alternativeBandFullConfiguration_rootPushforward
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (j : Fin M) (s : Fin 3) (A : AlternativeBandRoots R) :
    finitePushforwardMass Finset.univ
        (alternativeBandFullConfigurationMass R B j)
        (alternativeBandConfigurationRoot R j s) A =
      alternativeBandRootWeight R A *
        alternativeBandCoordinateDensity R B s j A := by
  have hroot :
      (alternativeBandConfigurationRoot R j s) =
        fun c k ↦
          alternativeBandLocalConfigurationRoot R j s k (c k) := by
    funext c
    exact alternativeBandConfigurationRoot_eq_local R j s c
  rw [hroot]
  change
    finitePushforwardMass Finset.univ
        (finitePiWeight
          (alternativeBandLocalConfigurationMass R B j))
        (fun c k ↦
          alternativeBandLocalConfigurationRoot R j s k (c k)) A =
      alternativeBandRootWeight R A *
        alternativeBandCoordinateDensity R B s j A
  rw [finitePiPushforwardMass]
  rw [finitePiWeight, alternativeBandRootWeight, finitePiWeight,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun k ↦ finitePushforwardMass Finset.univ
        (alternativeBandLocalConfigurationMass R B j k)
        (alternativeBandLocalConfigurationRoot R j s k) (A k)) j,
    Fintype.prod_eq_mul_prod_subtype_ne
      (fun k ↦ subtypeBernoulliWeight
        (R k) reciprocalBernoulli (A k)) j]
  rw [alternativeBandLocalConfigurationPushforward_active
    R B hprime j s (A j)]
  have hinactive :
      (∏ k : {k : Fin M // k ≠ j},
        finitePushforwardMass Finset.univ
          (alternativeBandLocalConfigurationMass R B j k.1)
          (alternativeBandLocalConfigurationRoot R j s k.1) (A k.1)) =
      ∏ k : {k : Fin M // k ≠ j},
        subtypeBernoulliWeight
          (R k.1) reciprocalBernoulli (A k.1) := by
    apply Finset.prod_congr rfl
    intro k _hk
    exact alternativeBandLocalConfigurationPushforward_inactive
      R B j s k (A k.1)
  rw [hinactive, alternativeBandCoordinateDensity]
  ring

/-- Fixed-active configuration pushforward, regrouped at the root level. -/
theorem alternativeBandComponent_wordSupportMass_eq_rootPushforward
    {M : ℕ} (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (j : Fin M) (s : Fin 3) (S : Finset ℕ) :
    (alternativeBandComponentLaw
      R B hprime hpetals hB hdisj j).wordSupportMass
        (fiveStateWord s) S =
      finitePushforwardMass Finset.univ
        (fun A ↦ alternativeBandRootWeight R A *
          alternativeBandCoordinateDensity R B s j A)
        (alternativeBandRootUnion R) S := by
  rw [alternativeBandComponent_wordSupportMass_eq_configurationPushforward
    R B hprime hpetals hB hdisj j s S]
  rw [finitePushforwardMass_comp
    (alternativeBandFullConfigurationMass R B j)
    (alternativeBandConfigurationRoot R j s)
    (alternativeBandRootUnion R) S]
  apply Finset.sum_congr rfl
  intro A _hA
  rw [alternativeBandFullConfiguration_rootPushforward
    R B hprime j s A]

theorem alternativeBandCubeLaw_wordSupportMass_eq_average
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (s : Fin 3) (S : Finset ℕ) :
    (alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).wordSupportMass
        (fiveStateWord s) S =
      (M : ℝ)⁻¹ * ∑ j,
        (alternativeBandComponentLaw
          R B hprime hpetals hB hdisj j).wordSupportMass
            (fiveStateWord s) S := by
  rw [FiniteCubeLaw.wordSupportMass]
  change
    (∑ x : AlternativeBandSample R B,
      if (alternativeBandCube
          R B hpetals hdisj x.1 x.2).wordSupport
            (fiveStateWord s) = S then
        alternativeBandMass R B x
      else 0) =
      (M : ℝ)⁻¹ * ∑ j,
        (alternativeBandComponentLaw
          R B hprime hpetals hB hdisj j).wordSupportMass
            (fiveStateWord s) S
  rw [Fintype.sum_sigma, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [FiniteCubeLaw.wordSupportMass]
  change
    (∑ x : AlternativeBandComponentSample R B j,
      if (alternativeBandCube R B hpetals hdisj j x).wordSupport
          (fiveStateWord s) = S then
        alternativeBandMass R B ⟨j, x⟩
      else 0) =
      (M : ℝ)⁻¹ *
        ∑ x : AlternativeBandComponentSample R B j,
          if (alternativeBandCube R B hpetals hdisj j x).wordSupport
              (fiveStateWord s) = S then
            alternativeBandComponentMass R B j x
          else 0
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hsupp :
      (alternativeBandCube R B hpetals hdisj j x).wordSupport
        (fiveStateWord s) = S
  <;> simp [hsupp, alternativeBandMass]

/-- Exact rooted pushforward identity for the complete alternative-band
cube marginal. -/
theorem alternativeBandCubeLaw_wordSupportMass_eq_rootPushforward
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (s : Fin 3) (S : Finset ℕ) :
    (alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).wordSupportMass
        (fiveStateWord s) S =
      finitePushforwardMass Finset.univ
        (fun A ↦ alternativeBandRootWeight R A *
          alternativeBandRootDensity R B s A)
        (alternativeBandRootUnion R) S := by
  rw [alternativeBandCubeLaw_wordSupportMass_eq_average]
  simp_rw [alternativeBandComponent_wordSupportMass_eq_rootPushforward
    R B hprime hpetals hB hdisj]
  simp_rw [finitePushforwardMass, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _hA
  by_cases hAS : alternativeBandRootUnion R A = S
  · simp only [hAS, if_true, alternativeBandRootDensity,
      uniformAlternativeAverage]
    rw [Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  · simp [hAS]

/-- Canonical root tuple associated with an ordinary support. -/
def alternativeBandRootsOfSupport
    {M : ℕ} (R : Fin M → Finset ℕ) (S : Finset ℕ) :
    AlternativeBandRoots R :=
  fun j ↦ subtypeSupportOf (R j) S

theorem alternativeBandRootUnion_rootsOfSupport
    {M : ℕ} (R : Fin M → Finset ℕ) {S : Finset ℕ}
    (hS : S ⊆ allBandSupport R) :
    alternativeBandRootUnion R
      (alternativeBandRootsOfSupport R S) = S := by
  ext p
  constructor
  · intro hp
    rw [alternativeBandRootUnion, mem_biUnion] at hp
    obtain ⟨j, _hj, hpj⟩ := hp
    rw [underlyingValues, mem_image] at hpj
    obtain ⟨q, hq, rfl⟩ := hpj
    exact mem_subtypeSupportOf.mp hq
  · intro hp
    have hpAll := hS hp
    rw [allBandSupport, mem_biUnion] at hpAll
    obtain ⟨j, _hj, hpR⟩ := hpAll
    rw [alternativeBandRootUnion, mem_biUnion]
    refine ⟨j, Finset.mem_univ _, ?_⟩
    rw [underlyingValues, mem_image]
    let q : ↥(R j) := ⟨p, hpR⟩
    exact ⟨q, mem_subtypeSupportOf.mpr hp, rfl⟩

/-- The unconditioned root pushforward is the canonical reciprocal mass at
every support in the ambient powerset. -/
theorem alternativeBandRootPushforward_eq_canonical_of_subset
    {M : ℕ} {R : Fin M → Finset ℕ}
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hdisj : PairwiseDisjointBands R)
    {S : Finset ℕ} (hS : S ⊆ allBandSupport R) :
    finitePushforwardMass Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandRootUnion R) S =
      1 / (squarefreeZ (allBandSupport R) *
        (primeProduct S : ℝ)) := by
  let A := alternativeBandRootsOfSupport R S
  have hA : alternativeBandRootUnion R A = S :=
    alternativeBandRootUnion_rootsOfSupport R hS
  calc
    finitePushforwardMass Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandRootUnion R) S =
      finitePushforwardMass Finset.univ
        (alternativeBandRootWeight R)
        (alternativeBandRootUnion R)
        (alternativeBandRootUnion R A) := by rw [hA]
    _ = 1 / (squarefreeZ (allBandSupport R) *
        (primeProduct (alternativeBandRootUnion R A) : ℝ)) :=
      alternativeBandRootPushforward_eq_canonical hprime hdisj A
    _ = 1 / (squarefreeZ (allBandSupport R) *
        (primeProduct S : ℝ)) := by rw [hA]

/-- The core one-coordinate conclusion: `M` independent alternative bands
with a uniform rooted second-moment bound `K` produce support error at most
`sqrt (K / M)`. -/
theorem alternativeBandCubeLaw_wordSupportDistance_le
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    (s : Fin 3) {K : ℝ} (hK : 0 ≤ K)
    (hsecond : ∀ j,
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight (R j) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass (R j) reciprocalBernoulli (B j))
          (fiveRootLikelihood
            (R j) reciprocalBernoulli (B j) s)) ≤ K) :
    (alternativeBandCubeLaw
      hM R B hprime hpetals hB hdisj).wordSupportDistance
        (fiveStateWord s) ≤
      Real.sqrt (K / (M : ℝ)) := by
  rw [FiniteCubeLaw.wordSupportDistance]
  calc
    (∑ S ∈ (allBandSupport R).powerset,
        |(alternativeBandCubeLaw
            hM R B hprime hpetals hB hdisj).wordSupportMass
              (fiveStateWord s) S -
          1 / (squarefreeZ (allBandSupport R) *
            (primeProduct S : ℝ))|) =
      ∑ S ∈ (allBandSupport R).powerset,
        |finitePushforwardMass Finset.univ
            (fun A ↦ alternativeBandRootWeight R A *
              alternativeBandRootDensity R B s A)
            (alternativeBandRootUnion R) S -
          finitePushforwardMass Finset.univ
            (alternativeBandRootWeight R)
            (alternativeBandRootUnion R) S| := by
              apply Finset.sum_congr rfl
              intro S hS
              rw [alternativeBandCubeLaw_wordSupportMass_eq_rootPushforward]
              rw [alternativeBandRootPushforward_eq_canonical_of_subset
                hprime hdisj (Finset.mem_powerset.mp hS)]
    _ ≤ Real.sqrt (K / (M : ℝ)) :=
      alternativeBandRootPushforward_l1_le
        hM R B hprime hB s hK hsecond

theorem alternativeBandCubeLaw_wordSupportDistance_le_all
    {M : ℕ} (hM : 0 < M) (R : Fin M → Finset ℕ)
    (B : ∀ j, FiveConfiguration (R j) → Bool)
    (hprime : ∀ j, IsPrimeSupport (R j))
    (hpetals : ∀ j, FiveEventHasPetals (R j) (B j))
    (hB : ∀ j, 0 < fiveEventMass (R j) reciprocalBernoulli (B j))
    (hdisj : PairwiseDisjointBands R)
    {K : ℝ} (hK : 0 ≤ K)
    (hsecond : ∀ j (s : Fin 3),
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight (R j) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass (R j) reciprocalBernoulli (B j))
          (fiveRootLikelihood
            (R j) reciprocalBernoulli (B j) s)) ≤ K) :
    ∀ ω : Fin 1 → ZMod 3,
      (alternativeBandCubeLaw
        hM R B hprime hpetals hB hdisj).wordSupportDistance ω ≤
        Real.sqrt (K / (M : ℝ)) := by
  intro ω
  let s := zmodThreeToFin (ω 0)
  have hω : ω = fiveStateWord s := by
    funext i
    apply ZMod.val_injective
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [s, fiveStateWord, zmodThreeToFin]
  rw [hω]
  exact alternativeBandCubeLaw_wordSupportDistance_le
    hM R B hprime hpetals hB hdisj s hK
      (fun j ↦ hsecond j s)

end Erdos536
