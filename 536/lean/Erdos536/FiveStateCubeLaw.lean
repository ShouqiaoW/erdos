import Erdos536.BalancedCubeCutoff
import Erdos536.FiveStateCoupling

/-!
# Five-state configurations as pair-product cubes

An accepted configuration of the finite five-state model gives a
one-dimensional pair-product cube: label `1` is the common part and labels
`2,3,4` are the three petals.  This file packages the conditioned
configuration law as a `FiniteCubeLaw` and identifies each word marginal
with the corresponding conditioned five-state support marginal.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Forget the subtype proof on a finite set. -/
def underlyingValues {R : Finset ℕ} (S : Finset ↥R) : Finset ℕ :=
  S.image Subtype.val

theorem underlyingValues_subset {R : Finset ℕ} (S : Finset ↥R) :
    underlyingValues S ⊆ R := by
  intro p hp
  rw [underlyingValues, mem_image] at hp
  obtain ⟨q, _hqS, rfl⟩ := hp
  exact q.property

theorem underlyingValues_injective {R : Finset ℕ} :
    Function.Injective (underlyingValues (R := R)) := by
  intro S T h
  ext p
  have hp :
      p.1 ∈ underlyingValues S ↔ p.1 ∈ underlyingValues T := by
    simp only [h]
  simpa [underlyingValues] using hp

/-- The common-label part of a configuration, on the subtype ground set. -/
def fiveCommonSubtype (R : Finset ℕ) (c : FiveConfiguration R) :
    Finset ↥R :=
  Finset.univ.filter fun p ↦ c p = 1

/-- One petal-label part of a configuration, on the subtype ground set. -/
def fivePetalSubtype (R : Finset ℕ) (c : FiveConfiguration R)
    (s : Fin 3) : Finset ↥R :=
  Finset.univ.filter fun p ↦ c p = petalLabel s

/-- The common-label part after forgetting subtype proofs. -/
def fiveCommonValues (R : Finset ℕ) (c : FiveConfiguration R) :
    Finset ℕ :=
  underlyingValues (fiveCommonSubtype R c)

/-- A petal-label part after forgetting subtype proofs. -/
def fivePetalValues (R : Finset ℕ) (c : FiveConfiguration R)
    (s : Fin 3) : Finset ℕ :=
  underlyingValues (fivePetalSubtype R c s)

@[simp]
theorem mem_fiveCommonSubtype (R : Finset ℕ)
    (c : FiveConfiguration R) (p : ↥R) :
    p ∈ fiveCommonSubtype R c ↔ c p = 1 := by
  simp [fiveCommonSubtype]

@[simp]
theorem mem_fivePetalSubtype (R : Finset ℕ)
    (c : FiveConfiguration R) (s : Fin 3) (p : ↥R) :
    p ∈ fivePetalSubtype R c s ↔ c p = petalLabel s := by
  simp [fivePetalSubtype]

theorem fiveCommonSubtype_disjoint_fivePetalSubtype
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    Disjoint (fiveCommonSubtype R c) (fivePetalSubtype R c s) := by
  rw [Finset.disjoint_left]
  intro p hpC hpP
  have hC : c p = 1 := (mem_fiveCommonSubtype R c p).mp hpC
  have hP : c p = petalLabel s :=
    (mem_fivePetalSubtype R c s p).mp hpP
  have hne : (1 : FiveLabel) ≠ petalLabel s := by
    fin_cases s <;> decide
  exact hne (hC.symm.trans hP)

theorem fivePetalSubtype_disjoint
    (R : Finset ℕ) (c : FiveConfiguration R) {s t : Fin 3}
    (hst : s ≠ t) :
    Disjoint (fivePetalSubtype R c s) (fivePetalSubtype R c t) := by
  rw [Finset.disjoint_left]
  intro p hpS hpT
  have hS : c p = petalLabel s :=
    (mem_fivePetalSubtype R c s p).mp hpS
  have hT : c p = petalLabel t :=
    (mem_fivePetalSubtype R c t p).mp hpT
  have : petalLabel s = petalLabel t := hS.symm.trans hT
  apply hst
  exact Fin.ext (by simpa [petalLabel] using congrArg Fin.val this)

theorem fiveCommonValues_disjoint_fivePetalValues
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    Disjoint (fiveCommonValues R c) (fivePetalValues R c s) := by
  rw [Finset.disjoint_left]
  intro p hpC hpP
  rw [fiveCommonValues, underlyingValues, mem_image] at hpC
  rw [fivePetalValues, underlyingValues, mem_image] at hpP
  obtain ⟨q, hqC, hq⟩ := hpC
  obtain ⟨u, huP, hu⟩ := hpP
  have hqu : q = u := Subtype.ext (hq.trans hu.symm)
  subst u
  exact Finset.disjoint_left.mp
    (fiveCommonSubtype_disjoint_fivePetalSubtype R c s) hqC huP

theorem fivePetalValues_disjoint
    (R : Finset ℕ) (c : FiveConfiguration R) {s t : Fin 3}
    (hst : s ≠ t) :
    Disjoint (fivePetalValues R c s) (fivePetalValues R c t) := by
  rw [Finset.disjoint_left]
  intro p hpS hpT
  rw [fivePetalValues, underlyingValues, mem_image] at hpS hpT
  obtain ⟨q, hqS, hq⟩ := hpS
  obtain ⟨u, huT, hu⟩ := hpT
  have hqu : q = u := Subtype.ext (hq.trans hu.symm)
  subst u
  exact Finset.disjoint_left.mp
    (fivePetalSubtype_disjoint R c hst) hqS huT

/-- Regard a residue modulo three as its canonical element of `Fin 3`. -/
def zmodThreeToFin (s : ZMod 3) : Fin 3 :=
  ⟨s.val, s.val_lt⟩

/-- The ternary word corresponding to a five-state support. -/
def fiveStateWord (s : Fin 3) : Fin 1 → ZMod 3 :=
  fun _ ↦ (s.1 : ZMod 3)

theorem finThree_cast_zmod_injective :
    Function.Injective (fun s : Fin 3 ↦ (s.1 : ZMod 3)) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg ZMod.val h
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt,
    Nat.mod_eq_of_lt t.isLt] using hv

theorem zmodThreeToFin_fiveStateWord (s : Fin 3) (i : Fin 1) :
    zmodThreeToFin (fiveStateWord s i) = s := by
  apply Fin.ext
  simp [zmodThreeToFin, fiveStateWord]

theorem fiveLabelIncluded_iff_common_or_otherPetal
    (s : Fin 3) (l : FiveLabel) :
    fiveLabelIncluded s l ↔
      l = 1 ∨ ∃ t : Fin 3, t ≠ s ∧ l = petalLabel t := by
  fin_cases s <;> fin_cases l <;>
    simp [fiveLabelIncluded, petalLabel] <;> decide

/-- Predicate saying that every accepted configuration has three nonempty
petals. -/
def FiveEventHasPetals (R : Finset ℕ)
    (B : FiveConfiguration R → Bool) : Prop :=
  ∀ c, B c → ∀ s : Fin 3, (fivePetalSubtype R c s).Nonempty

/-- The one-dimensional pair-product cube carried by an accepted
five-state configuration. -/
def fiveConfigurationCube
    (R : Finset ℕ) (B : FiveConfiguration R → Bool)
    (hpetals : FiveEventHasPetals R B)
    (c : {c : FiveConfiguration R // B c}) :
    PairProductCube 1 where
  common := fiveCommonValues R c.1
  petal := fun _ s ↦ fivePetalValues R c.1 (zmodThreeToFin s)
  petal_nonempty := by
    intro _ s
    obtain ⟨p, hp⟩ := hpetals c.1 c.2 (zmodThreeToFin s)
    exact ⟨p.1, by
      rw [fivePetalValues, underlyingValues, mem_image]
      exact ⟨p, hp, rfl⟩⟩
  common_disjoint := by
    intro _ s
    exact fiveCommonValues_disjoint_fivePetalValues
      R c.1 (zmodThreeToFin s)
  petal_disjoint := by
    intro i s j t hij
    have hst : s ≠ t := by
      intro h
      have hij' : (i, s) = (j, t) := by
        apply Prod.ext
        · exact Subsingleton.elim _ _
        · exact h
      exact hij hij'
    apply fivePetalValues_disjoint R c.1
    intro hfin
    apply hst
    apply ZMod.val_injective
    exact congrArg Fin.val hfin

/-- The word support of the cube is exactly the represented five-state
support, after forgetting subtype proofs. -/
theorem fiveConfigurationCube_wordSupport
    (R : Finset ℕ) (B : FiveConfiguration R → Bool)
    (hpetals : FiveEventHasPetals R B)
    (c : {c : FiveConfiguration R // B c}) (s : Fin 3) :
    (fiveConfigurationCube R B hpetals c).wordSupport
        (fiveStateWord s) =
      underlyingValues (fiveStateSupport R s c.1) := by
  ext p
  constructor
  · intro hp
    rcases ((fiveConfigurationCube R B hpetals c).mem_wordSupport_iff
      (fiveStateWord s) p).mp hp with hpC | hpP
    · change p ∈ fiveCommonValues R c.1 at hpC
      rw [fiveCommonValues, underlyingValues, mem_image] at hpC
      obtain ⟨q, hqC, rfl⟩ := hpC
      rw [underlyingValues, mem_image]
      refine ⟨q, ?_, rfl⟩
      rw [mem_fiveStateSupport,
        fiveLabelIncluded_iff_common_or_otherPetal]
      exact Or.inl ((mem_fiveCommonSubtype R c.1 q).mp hqC)
    · obtain ⟨i, z, hz, hpz⟩ := hpP
      change p ∈ fivePetalValues R c.1 (zmodThreeToFin z) at hpz
      rw [fivePetalValues, underlyingValues, mem_image] at hpz
      obtain ⟨q, hqz, rfl⟩ := hpz
      rw [underlyingValues, mem_image]
      refine ⟨q, ?_, rfl⟩
      rw [mem_fiveStateSupport,
        fiveLabelIncluded_iff_common_or_otherPetal]
      refine Or.inr ⟨zmodThreeToFin z, ?_, ?_⟩
      · intro heq
        apply hz
        apply ZMod.val_injective
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa [fiveStateWord, zmodThreeToFin,
          Nat.mod_eq_of_lt s.isLt] using congrArg Fin.val heq
      · exact (mem_fivePetalSubtype R c.1
          (zmodThreeToFin z) q).mp hqz
  · intro hp
    rw [underlyingValues, mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    rw [mem_fiveStateSupport,
      fiveLabelIncluded_iff_common_or_otherPetal] at hq
    apply ((fiveConfigurationCube R B hpetals c).mem_wordSupport_iff
      (fiveStateWord s) q.1).mpr
    rcases hq with hcommon | ⟨t, hts, ht⟩
    · apply Or.inl
      change q.1 ∈ fiveCommonValues R c.1
      rw [fiveCommonValues, underlyingValues, mem_image]
      exact ⟨q, (mem_fiveCommonSubtype R c.1 q).mpr hcommon, rfl⟩
    · apply Or.inr
      let z : ZMod 3 := (t.1 : ZMod 3)
      refine ⟨0, z, ?_, ?_⟩
      · intro hz
        exact hts (finThree_cast_zmod_injective
          (by simpa [z, fiveStateWord] using hz))
      · change q.1 ∈ fivePetalValues R c.1 (zmodThreeToFin z)
        rw [fivePetalValues, underlyingValues, mem_image]
        refine ⟨q, ?_, rfl⟩
        rw [mem_fivePetalSubtype]
        simpa [zmodThreeToFin, z,
          Nat.mod_eq_of_lt t.isLt] using ht

/-- Accepted configurations, used as the finite sample type of the
conditioned law. -/
abbrev AcceptedFiveConfiguration (R : Finset ℕ)
    (B : FiveConfiguration R → Bool) :=
  {c : FiveConfiguration R // B c}

/-- The conditioned mass of one accepted configuration. -/
noncomputable def conditionedFiveConfigurationMass
    (R : Finset ℕ) (r : ℕ → ℝ)
    (B : FiveConfiguration R → Bool)
    (c : AcceptedFiveConfiguration R B) : ℝ :=
  fiveConfigurationWeight R r c.1 / fiveEventMass R r B

theorem sum_acceptedFiveConfiguration_support
    (R : Finset ℕ) (r : ℕ → ℝ)
    (B : FiveConfiguration R → Bool)
    (s : Fin 3) (S : Finset ↥R) :
    (∑ c : AcceptedFiveConfiguration R B,
        if fiveStateSupport R s c.1 = S then
          fiveConfigurationWeight R r c.1
        else 0) =
      fiveEventSupportMass R r B s S := by
  classical
  rw [fiveEventSupportMass]
  symm
  calc
    (∑ c : FiveConfiguration R,
        if B c ∧ fiveStateSupport R s c = S then
          fiveConfigurationWeight R r c
        else 0) =
        ∑ c ∈ Finset.univ.filter (fun c ↦ B c),
          if fiveStateSupport R s c = S then
            fiveConfigurationWeight R r c
          else 0 := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro c _hc
            by_cases hBc : B c
            · by_cases hS : fiveStateSupport R s c = S <;>
                simp [hBc, hS]
            · simp [hBc]
    _ = ∑ c : AcceptedFiveConfiguration R B,
          if fiveStateSupport R s c.1 = S then
            fiveConfigurationWeight R r c.1
          else 0 := by
            apply Finset.sum_subtype
            intro c
            simp

theorem sum_conditionedFiveConfigurationMass
    (R : Finset ℕ) (r : ℕ → ℝ)
    (B : FiveConfiguration R → Bool)
    (hB : fiveEventMass R r B ≠ 0) :
    (∑ c : AcceptedFiveConfiguration R B,
        conditionedFiveConfigurationMass R r B c) = 1 := by
  classical
  simp_rw [conditionedFiveConfigurationMass]
  rw [← Finset.sum_div]
  have hevent :
      (∑ c : AcceptedFiveConfiguration R B,
          fiveConfigurationWeight R r c.1) =
        fiveEventMass R r B := by
    rw [fiveEventMass, ← Finset.sum_filter]
    symm
    apply Finset.sum_subtype
    intro c
    simp
  rw [hevent, div_self hB]

/-- The normalized five-state event law, packaged as a law on
one-dimensional pair-product cubes. -/
noncomputable def conditionedFiveCubeLaw
    (R : Finset ℕ) (r : ℕ → ℝ)
    (B : FiveConfiguration R → Bool)
    (hpetals : FiveEventHasPetals R B)
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr : ∀ p ∈ R, r p ≤ 3 / 4)
    (hB : 0 < fiveEventMass R r B) :
    FiniteCubeLaw (AcceptedFiveConfiguration R B) 1 R where
  samples := Finset.univ
  mass := conditionedFiveConfigurationMass R r B
  cube := fiveConfigurationCube R B hpetals
  mass_nonneg := by
    intro c _hc
    apply div_nonneg
    · rw [fiveConfigurationWeight]
      exact Finset.prod_nonneg fun p _hp ↦
        fiveLabelWeight_nonneg (hr0 p.1 p.2) (hr p.1 p.2) (c.1 p)
    · exact hB.le
  mass_sum := by
    simpa using sum_conditionedFiveConfigurationMass R r B hB.ne'
  wordSupport_subset := by
    intro c _hc ω
    have hword :
        (fiveConfigurationCube R B hpetals c).wordSupport ω =
          underlyingValues
            (fiveStateSupport R (zmodThreeToFin (ω 0)) c.1) := by
      have hω :
          ω = fiveStateWord (zmodThreeToFin (ω 0)) := by
        funext i
        apply ZMod.val_injective
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp [fiveStateWord, zmodThreeToFin]
      calc
        (fiveConfigurationCube R B hpetals c).wordSupport ω =
            (fiveConfigurationCube R B hpetals c).wordSupport
              (fiveStateWord (zmodThreeToFin (ω 0))) :=
          congrArg
            (fun w ↦
              (fiveConfigurationCube R B hpetals c).wordSupport w) hω
        _ = underlyingValues
              (fiveStateSupport R (zmodThreeToFin (ω 0)) c.1) :=
          fiveConfigurationCube_wordSupport R B hpetals c _
    rw [hword]
    exact underlyingValues_subset _

/-- Each word marginal of the cube law is exactly the corresponding
conditioned five-state support marginal. -/
theorem conditionedFiveCubeLaw_wordSupportMass
    (R : Finset ℕ) (r : ℕ → ℝ)
    (B : FiveConfiguration R → Bool)
    (hpetals : FiveEventHasPetals R B)
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr : ∀ p ∈ R, r p ≤ 3 / 4)
    (hB : 0 < fiveEventMass R r B)
    (s : Fin 3) (S : Finset ↥R) :
    (conditionedFiveCubeLaw R r B hpetals hr0 hr hB).wordSupportMass
        (fiveStateWord s) (underlyingValues S) =
      conditionedFiveSupportMass R r B s S := by
  classical
  have hsupport :
      ∀ c : AcceptedFiveConfiguration R B,
        (fiveConfigurationCube R B hpetals c).wordSupport
            (fiveStateWord s) = underlyingValues S ↔
          fiveStateSupport R s c.1 = S := by
    intro c
    rw [fiveConfigurationCube_wordSupport]
    constructor
    · intro h
      exact (underlyingValues_injective (R := R)) h
    · intro h
      rw [h]
  rw [FiniteCubeLaw.wordSupportMass, conditionedFiveSupportMass]
  change
    (∑ c ∈ (Finset.univ :
        Finset (AcceptedFiveConfiguration R B)),
      if (fiveConfigurationCube R B hpetals c).wordSupport
          (fiveStateWord s) = underlyingValues S then
        conditionedFiveConfigurationMass R r B c
      else 0) =
      fiveEventSupportMass R r B s S / fiveEventMass R r B
  simp only [hsupport, conditionedFiveConfigurationMass]
  calc
    (∑ c : AcceptedFiveConfiguration R B,
        if fiveStateSupport R s c.1 = S then
          fiveConfigurationWeight R r c.1 / fiveEventMass R r B
        else 0) =
        (∑ c : AcceptedFiveConfiguration R B,
          if fiveStateSupport R s c.1 = S then
            fiveConfigurationWeight R r c.1
          else 0) / fiveEventMass R r B := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro c _hc
            by_cases hS : fiveStateSupport R s c.1 = S <;>
              simp [hS]
    _ = fiveEventSupportMass R r B s S /
        fiveEventMass R r B := by
          rw [sum_acceptedFiveConfiguration_support]

end Erdos536
