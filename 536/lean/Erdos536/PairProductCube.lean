import Erdos536.Squarefree

/-!
# Pair-product cubes

This file formalizes the finite set-system geometry of the balanced cubes.
The analytic construction of a probability law on such cubes is kept in
later modules.
-/

open Finset

namespace Erdos536

/-- A dimension-`H` pair-product cube.  Petals are indexed by a coordinate
and one of the three elements of `ZMod 3`. -/
structure PairProductCube (H : ℕ) where
  common : Finset ℕ
  petal : Fin H → ZMod 3 → Finset ℕ
  petal_nonempty : ∀ i s, (petal i s).Nonempty
  common_disjoint : ∀ i s, Disjoint common (petal i s)
  petal_disjoint :
    ∀ i s j t, (i, s) ≠ (j, t) → Disjoint (petal i s) (petal j t)

/-- The contribution at one coordinate: all petals except the one named by
the word. -/
def PairProductCube.coordinateSupport {H : ℕ} (c : PairProductCube H)
    (ω : Fin H → ZMod 3) (i : Fin H) : Finset ℕ :=
  (Finset.univ.filter fun s : ZMod 3 => s ≠ ω i).biUnion (c.petal i)

/-- The prime support represented by a ternary word. -/
def PairProductCube.wordSupport {H : ℕ} (c : PairProductCube H)
    (ω : Fin H → ZMod 3) : Finset ℕ :=
  c.common ∪ Finset.univ.biUnion (c.coordinateSupport ω)

theorem PairProductCube.mem_wordSupport_iff {H : ℕ}
    (c : PairProductCube H) (ω : Fin H → ZMod 3) (p : ℕ) :
    p ∈ c.wordSupport ω ↔
      p ∈ c.common ∨
        ∃ i : Fin H, ∃ s : ZMod 3, s ≠ ω i ∧ p ∈ c.petal i s := by
  simp [PairProductCube.wordSupport, PairProductCube.coordinateSupport]

theorem PairProductCube.selectedPetal_subset_wordSupport {H : ℕ}
    (c : PairProductCube H) (ω : Fin H → ZMod 3)
    {i : Fin H} {s : ZMod 3} (hs : s ≠ ω i) :
    c.petal i s ⊆ c.wordSupport ω := by
  intro p hp
  exact (c.mem_wordSupport_iff ω p).mpr
    (Or.inr ⟨i, s, hs, hp⟩)

theorem PairProductCube.omittedPetal_disjoint_wordSupport {H : ℕ}
    (c : PairProductCube H) (ω : Fin H → ZMod 3) (i : Fin H) :
    Disjoint (c.petal i (ω i)) (c.wordSupport ω) := by
  rw [Finset.disjoint_left]
  intro p hp hword
  rcases (c.mem_wordSupport_iff ω p).mp hword with hcommon | hpetal
  · exact Finset.disjoint_left.mp (c.common_disjoint i (ω i)) hcommon hp
  · obtain ⟨j, s, hs, hps⟩ := hpetal
    have hindices : (i, ω i) ≠ (j, s) := by
      intro hEq
      have hi : i = j := congrArg Prod.fst hEq
      have hstate : ω i = s := congrArg Prod.snd hEq
      subst j
      exact hs hstate.symm
    exact Finset.disjoint_left.mp
      (c.petal_disjoint i (ω i) j s hindices) hp hps

/-- Distinct words give distinct supports because every petal is nonempty. -/
theorem PairProductCube.wordSupport_injective {H : ℕ}
    (c : PairProductCube H) :
    Function.Injective c.wordSupport := by
  intro ω τ hsupport
  funext i
  by_contra hne
  obtain ⟨p, hp⟩ := c.petal_nonempty i (ω i)
  have hpτ : p ∈ c.wordSupport τ :=
    c.selectedPetal_subset_wordSupport τ hne hp
  have hpω : p ∉ c.wordSupport ω :=
    Finset.disjoint_left.mp (c.omittedPetal_disjoint_wordSupport ω i) hp
  exact hpω (hsupport ▸ hpτ)

/-- At a coordinate of an affine ternary line, the three states are either
all equal or pairwise distinct. -/
def IsCoordinateLine {H : ℕ} (ω₀ ω₁ ω₂ : Fin H → ZMod 3) : Prop :=
  ∀ i, (ω₀ i = ω₁ i ∧ ω₁ i = ω₂ i) ∨
    (ω₀ i ≠ ω₁ i ∧ ω₀ i ≠ ω₂ i ∧ ω₁ i ≠ ω₂ i)

private theorem omitted_pair_equiv
    {a b c s : ZMod 3}
    (h : (a = b ∧ b = c) ∨ (a ≠ b ∧ a ≠ c ∧ b ≠ c)) :
    (s ≠ a ∨ s ≠ b) ↔ (s ≠ a ∨ s ≠ c) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hab, hac, hbc⟩
  · rfl
  · constructor <;> intro _
    · by_cases hsa : s = a
      · exact Or.inr (hsa ▸ hac)
      · exact Or.inl hsa
    · by_cases hsa : s = a
      · exact Or.inr (hsa ▸ hab)
      · exact Or.inl hsa

private theorem omitted_pair_equiv'
    {a b c s : ZMod 3}
    (h : (a = b ∧ b = c) ∨ (a ≠ b ∧ a ≠ c ∧ b ≠ c)) :
    (s ≠ a ∨ s ≠ c) ↔ (s ≠ b ∨ s ≠ c) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨hab, hac, hbc⟩
  · rfl
  · constructor <;> intro _
    · by_cases hsc : s = c
      · exact Or.inl (hsc ▸ hbc.symm)
      · exact Or.inr hsc
    · by_cases hsc : s = c
      · exact Or.inl (hsc ▸ hac.symm)
      · exact Or.inr hsc

theorem PairProductCube.mem_union_wordSupport_iff {H : ℕ}
    (c : PairProductCube H) (ω τ : Fin H → ZMod 3) (p : ℕ) :
    p ∈ c.wordSupport ω ∪ c.wordSupport τ ↔
      p ∈ c.common ∨
        ∃ i : Fin H, ∃ s : ZMod 3,
          (s ≠ ω i ∨ s ≠ τ i) ∧ p ∈ c.petal i s := by
  simp only [mem_union, c.mem_wordSupport_iff]
  aesop

/-- Three coordinate-line words have identical pairwise unions of their
prime supports. -/
theorem PairProductCube.coordinateLine_equalPairwiseUnions {H : ℕ}
    (c : PairProductCube H) {ω₀ ω₁ ω₂ : Fin H → ZMod 3}
    (hline : IsCoordinateLine ω₀ ω₁ ω₂) :
    EqualPairwiseUnions (c.wordSupport ω₀) (c.wordSupport ω₁)
      (c.wordSupport ω₂) := by
  constructor
  · ext p
    rw [c.mem_union_wordSupport_iff, c.mem_union_wordSupport_iff]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨i, s, hs, hp⟩
      exact ⟨i, s, (omitted_pair_equiv (hline i)).mp hs, hp⟩
    · rintro ⟨i, s, hs, hp⟩
      exact ⟨i, s, (omitted_pair_equiv (hline i)).mpr hs, hp⟩
  · ext p
    rw [c.mem_union_wordSupport_iff, c.mem_union_wordSupport_iff]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨i, s, hs, hp⟩
      exact ⟨i, s, (omitted_pair_equiv' (hline i)).mp hs, hp⟩
    · rintro ⟨i, s, hs, hp⟩
      exact ⟨i, s, (omitted_pair_equiv' (hline i)).mpr hs, hp⟩

end Erdos536
