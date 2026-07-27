import Erdos536.CapSet
import Erdos536.PairProductCube

/-!
# The cap-set saving on a pair-product cube

The words of a pair-product cube which land in an admissible support family
contain no affine ternary line.  The qualitative cap-set theorem therefore
gives a dimension in which every such cube has arbitrarily small relative
occupancy.
-/

open Finset

namespace Erdos536

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The words of `c` whose represented support belongs to `𝓕`. -/
def PairProductCube.familyWords {H : ℕ} (c : PairProductCube H)
    (𝓕 : Finset (Finset ℕ)) : Finset (CapSpace H) :=
  Finset.univ.filter fun ω ↦ c.wordSupport ω ∈ 𝓕

@[simp]
theorem PairProductCube.mem_familyWords {H : ℕ} (c : PairProductCube H)
    (𝓕 : Finset (Finset ℕ)) (ω : CapSpace H) :
    ω ∈ c.familyWords 𝓕 ↔ c.wordSupport ω ∈ 𝓕 := by
  simp [PairProductCube.familyWords]

private theorem zmodThree_line_points_pairwise_ne (a d : ZMod 3) (hd : d ≠ 0) :
    a ≠ a + d ∧ a ≠ a + d + d ∧ a + d ≠ a + d + d := by
  have h₁₂ : a ≠ a + d := by
    intro h
    apply hd
    apply add_left_cancel (a := a)
    simpa using h
  have h₂₃ : a + d ≠ a + d + d := by
    intro h
    apply hd
    apply add_left_cancel (a := a + d)
    simpa using h
  have h₁₃ : a ≠ a + d + d := by
    intro h
    have hdd : d + d = 0 := by
      apply add_left_cancel (a := a)
      simpa [add_assoc] using h.symm
    have hsmul : (2 : ZMod 3) • d = 0 := by
      rw [two_smul]
      exact hdd
    have htwo : (2 : ZMod 3) ≠ 0 := by decide
    exact hd ((smul_eq_zero.mp hsmul).resolve_left htwo)
  exact ⟨h₁₂, h₁₃, h₂₃⟩

/-- In characteristic three, the three points parametrized by a direction
form a coordinate line: each coordinate is either constant or runs through
three distinct values. -/
theorem affineLine_isCoordinateLine {H : ℕ} (x v : CapSpace H) :
    IsCoordinateLine x (x + v) (x + v + v) := by
  intro i
  by_cases hvi : v i = 0
  · left
    simp [Pi.add_apply, hvi]
  · right
    simpa only [Pi.add_apply] using
      zmodThree_line_points_pairwise_ne (x i) (v i) hvi

/-- Pulling an admissible support family back to a pair-product cube produces
an affine-line-free set of ternary words. -/
theorem PairProductCube.familyWords_affineLineFree {H : ℕ}
    (c : PairProductCube H) (𝓕 : Finset (Finset ℕ))
    (h𝓕 : Admissible 𝓕) :
    AffineLineFree (c.familyWords 𝓕) := by
  intro x v hv hx hxv hxvv
  have hmem₀ : c.wordSupport x ∈ 𝓕 := (c.mem_familyWords 𝓕 x).mp hx
  have hmem₁ : c.wordSupport (x + v) ∈ 𝓕 :=
    (c.mem_familyWords 𝓕 (x + v)).mp hxv
  have hmem₂ : c.wordSupport (x + v + v) ∈ 𝓕 :=
    (c.mem_familyWords 𝓕 (x + v + v)).mp hxvv
  obtain ⟨hne₀₁, hne₀₂, hne₁₂⟩ :=
    affineLine_points_pairwise_ne x v hv
  have hsupport₀₁ : c.wordSupport x ≠ c.wordSupport (x + v) :=
    fun h ↦ hne₀₁ (c.wordSupport_injective h)
  have hsupport₀₂ : c.wordSupport x ≠ c.wordSupport (x + v + v) :=
    fun h ↦ hne₀₂ (c.wordSupport_injective h)
  have hsupport₁₂ : c.wordSupport (x + v) ≠ c.wordSupport (x + v + v) :=
    fun h ↦ hne₁₂ (c.wordSupport_injective h)
  have hcard :
      ({c.wordSupport x, c.wordSupport (x + v),
          c.wordSupport (x + v + v)} : Finset (Finset ℕ)).card = 3 := by
    simp [hsupport₀₁, hsupport₀₂, hsupport₁₂]
  exact (h𝓕 hmem₀ hmem₁ hmem₂ hcard)
    (c.coordinateLine_equalPairwiseUnions (affineLine_isCoordinateLine x v))

/-- Qualitative cap-set saving, uniformly over all pair-product cubes and
admissible support families, in a dimension depending only on `ε`. -/
theorem exists_dimension_cubeSaving_card_le (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ (c : PairProductCube H) (𝓕 : Finset (Finset ℕ)),
      Admissible 𝓕 →
        ((c.familyWords 𝓕).card : ℝ) ≤ ε * (3 : ℝ) ^ H := by
  obtain ⟨H, hH⟩ := exists_dimension_affineLineFree_card_le ε hε
  refine ⟨H, fun c 𝓕 h𝓕 ↦ ?_⟩
  exact hH (c.familyWords 𝓕) (c.familyWords_affineLineFree 𝓕 h𝓕)

end Erdos536
