import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Algebra.Field.ZMod

namespace Erdos536

open Finset

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The vector space used for the cap-set input. -/
abbrev CapSpace (H : ℕ) := Fin H → ZMod 3

/-- A finite set contains no affine line with nonzero direction. -/
def AffineLineFree {H : ℕ} (A : Finset (CapSpace H)) : Prop :=
  ∀ x v, v ≠ 0 → x ∈ A → x + v ∈ A → x + v + v ∈ A → False

/-- A nonconstant three-term arithmetic progression in `CapSpace H` is an affine
line, parametrized by the difference between its first two terms. -/
theorem threeAP_is_affineLine {H : ℕ} {a b c : CapSpace H}
    (habc : a + c = b + b) (hab : a ≠ b) :
    ∃ v, v ≠ 0 ∧ b = a + v ∧ c = a + v + v := by
  refine ⟨b - a, sub_ne_zero.mpr hab.symm, ?_, ?_⟩
  · simp
  · calc
      c = (a + c) - a := by abel
      _ = (b + b) - a := by rw [habc]
      _ = a + (b - a) + (b - a) := by abel

/-- Affine-line-freeness implies mathlib's `ThreeAPFree` predicate. -/
theorem AffineLineFree.threeAPFree {H : ℕ} {A : Finset (CapSpace H)}
    (hA : AffineLineFree A) : ThreeAPFree (A : Set (CapSpace H)) := by
  intro a ha b hb c hc habc
  by_contra hab
  obtain ⟨v, hv, hb', hc'⟩ := threeAP_is_affineLine habc hab
  rw [hb'] at hb
  rw [hc'] at hc
  exact hA a v hv ha hb hc

/-- The three points of an affine line with nonzero direction in
`(ZMod 3)^H` are pairwise distinct. -/
theorem affineLine_points_pairwise_ne {H : ℕ} (x v : CapSpace H) (hv : v ≠ 0) :
    x ≠ x + v ∧ x ≠ x + v + v ∧ x + v ≠ x + v + v := by
  have h₁₂ : x ≠ x + v := by
    intro h
    apply hv
    have hzero : (0 : CapSpace H) = v := by
      apply add_left_cancel (a := x)
      simpa using h
    exact hzero.symm
  have h₂₃ : x + v ≠ x + v + v := by
    intro h
    apply hv
    have hzero : (0 : CapSpace H) = v := by
      apply add_left_cancel (a := x + v)
      simpa using h
    exact hzero.symm
  have h₁₃ : x ≠ x + v + v := by
    intro h
    have hvv : v + v = 0 := by
      apply add_left_cancel (a := x)
      simpa [add_assoc] using h.symm
    have hsmul : (2 : ZMod 3) • v = 0 := by
      simpa [two_smul (R := ZMod 3)] using hvv
    have htwo : (2 : ZMod 3) ≠ 0 := by decide
    exact hv ((smul_eq_zero.mp hsmul).resolve_left htwo)
  exact ⟨h₁₂, h₁₃, h₂₃⟩

/-- Qualitative cap-set bound in a suitable dimension. -/
theorem exists_dimension_affineLineFree_card_lt (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ A : Finset (CapSpace H), AffineLineFree A →
      (A.card : ℝ) < ε * (3 : ℝ) ^ H := by
  obtain ⟨H, hH⟩ :=
    pow_unbounded_of_one_lt (cornersTheoremBound ε) (by norm_num : 1 < (3 : ℕ))
  refine ⟨H, fun A hA ↦ ?_⟩
  by_contra hcard
  have hcard' :
      ε * (Fintype.card (CapSpace H) : ℝ) ≤ (A.card : ℝ) := by
    rw [Fintype.card_pi_const, ZMod.card]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using le_of_not_gt hcard
  have hbound : cornersTheoremBound ε ≤ Fintype.card (CapSpace H) := by
    rw [Fintype.card_pi_const, ZMod.card]
    exact hH.le
  exact roth_3ap_theorem ε hε hbound A hcard' hA.threeAPFree

/-- The requested non-strict qualitative cap-set estimate. -/
theorem exists_dimension_affineLineFree_card_le (ε : ℝ) (hε : 0 < ε) :
    ∃ H : ℕ, ∀ A : Finset (CapSpace H), AffineLineFree A →
      (A.card : ℝ) ≤ ε * (3 : ℝ) ^ H := by
  obtain ⟨H, hH⟩ := exists_dimension_affineLineFree_card_lt ε hε
  exact ⟨H, fun A hA ↦ (hH A hA).le⟩

end Erdos536
