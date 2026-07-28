import Mathlib

/-!
# The finite algebra behind Lemma 8.6

This file isolates the parts of the compensated-score argument which are genuinely
finite-dimensional.  In particular, none of the estimates below hides a limiting
or uniformity assertion: all analytic estimates enter as explicit hypotheses.
-/

open scoped BigOperators

namespace Erdos390

section CompensatedCoefficientLedger

variable {P J : Type*} [Fintype P]

/-- Subtracting a bandwise regression coefficient preserves the three coefficient
norms needed in the compensated-score argument, with the displayed constants.

The hypotheses deliberately keep the raw-score and regression ledgers separate.
Thus applications must prove the weighted `L¹` and `L²` estimates at the scale at
which they are actually used; an additive `o(1)` cannot silently replace a
row-relative bound here. -/
theorem compensated_coefficient_norm_ledger
    (band : P → J) (ρ g : P → ℝ) (q : J → ℝ)
    (w Gsup Qsup G₁ Q₁ G₂ Q₂ : ℝ)
    (hρ : ∀ p, 0 ≤ ρ p)
    (hgSup : ∀ p, |g p| ≤ Gsup * w)
    (hqSup : ∀ p, |q (band p)| ≤ Qsup * w)
    (hg₁ : ∑ p, ρ p * |g p| ≤ G₁ * w)
    (hq₁ : ∑ p, ρ p * |q (band p)| ≤ Q₁ * w)
    (hg₂ : ∑ p, ρ p * (g p) ^ 2 ≤ G₂ * w ^ 2)
    (hq₂ : ∑ p, ρ p * (q (band p)) ^ 2 ≤ Q₂ * w ^ 2) :
    (∀ p, |g p - q (band p)| ≤ (Gsup + Qsup) * w) ∧
      (∑ p, ρ p * |g p - q (band p)| ≤ (G₁ + Q₁) * w) ∧
      (∑ p, ρ p * (g p - q (band p)) ^ 2 ≤ 2 * (G₂ + Q₂) * w ^ 2) := by
  constructor
  · intro p
    calc
      |g p - q (band p)| ≤ |g p| + |q (band p)| := abs_sub _ _
      _ ≤ Gsup * w + Qsup * w := add_le_add (hgSup p) (hqSup p)
      _ = (Gsup + Qsup) * w := by ring
  constructor
  · calc
      ∑ p, ρ p * |g p - q (band p)|
          ≤ ∑ p, (ρ p * |g p| + ρ p * |q (band p)|) := by
            apply Finset.sum_le_sum
            intro p _
            calc
              ρ p * |g p - q (band p)|
                  ≤ ρ p * (|g p| + |q (band p)|) :=
                    mul_le_mul_of_nonneg_left (abs_sub (g p) (q (band p))) (hρ p)
              _ = ρ p * |g p| + ρ p * |q (band p)| := by ring
      _ = (∑ p, ρ p * |g p|) + ∑ p, ρ p * |q (band p)| :=
        Finset.sum_add_distrib
      _ ≤ G₁ * w + Q₁ * w := add_le_add hg₁ hq₁
      _ = (G₁ + Q₁) * w := by ring
  · calc
      ∑ p, ρ p * (g p - q (band p)) ^ 2
          ≤ ∑ p, (2 * (ρ p * (g p) ^ 2) + 2 * (ρ p * (q (band p)) ^ 2)) := by
            apply Finset.sum_le_sum
            intro p _
            have hsquare : (g p - q (band p)) ^ 2 ≤
                2 * (g p) ^ 2 + 2 * (q (band p)) ^ 2 := by
              nlinarith [sq_nonneg (g p + q (band p))]
            calc
              ρ p * (g p - q (band p)) ^ 2
                  ≤ ρ p * (2 * (g p) ^ 2 + 2 * (q (band p)) ^ 2) :=
                    mul_le_mul_of_nonneg_left hsquare (hρ p)
              _ = 2 * (ρ p * (g p) ^ 2) + 2 * (ρ p * (q (band p)) ^ 2) := by ring
      _ = 2 * (∑ p, ρ p * (g p) ^ 2) +
          2 * (∑ p, ρ p * (q (band p)) ^ 2) := by
            simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 2 * (G₂ * w ^ 2) + 2 * (Q₂ * w ^ 2) := by linarith
      _ = 2 * (G₂ + Q₂) * w ^ 2 := by ring

end CompensatedCoefficientLedger

section SequentialSchurRegression

variable {Q Z : Type*} [AddCommGroup Q] [Module ℝ Q]
  [AddCommGroup Z] [Module ℝ Z]

/-- The sequential Schur-complement solve really solves the original joint block
system.  This is the algebra used when the nuisance coordinates are eliminated
first and the band coordinates are regressed second. -/
theorem sequential_schur_regression
    (C : Q →ₗ[ℝ] Q) (U : Z →ₗ[ℝ] Q) (Ut : Q →ₗ[ℝ] Z)
    (Γ : Z ≃ₗ[ℝ] Z) (bQ : Q) (bZ : Z) (q : Q) (a : Z)
    (hschur : C q - U (Γ.symm (Ut q)) = bQ - U (Γ.symm bZ))
    (ha : a = Γ.symm (bZ - Ut q)) :
    C q + U a = bQ ∧ Ut q + Γ a = bZ := by
  constructor
  · calc
      C q + U a
          = (C q - U (Γ.symm (Ut q))) + U (Γ.symm bZ) := by
              simp only [ha, map_sub]
              abel
      _ = (bQ - U (Γ.symm bZ)) + U (Γ.symm bZ) := by rw [hschur]
      _ = bQ := sub_add_cancel _ _
  · rw [ha, Γ.apply_symm_apply]
    abel

end SequentialSchurRegression

section RelativeErrorLedger

/-- A leading `w²` Schur gap survives a relative error.  The conclusion records
both sides because both are used in the nonlinear-fit inverse estimates. -/
theorem relative_schur_gap
    (leading full w lower upper ε : ℝ)
    (hleadingLower : lower * w ^ 2 ≤ leading)
    (hleadingUpper : leading ≤ upper * w ^ 2)
    (herror : |full - leading| ≤ ε * w ^ 2)
    (hsmall : 2 * ε ≤ lower) :
    (lower / 2) * w ^ 2 ≤ full ∧ full ≤ (upper + ε) * w ^ 2 := by
  have hminus : -(ε * w ^ 2) ≤ full - leading := neg_le_of_abs_le herror
  have hplus : full - leading ≤ ε * w ^ 2 := le_of_abs_le herror
  constructor <;> nlinarith [sq_nonneg w]

/-- A marked covariance row remains of size `O(w ρ)` after adding a relative
prime-power transfer error. -/
theorem marked_row_transfer
    (squarefree full w ρ Cmain Cerror : ℝ)
    (hmain : |squarefree| ≤ Cmain * w * ρ)
    (herror : |full - squarefree| ≤ Cerror * w * ρ) :
    |full| ≤ (Cmain + Cerror) * w * ρ := by
  calc
    |full| = |squarefree + (full - squarefree)| := by ring_nf
    _ ≤ |squarefree| + |full - squarefree| := abs_add_le _ _
    _ ≤ Cmain * w * ρ + Cerror * w * ρ := add_le_add hmain herror
    _ = (Cmain + Cerror) * w * ρ := by ring

end RelativeErrorLedger

end Erdos390
