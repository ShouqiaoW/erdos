import Mathlib

/-!
# Stable inversion in the literal ordinary raw supremum norm

This elementary connector is deliberately stated in the ambient norm of a
finite raw gauge space.  In the applications that norm is the ordinary
coordinate supremum norm, not the sharp norm obtained after division by a
moving band centre.

The theorem is useful when invertibility has already been obtained (for
example from the independently proved sharp estimate), while a separate
maximum-principle or continuum argument supplies an ordinary inverse estimate
for a reference operator.  It transfers that estimate without changing the
map and without assuming an ordinary inverse as a structure field.
-/

noncomputable section

namespace Erdos390.Full.OrdinaryRawInverseTransfer

variable {V : Type*} [NormedAddCommGroup V] [Module ℝ V]

/-- Absorption of an ordinary-norm operator perturbation.  The equivalence
`e` is retained literally; no replacement operator is constructed. -/
theorem inverse_norm_le_of_reference
    (e : V ≃ₗ[ℝ] V) (reference : V →ₗ[ℝ] V)
    {C delta : ℝ}
    (hC : 0 ≤ C)
    (hsmall : C * delta ≤ 1 / 2)
    (href : ∀ q, ‖q‖ ≤ C * ‖reference q‖)
    (herror : ∀ q, ‖reference q - e q‖ ≤ delta * ‖q‖) :
    ∀ v, ‖e.symm v‖ ≤ (2 * C) * ‖v‖ := by
  intro v
  let q : V := e.symm v
  have heq : e q = v := e.apply_symm_apply v
  have htriangle : ‖reference q‖ ≤
      ‖e q‖ + ‖reference q - e q‖ := by
    calc
      ‖reference q‖ = ‖e q + (reference q - e q)‖ := by
        congr 1
        abel
      _ ≤ ‖e q‖ + ‖reference q - e q‖ :=
        norm_add_le (e q) (reference q - e q)
  have hpert : C * ‖reference q - e q‖ ≤
      (C * delta) * ‖q‖ := by
    calc
      C * ‖reference q - e q‖ ≤ C * (delta * ‖q‖) :=
        mul_le_mul_of_nonneg_left (herror q) hC
      _ = (C * delta) * ‖q‖ := by ring
  have habsorb : (C * delta) * ‖q‖ ≤ (1 / 2) * ‖q‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg q)
  have hq : ‖q‖ ≤ C * ‖v‖ + (1 / 2) * ‖q‖ := by
    calc
      ‖q‖ ≤ C * ‖reference q‖ := href q
      _ ≤ C * (‖e q‖ + ‖reference q - e q‖) :=
        mul_le_mul_of_nonneg_left htriangle hC
      _ = C * ‖e q‖ + C * ‖reference q - e q‖ := by ring
      _ ≤ C * ‖e q‖ + (C * delta) * ‖q‖ :=
        add_le_add le_rfl hpert
      _ = C * ‖v‖ + (C * delta) * ‖q‖ := by rw [heq]
      _ ≤ C * ‖v‖ + (1 / 2) * ‖q‖ :=
        add_le_add le_rfl habsorb
  change ‖q‖ ≤ (2 * C) * ‖v‖
  linarith

end Erdos390.Full.OrdinaryRawInverseTransfer
