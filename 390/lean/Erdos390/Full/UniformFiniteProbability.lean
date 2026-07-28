import Erdos390.Full.FiniteExponentialFamily

/-!
# Uniform probability on an actual finite cell

This is the exact bridge between counting averages on a finite arithmetic
cell and the `FiniteProbability` objects used by the tilt and covariance
modules.  Nonemptiness is explicit, so normalization never divides by a
silently vanishing cell cardinality.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Alpha : Type*}

/-- Uniform probability on the subtype represented by a nonempty finset. -/
def uniformOnFinset (S : Finset Alpha) (hS : S.Nonempty) :
    FiniteProbability S where
  mass := fun _ ↦ 1 / (S.card : ℝ)
  mass_nonneg := fun _ ↦ by positivity
  mass_sum := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have huniv : (Finset.univ : Finset S).card = S.card := by
      rw [Finset.card_univ, Fintype.card_coe]
    rw [huniv]
    have hcard : (S.card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr hS)
    field_simp

@[simp] theorem uniformOnFinset_mass (S : Finset Alpha) (hS : S.Nonempty)
    (x : S) :
    (uniformOnFinset S hS).mass x = 1 / (S.card : ℝ) := rfl

/-- Expectation under the uniform law is the literal subtype sum divided by
the actual cell cardinality. -/
theorem uniformOnFinset_expect_eq (S : Finset Alpha) (hS : S.Nonempty)
    (F : S → ℝ) :
    (uniformOnFinset S hS).expect F =
      (∑ x : S, F x) / (S.card : ℝ) := by
  unfold expect
  calc
    (∑ x : S, (1 / (S.card : ℝ)) * F x) =
        (1 / (S.card : ℝ)) * ∑ x : S, F x := by
      rw [Finset.mul_sum]
    _ = (∑ x : S, F x) / (S.card : ℝ) := by ring

/-- Subtype summation is exactly the usual filtered finset summation. -/
theorem sum_subtype_eq_sum_filter (S : Finset Alpha) (F : Alpha → ℝ) :
    (∑ x : S, F x) = ∑ x ∈ S, F x := by
  exact Finset.sum_coe_sort S F

/-- Expectation written with the ambient function and the literal cell
cardinality. -/
theorem uniformOnFinset_expect_ambient_eq
    (S : Finset Alpha) (hS : S.Nonempty) (F : Alpha → ℝ) :
    (uniformOnFinset S hS).expect (fun x : S ↦ F x) =
      (∑ x ∈ S, F x) / (S.card : ℝ) := by
  rw [uniformOnFinset_expect_eq, sum_subtype_eq_sum_filter]

end FiniteProbability

end

end Erdos390.Full
