import Erdos390.Full.PrimePowerCovariance

/-!
# Exact finite tagged probability mixtures

The covariance of a mixture is not the mixture of the covariances.  This
module therefore starts one level lower: expectations on a tagged sigma
type are proved to be exact convex combinations.  Common-profile estimates
can then be averaged before any covariance subtraction is performed.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]

/-- The exact probability law on the tagged disjoint union. -/
def sigmaMixture (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c)) :
    FiniteProbability (Sigma Omega) where
  mass x := weight.mass x.1 * (mu x.1).mass x.2
  mass_nonneg x := mul_nonneg (weight.mass_nonneg x.1)
    ((mu x.1).mass_nonneg x.2)
  mass_sum := by
    rw [Fintype.sum_sigma]
    calc
      (∑ c, ∑ x, weight.mass c * (mu c).mass x) =
          ∑ c, weight.mass c * ∑ x, (mu c).mass x := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
      _ = ∑ c, weight.mass c := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [(mu c).mass_sum, mul_one]
      _ = 1 := weight.mass_sum

theorem sigmaMixture_expect
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) :
    (sigmaMixture weight mu).expect F =
      ∑ c, weight.mass c * (mu c).expect (fun x ↦ F ⟨c, x⟩) := by
  unfold sigmaMixture expect
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- A common centered expectation error survives an arbitrary convex
mixture with exactly the same error. -/
theorem abs_sigmaMixture_expect_sub_common_le
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) (main error : ℝ)
    (hcell : ∀ c,
      |(mu c).expect (fun x ↦ F ⟨c, x⟩) - main| ≤ error) :
    |(sigmaMixture weight mu).expect F - main| ≤ error := by
  rw [sigmaMixture_expect]
  have hrewrite :
      (∑ c, weight.mass c * (mu c).expect (fun x ↦ F ⟨c, x⟩)) -
          main =
        ∑ c, weight.mass c *
          ((mu c).expect (fun x ↦ F ⟨c, x⟩) - main) := by
    calc
      _ = (∑ c, weight.mass c *
            (mu c).expect (fun x ↦ F ⟨c, x⟩)) -
          (∑ c, weight.mass c) * main := by rw [weight.mass_sum, one_mul]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c hc
        ring
  rw [hrewrite]
  calc
    |∑ c, weight.mass c *
        ((mu c).expect (fun x ↦ F ⟨c, x⟩) - main)| ≤
        ∑ c, |weight.mass c *
          ((mu c).expect (fun x ↦ F ⟨c, x⟩) - main)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, weight.mass c * error := by
      apply Finset.sum_le_sum
      intro c hc
      rw [abs_mul, abs_of_nonneg (weight.mass_nonneg c)]
      exact mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = error := by
      rw [← Finset.sum_mul, weight.mass_sum, one_mul]

/-- A common nonnegative expectation upper bound also survives convex
mixing unchanged. -/
theorem sigmaMixture_expect_le_common
    (weight : FiniteProbability Cell)
    (mu : ∀ c, FiniteProbability (Omega c))
    (F : Sigma Omega → ℝ) (upper : ℝ)
    (hcell : ∀ c,
      (mu c).expect (fun x ↦ F ⟨c, x⟩) ≤ upper) :
    (sigmaMixture weight mu).expect F ≤ upper := by
  rw [sigmaMixture_expect]
  calc
    _ ≤ ∑ c, weight.mass c * upper := by
      exact Finset.sum_le_sum fun c hc ↦
        mul_le_mul_of_nonneg_left (hcell c) (weight.mass_nonneg c)
    _ = upper := by rw [← Finset.sum_mul, weight.mass_sum, one_mul]

end FiniteProbability

namespace PrimePowerCovariance.BoundedValuationLaw

open ArithmeticModel

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- Regard the same law as bounded by a larger common endpoint.  All
statistics are definitionally unchanged. -/
def widen {Omega₀ : Type*} [Fintype Omega₀] {M₀ M₁ : ℕ}
    (law : BoundedValuationLaw Omega₀ M₀) (hM : M₀ ≤ M₁) :
    BoundedValuationLaw Omega₀ M₁ where
  probability := law.probability
  value := law.value
  value_pos := law.value_pos
  value_le omega := (law.value_le omega).trans hM

@[simp] theorem widen_probability
    {Omega₀ : Type*} [Fintype Omega₀] {M₀ M₁ : ℕ}
    (law : BoundedValuationLaw Omega₀ M₀) (hM : M₀ ≤ M₁) :
    (widen law hM).probability = law.probability := rfl

@[simp] theorem widen_value
    {Omega₀ : Type*} [Fintype Omega₀] {M₀ M₁ : ℕ}
    (law : BoundedValuationLaw Omega₀ M₀) (hM : M₀ ≤ M₁)
    (omega : Omega₀) :
    (widen law hM).value omega = law.value omega := rfl

/-- A tagged mixture of bounded valuation laws with a common endpoint. -/
def sigmaMixture (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M) :
    BoundedValuationLaw (Sigma Omega) M where
  probability := FiniteProbability.sigmaMixture weight
    (fun c ↦ (law c).probability)
  value x := (law x.1).value x.2
  value_pos x := (law x.1).value_pos x.2
  value_le x := (law x.1).value_le x.2

/-- Tagged mixture for component laws which originally carry different
endpoints, after proof that one common endpoint dominates all of them. -/
def sigmaMixtureVarying
    (endpoint : Cell → ℕ) (common : ℕ)
    (hendpoint : ∀ c, endpoint c ≤ common)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) (endpoint c)) :
    BoundedValuationLaw (Sigma Omega) common :=
  sigmaMixture weight (fun c ↦ widen (law c) (hendpoint c))

@[simp] theorem sigmaMixtureVarying_value
    (endpoint : Cell → ℕ) (common : ℕ)
    (hendpoint : ∀ c, endpoint c ≤ common)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) (endpoint c))
    (x : Sigma Omega) :
    (sigmaMixtureVarying endpoint common hendpoint weight law).value x =
      (law x.1).value x.2 := rfl

@[simp] theorem sigmaMixture_value
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    (x : Sigma Omega) :
    (sigmaMixture weight law).value x = (law x.1).value x.2 := rfl

/-- Divisibility probabilities of the tagged law inherit a common profile
estimate before covariance is formed.  This is the step which accounts for
the between-cell covariance term: it is deliberately an expectation
statement, not an average-of-covariances statement. -/
theorem abs_sigmaMixture_expect_divInd_sub_common_le
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    (D : ℕ) (main error : ℝ)
    (hcell : ∀ c,
      |(law c).probability.expect
          (fun x ↦ divInd D ((law c).value x)) - main| ≤ error) :
    |(sigmaMixture weight law).probability.expect
          (fun x ↦ divInd D ((sigmaMixture weight law).value x)) - main| ≤
      error := by
  exact FiniteProbability.abs_sigmaMixture_expect_sub_common_le
    weight (fun c ↦ (law c).probability)
      (fun x ↦ divInd D ((law x.1).value x.2)) main error hcell

/-- A common reciprocal fallback estimate also survives the tagged
mixture, again at expectation level. -/
theorem sigmaMixture_expect_divInd_le_common
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    (D : ℕ) (upper : ℝ)
    (hcell : ∀ c,
      (law c).probability.expect
        (fun x ↦ divInd D ((law c).value x)) ≤ upper) :
    (sigmaMixture weight law).probability.expect
        (fun x ↦ divInd D ((sigmaMixture weight law).value x)) ≤ upper := by
  exact FiniteProbability.sigmaMixture_expect_le_common
    weight (fun c ↦ (law c).probability)
      (fun x ↦ divInd D ((law x.1).value x.2)) upper hcell

end PrimePowerCovariance.BoundedValuationLaw

end

end Erdos390.Full
