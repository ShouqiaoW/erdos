import Mathlib

/-!
# The finite algebraic core of Lemma 7.5

This file formalizes the part of Lemma 7.5 which is independent of the
marked-friable asymptotics.  The analytic estimates enter only as explicit
hypotheses.  The reciprocal weight `u i` is instantiated in the paper by
`1 / p`, `rowScale i` by `p`, and `invW` by `1 / W`.
-/

open scoped BigOperators

namespace Erdos390.Lemma75

/-- A probability distribution on a finite type, kept in `ℝ` so that all
expectation and covariance identities reduce to finite-sum algebra. -/
structure FiniteProbability (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ ω, 0 ≤ mass ω
  mass_sum : ∑ ω, mass ω = 1

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

def expect (μ : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * X ω

def covariance (μ : FiniteProbability Ω) (X Y : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => X ω * Y ω) - μ.expect X * μ.expect Y

def variance (μ : FiniteProbability Ω) (X : Ω → ℝ) : ℝ :=
  μ.covariance X X

@[simp] theorem expect_zero (μ : FiniteProbability Ω) :
    μ.expect (fun _ => 0) = 0 := by
  simp [expect]

theorem expect_add (μ : FiniteProbability Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω + Y ω) = μ.expect X + μ.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteProbability Ω) (X Y : Ω → ℝ) :
    μ.expect (fun ω => X ω - Y ω) = μ.expect X - μ.expect Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_const_mul (μ : FiniteProbability Ω) (c : ℝ) (X : Ω → ℝ) :
    μ.expect (fun ω => c * X ω) = c * μ.expect X := by
  simp only [expect]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  ring_nf

@[simp] theorem expect_const (μ : FiniteProbability Ω) (c : ℝ) :
    μ.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, μ.mass_sum]

theorem expect_nonneg (μ : FiniteProbability Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expect X := by
  apply Finset.sum_nonneg
  intro ω hω
  exact mul_nonneg (μ.mass_nonneg ω) (hX ω)

theorem expect_mono (μ : FiniteProbability Ω) {X Y : Ω → ℝ}
    (hXY : ∀ ω, X ω ≤ Y ω) : μ.expect X ≤ μ.expect Y := by
  apply Finset.sum_le_sum
  intro ω hω
  exact mul_le_mul_of_nonneg_left (hXY ω) (μ.mass_nonneg ω)

theorem covariance_congr (μ : FiniteProbability Ω) {X X' Y Y' : Ω → ℝ}
    (hX : X = X') (hY : Y = Y') : μ.covariance X Y = μ.covariance X' Y' := by
  subst X'
  subst Y'
  rfl

theorem covariance_symm (μ : FiniteProbability Ω) (X Y : Ω → ℝ) :
    μ.covariance X Y = μ.covariance Y X := by
  simp only [covariance]
  congr 1
  · apply congrArg μ.expect
    funext ω
    ring
  · ring

theorem covariance_add_left (μ : FiniteProbability Ω) (X Y Z : Ω → ℝ) :
    μ.covariance (fun ω => X ω + Y ω) Z =
      μ.covariance X Z + μ.covariance Y Z := by
  simp only [covariance, expect_add]
  rw [show (fun ω => (X ω + Y ω) * Z ω) =
      (fun ω => X ω * Z ω + Y ω * Z ω) by
        funext ω
        ring]
  rw [expect_add]
  ring

theorem covariance_add_right (μ : FiniteProbability Ω) (X Y Z : Ω → ℝ) :
    μ.covariance X (fun ω => Y ω + Z ω) =
      μ.covariance X Y + μ.covariance X Z := by
  rw [μ.covariance_symm X (fun ω => Y ω + Z ω)]
  rw [μ.covariance_add_left Y Z X]
  rw [μ.covariance_symm Y X, μ.covariance_symm Z X]

theorem covariance_const_mul_left (μ : FiniteProbability Ω)
    (c : ℝ) (X Y : Ω → ℝ) :
    μ.covariance (fun ω => c * X ω) Y = c * μ.covariance X Y := by
  simp only [covariance, expect_const_mul]
  rw [show (fun ω => (c * X ω) * Y ω) =
      (fun ω => c * (X ω * Y ω)) by
        funext ω
        ring]
  rw [expect_const_mul]
  ring

theorem covariance_const_mul_right (μ : FiniteProbability Ω)
    (c : ℝ) (X Y : Ω → ℝ) :
    μ.covariance X (fun ω => c * Y ω) = c * μ.covariance X Y := by
  rw [μ.covariance_symm X (fun ω => c * Y ω)]
  rw [μ.covariance_const_mul_left c Y X]
  rw [μ.covariance_symm Y X]

theorem covariance_sum_left {ι : Type*} (μ : FiniteProbability Ω)
    (s : Finset ι) (X : ι → Ω → ℝ) (Y : Ω → ℝ) :
    μ.covariance (fun ω => ∑ i ∈ s, X i ω) Y =
      ∑ i ∈ s, μ.covariance (X i) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [covariance]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      rw [show (fun ω => X a ω + ∑ i ∈ s, X i ω) =
          (fun ω => X a ω + (fun ω => ∑ i ∈ s, X i ω) ω) by rfl]
      rw [μ.covariance_add_left, ih]

theorem covariance_sum_right {ι : Type*} (μ : FiniteProbability Ω)
    (s : Finset ι) (X : Ω → ℝ) (Y : ι → Ω → ℝ) :
    μ.covariance X (fun ω => ∑ i ∈ s, Y i ω) =
      ∑ i ∈ s, μ.covariance X (Y i) := by
  rw [μ.covariance_symm X (fun ω => ∑ i ∈ s, Y i ω)]
  rw [μ.covariance_sum_left s Y X]
  apply Finset.sum_congr rfl
  intro i hi
  exact μ.covariance_symm (Y i) X

theorem covariance_weighted_sum_left {ι : Type*} (μ : FiniteProbability Ω)
    (s : Finset ι) (a : ι → ℝ) (X : ι → Ω → ℝ) (Y : Ω → ℝ) :
    μ.covariance (fun ω => ∑ i ∈ s, a i * X i ω) Y =
      ∑ i ∈ s, a i * μ.covariance (X i) Y := by
  rw [μ.covariance_sum_left s (fun i ω => a i * X i ω) Y]
  apply Finset.sum_congr rfl
  intro i hi
  exact μ.covariance_const_mul_left (a i) (X i) Y

theorem covariance_weighted_sum_right {ι : Type*} (μ : FiniteProbability Ω)
    (s : Finset ι) (a : ι → ℝ) (X : Ω → ℝ) (Y : ι → Ω → ℝ) :
    μ.covariance X (fun ω => ∑ i ∈ s, a i * Y i ω) =
      ∑ i ∈ s, a i * μ.covariance X (Y i) := by
  rw [μ.covariance_sum_right s X (fun i ω => a i * Y i ω)]
  apply Finset.sum_congr rfl
  intro i hi
  exact μ.covariance_const_mul_right (a i) X (Y i)

theorem variance_weighted_sum {ι : Type*} (μ : FiniteProbability Ω)
    (s : Finset ι) (a : ι → ℝ) (X : ι → Ω → ℝ) :
    μ.variance (fun ω => ∑ i ∈ s, a i * X i ω) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * μ.covariance (X i) (X j) := by
  simp only [variance]
  rw [μ.covariance_weighted_sum_left]
  apply Finset.sum_congr rfl
  intro i hi
  rw [μ.covariance_weighted_sum_right]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem variance_difference_expansion {ι : Type*} (μ : FiniteProbability Ω)
    (s : Finset ι) (a : ι → ℝ) (X Y : ι → Ω → ℝ) :
    μ.variance (fun ω => ∑ i ∈ s, a i * X i ω) -
        μ.variance (fun ω => ∑ i ∈ s, a i * Y i ω) =
      ∑ i ∈ s, ∑ j ∈ s,
        a i * a j * (μ.covariance (X i) (X j) -
          μ.covariance (Y i) (Y j)) := by
  rw [μ.variance_weighted_sum, μ.variance_weighted_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem variance_eq_centered_square (μ : FiniteProbability Ω) (X : Ω → ℝ) :
    μ.variance X = μ.expect (fun ω => (X ω - μ.expect X) ^ 2) := by
  let c := μ.expect X
  rw [show (fun ω => (X ω - μ.expect X) ^ 2) =
      (fun ω => X ω ^ 2 + (-2 * c) * X ω + c ^ 2) by
        funext ω
        dsimp [c]
        ring]
  rw [μ.expect_add, μ.expect_add, μ.expect_const_mul, μ.expect_const]
  simp only [variance, covariance]
  dsimp [c]
  ring_nf

theorem variance_nonneg (μ : FiniteProbability Ω) (X : Ω → ℝ) :
    0 ≤ μ.variance X := by
  rw [μ.variance_eq_centered_square]
  exact μ.expect_nonneg (fun ω => sq_nonneg (X ω - μ.expect X))

end FiniteProbability

section PrimePowerAlgebra

variable {Ω ι κ : Type*} [Fintype Ω]

/-- The contribution of the higher prime powers at one prime.  In the
application `powers i` is the finite set of exponents `k ≥ 2` which can
occur in the structured cell. -/
def highPart (powers : ι → Finset κ) (X : ι → κ → Ω → ℝ)
    (i : ι) (ω : Ω) : ℝ :=
  ∑ k ∈ powers i, X i k ω

/-- Full valuation column = squarefree column + higher-power column. -/
def fullPart (I : ι → Ω → ℝ) (powers : ι → Finset κ)
    (X : ι → κ → Ω → ℝ) (i : ι) (ω : Ω) : ℝ :=
  I i ω + highPart powers X i ω

theorem abs_covariance_high_base_le (μ : FiniteProbability Ω)
    (powers : ι → Finset κ) (X : ι → κ → Ω → ℝ)
    (I : ι → Ω → ℝ) (i j : ι) :
    |μ.covariance (highPart powers X i) (I j)| ≤
      ∑ k ∈ powers i, |μ.covariance (X i k) (I j)| := by
  classical
  change |μ.covariance (fun ω => ∑ k ∈ powers i, X i k ω) (I j)| ≤ _
  rw [μ.covariance_sum_left]
  exact Finset.abs_sum_le_sum_abs _ _

theorem abs_covariance_base_high_le (μ : FiniteProbability Ω)
    (powers : ι → Finset κ) (X : ι → κ → Ω → ℝ)
    (I : ι → Ω → ℝ) (i j : ι) :
    |μ.covariance (I i) (highPart powers X j)| ≤
      ∑ l ∈ powers j, |μ.covariance (I i) (X j l)| := by
  classical
  change |μ.covariance (I i) (fun ω => ∑ l ∈ powers j, X j l ω)| ≤ _
  rw [μ.covariance_sum_right]
  exact Finset.abs_sum_le_sum_abs _ _

theorem abs_covariance_high_high_le (μ : FiniteProbability Ω)
    (powers : ι → Finset κ) (X : ι → κ → Ω → ℝ)
    (i j : ι) :
    |μ.covariance (highPart powers X i) (highPart powers X j)| ≤
      ∑ k ∈ powers i, ∑ l ∈ powers j,
        |μ.covariance (X i k) (X j l)| := by
  classical
  change |μ.covariance (fun ω => ∑ k ∈ powers i, X i k ω)
      (highPart powers X j)| ≤ _
  rw [μ.covariance_sum_left]
  calc
    |∑ k ∈ powers i, μ.covariance (X i k) (highPart powers X j)| ≤
        ∑ k ∈ powers i,
          |μ.covariance (X i k) (highPart powers X j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ powers i, ∑ l ∈ powers j,
          |μ.covariance (X i k) (X j l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact abs_covariance_base_high_le μ powers X
        (fun _ => X i k) i j

theorem covariance_full_difference (μ : FiniteProbability Ω)
    (I J : ι → Ω → ℝ) (i j : ι) :
    μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I j ω + J j ω) -
        μ.covariance (I i) (I j) =
      μ.covariance (J i) (I j) +
        μ.covariance (I i) (J j) +
        μ.covariance (J i) (J j) := by
  rw [μ.covariance_add_left, μ.covariance_add_right,
    μ.covariance_add_right]
  ring

theorem abs_covariance_full_difference_le (μ : FiniteProbability Ω)
    (I J : ι → Ω → ℝ) (i j : ι) :
    |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I j ω + J j ω) -
        μ.covariance (I i) (I j)| ≤
      |μ.covariance (J i) (I j)| +
        |μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)| := by
  rw [covariance_full_difference μ I J i j]
  calc
    |μ.covariance (J i) (I j) + μ.covariance (I i) (J j) +
        μ.covariance (J i) (J j)| ≤
      |μ.covariance (J i) (I j) + μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)| := abs_add_le _ _
    _ ≤ |μ.covariance (J i) (I j)| +
        |μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)| := by
      linarith [abs_add_le (μ.covariance (J i) (I j))
        (μ.covariance (I i) (J j))]

/-- The diagonal estimate used in Lemma 7.5.  Its assumptions are the
pointwise identities of a squarefree indicator `I` and its nonnegative
higher-power part `J`. -/
theorem diagonal_difference_le_three_secondMoment
    (μ : FiniteProbability Ω) (I J : Ω → ℝ)
    (hI0 : ∀ ω, 0 ≤ I ω) (hI1 : ∀ ω, I ω ≤ 1)
    (hJ0 : ∀ ω, 0 ≤ J ω) (hJsq : ∀ ω, J ω ≤ J ω ^ 2)
    (hIJ : ∀ ω, I ω * J ω = J ω) :
    |μ.covariance (fun ω => I ω + J ω) (fun ω => I ω + J ω) -
        μ.covariance I I| ≤ 3 * μ.expect (fun ω => J ω ^ 2) := by
  have hEI0 : 0 ≤ μ.expect I := μ.expect_nonneg hI0
  have hEI1 : μ.expect I ≤ 1 := by
    calc
      μ.expect I ≤ μ.expect (fun _ => 1) := μ.expect_mono hI1
      _ = 1 := μ.expect_const 1
  have hEJ0 : 0 ≤ μ.expect J := μ.expect_nonneg hJ0
  have hEJsq0 : 0 ≤ μ.expect (fun ω => J ω ^ 2) :=
    μ.expect_nonneg (fun ω => sq_nonneg (J ω))
  have hEJle : μ.expect J ≤ μ.expect (fun ω => J ω ^ 2) :=
    μ.expect_mono hJsq
  have hcovIJ : μ.covariance I J = μ.expect J * (1 - μ.expect I) := by
    simp only [FiniteProbability.covariance]
    rw [show (fun ω => I ω * J ω) = J by
      funext ω
      exact hIJ ω]
    ring
  have hcovIJ0 : 0 ≤ μ.covariance I J := by
    rw [hcovIJ]
    exact mul_nonneg hEJ0 (by linarith)
  have hcovIJle : μ.covariance I J ≤ μ.expect (fun ω => J ω ^ 2) := by
    rw [hcovIJ]
    have hfactor : 0 ≤ 1 - μ.expect I := by linarith
    have hfactor1 : 1 - μ.expect I ≤ 1 := by linarith
    calc
      μ.expect J * (1 - μ.expect I) ≤ μ.expect J * 1 :=
        mul_le_mul_of_nonneg_left hfactor1 hEJ0
      _ = μ.expect J := by ring
      _ ≤ μ.expect (fun ω => J ω ^ 2) := hEJle
  have hvarJ0 : 0 ≤ μ.variance J := μ.variance_nonneg J
  have hvarJle : μ.variance J ≤ μ.expect (fun ω => J ω ^ 2) := by
    simp only [FiniteProbability.variance, FiniteProbability.covariance]
    rw [show (fun ω => J ω * J ω) = (fun ω => J ω ^ 2) by
      funext ω
      ring]
    exact sub_le_self _ (mul_self_nonneg (μ.expect J))
  have hdiag :
      μ.covariance (fun ω => I ω + J ω) (fun ω => I ω + J ω) -
          μ.covariance I I = 2 * μ.covariance I J + μ.variance J := by
    rw [μ.covariance_add_left, μ.covariance_add_right,
      μ.covariance_add_right, μ.covariance_symm J I]
    simp only [FiniteProbability.variance]
    ring
  rw [hdiag, abs_of_nonneg]
  · linarith
  · nlinarith

end PrimePowerAlgebra

section FiniteContraction

variable {Ω ι κ : Type*} [Fintype Ω]

theorem offDiagonal_sum_le_product [DecidableEq ι]
    (P : Finset ι) (a c : ι → ℝ)
    (ha : ∀ i ∈ P, 0 ≤ a i) (hc : ∀ i ∈ P, 0 ≤ c i) :
    (∑ i ∈ P, ∑ j ∈ P.erase i, a i * c j) ≤
      (∑ i ∈ P, a i) * (∑ j ∈ P, c j) := by
  calc
    (∑ i ∈ P, ∑ j ∈ P.erase i, a i * c j) ≤
        ∑ i ∈ P, ∑ j ∈ P, a i * c j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i P)
      intro j hjP hjErase
      exact mul_nonneg (ha i hi) (hc j hjP)
    _ = (∑ i ∈ P, a i) * (∑ j ∈ P, c j) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]

/-- Product-weighted contraction on the off-diagonal.  This is the finite
sum mechanism behind each of the `JI`, `IJ`, and `JJ` contractions. -/
theorem offDiagonal_contraction [DecidableEq ι]
    (P : Finset ι) (a c : ι → ℝ) (q r : ι → ι → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (ha : ∀ i ∈ P, 0 ≤ a i)
    (hc : ∀ j ∈ P, 0 ≤ c j)
    (hq : ∀ i ∈ P, ∀ j ∈ P.erase i,
      q i j ≤ C * a i * c j + r i j) :
    (∑ i ∈ P, ∑ j ∈ P.erase i, q i j) ≤
      C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by
  calc
    (∑ i ∈ P, ∑ j ∈ P.erase i, q i j) ≤
        ∑ i ∈ P, ∑ j ∈ P.erase i,
          (C * a i * c j + r i j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hq i hi j hj
    _ = C * (∑ i ∈ P, ∑ j ∈ P.erase i, a i * c j) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≤ C * ((∑ i ∈ P, a i) * (∑ j ∈ P, c j)) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by
      gcongr
      exact offDiagonal_sum_le_product P a c ha hc
    _ = C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by ring

theorem offDiagonal_two_contraction [DecidableEq ι]
    (P : Finset ι) (a c d e : ι → ℝ) (q r : ι → ι → ℝ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (ha : ∀ i ∈ P, 0 ≤ a i) (hc : ∀ j ∈ P, 0 ≤ c j)
    (hd : ∀ i ∈ P, 0 ≤ d i) (he : ∀ j ∈ P, 0 ≤ e j)
    (hq : ∀ i ∈ P, ∀ j ∈ P.erase i,
      q i j ≤ C * a i * c j + ε * d i * e j + r i j) :
    (∑ i ∈ P, ∑ j ∈ P.erase i, q i j) ≤
      C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
      ε * (∑ i ∈ P, d i) * (∑ j ∈ P, e j) +
      ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by
  have hfirst := offDiagonal_contraction P a c q
    (fun i j => ε * d i * e j + r i j) C hC ha hc
    (fun i hi j hj => by
      have h := hq i hi j hj
      linarith)
  calc
    (∑ i ∈ P, ∑ j ∈ P.erase i, q i j) ≤
        C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
          ∑ i ∈ P, ∑ j ∈ P.erase i, (ε * d i * e j + r i j) := hfirst
    _ = C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
        ε * (∑ i ∈ P, ∑ j ∈ P.erase i, d i * e j) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
      ring_nf
    _ ≤ C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
        ε * ((∑ i ∈ P, d i) * (∑ j ∈ P, e j)) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by
      gcongr
      exact offDiagonal_sum_le_product P d e hd he
    _ = C * (∑ i ∈ P, a i) * (∑ j ∈ P, c j) +
        ε * (∑ i ∈ P, d i) * (∑ j ∈ P, e j) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, r i j := by ring

theorem sum_mul_sq_weight_le [DecidableEq ι]
    (P : Finset ι) (u a : ι → ℝ) (invW : ℝ)
    (hu0 : ∀ i ∈ P, 0 ≤ u i) (huW : ∀ i ∈ P, u i ≤ invW)
    (ha0 : ∀ i ∈ P, 0 ≤ a i) :
    (∑ i ∈ P, a i * u i ^ 2) ≤
      invW * ∑ i ∈ P, a i * u i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hui : u i ^ 2 ≤ invW * u i := by
    nlinarith [hu0 i hi, huW i hi]
  calc
    a i * u i ^ 2 ≤ a i * (invW * u i) :=
      mul_le_mul_of_nonneg_left hui (ha0 i hi)
    _ = invW * (a i * u i) := by ring

theorem sum_t_abs_le_sum_abs [DecidableEq ι]
    (P : Finset ι) (t b u : ι → ℝ)
    (ht1 : ∀ i ∈ P, t i ≤ 1)
    (hu0 : ∀ i ∈ P, 0 ≤ u i) :
    (∑ i ∈ P, t i * |b i| * u i) ≤
      ∑ i ∈ P, |b i| * u i := by
  apply Finset.sum_le_sum
  intro i hi
  have habs : 0 ≤ |b i| := abs_nonneg _
  have hbu : 0 ≤ |b i| * u i := mul_nonneg habs (hu0 i hi)
  calc
    t i * |b i| * u i = t i * (|b i| * u i) := by ring
    _ ≤ 1 * (|b i| * u i) :=
      mul_le_mul_of_nonneg_right (ht1 i hi) hbu
    _ = |b i| * u i := by ring

theorem two_product_add_square_le (x y M r : ℝ)
    (hy0 : 0 ≤ y) (hM0 : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : x ≤ M) (hy : y ≤ r * M) :
    2 * x * y + y ^ 2 ≤ 3 * r * M ^ 2 := by
  have hrM0 : 0 ≤ r * M := mul_nonneg hr0 hM0
  have hxy : x * y ≤ M * (r * M) := mul_le_mul hx hy hy0 hM0
  have hyy : y ^ 2 ≤ (r * M) ^ 2 := (sq_le_sq₀ hy0 hrM0).2 hy
  have hrsub : 0 ≤ 1 - r := sub_nonneg.mpr hr1
  have hrr : r ^ 2 ≤ r := by nlinarith [mul_nonneg hr0 hrsub]
  have hrrM : r ^ 2 * M ^ 2 ≤ r * M ^ 2 :=
    mul_le_mul_of_nonneg_right hrr (sq_nonneg M)
  nlinarith

/-- The exact product-weighted `JI/IJ/JJ` ledger.  The three analytic
orientation estimates are hypotheses; their contraction to the four
one-dimensional weighted sums is proved here. -/
theorem productWeighted_orientation_ledger [DecidableEq ι]
    (μ : FiniteProbability Ω) (P : Finset ι)
    (I J : ι → Ω → ℝ) (b t u : ι → ℝ)
    (C ε : ℝ) (rJI rIJ rJJ : ι → ι → ℝ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (ht0 : ∀ i ∈ P, 0 ≤ t i) (hu0 : ∀ i ∈ P, 0 ≤ u i)
    (hJI : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (I j)| ≤
        C * t i * t j * u i ^ 2 * u j + ε * u i ^ 2 * u j + rJI i j)
    (hIJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (I i) (J j)| ≤
        C * t i * t j * u i * u j ^ 2 + ε * u i * u j ^ 2 + rIJ i j)
    (hJJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (J j)| ≤
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          ε * u i ^ 2 * u j ^ 2 + rJJ i j) :
    (∑ i ∈ P, ∑ j ∈ P.erase i, |b i * b j| *
      (|μ.covariance (J i) (I j)| + |μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)|)) ≤
      C * (2 * (∑ i ∈ P, t i * |b i| * u i) *
          (∑ i ∈ P, t i * |b i| * u i ^ 2) +
        (∑ i ∈ P, t i * |b i| * u i ^ 2) ^ 2) +
      ε * (2 * (∑ i ∈ P, |b i| * u i) *
          (∑ i ∈ P, |b i| * u i ^ 2) +
        (∑ i ∈ P, |b i| * u i ^ 2) ^ 2) +
      ∑ i ∈ P, ∑ j ∈ P.erase i,
        |b i * b j| * (rJI i j + rIJ i j + rJJ i j) := by
  have hJIc := offDiagonal_two_contraction P
    (fun i => t i * |b i| * u i ^ 2)
    (fun j => t j * |b j| * u j)
    (fun i => |b i| * u i ^ 2)
    (fun j => |b j| * u j)
    (fun i j => |b i * b j| * |μ.covariance (J i) (I j)|)
    (fun i j => |b i * b j| * rJI i j) C ε hC hε
    (fun i hi => mul_nonneg (mul_nonneg (ht0 i hi) (abs_nonneg _))
      (sq_nonneg _))
    (fun j hj => mul_nonneg (mul_nonneg (ht0 j hj) (abs_nonneg _))
      (hu0 j hj))
    (fun i hi => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun j hj => mul_nonneg (abs_nonneg _) (hu0 j hj))
    (fun i hi j hj => by
      have hij := hJI i hi j hj
      have hb : 0 ≤ |b i * b j| := abs_nonneg _
      calc
        |b i * b j| * |μ.covariance (J i) (I j)| ≤
            |b i * b j| *
              (C * t i * t j * u i ^ 2 * u j +
                ε * u i ^ 2 * u j + rJI i j) :=
          mul_le_mul_of_nonneg_left hij hb
        _ = C * (t i * |b i| * u i ^ 2) *
              (t j * |b j| * u j) +
            ε * (|b i| * u i ^ 2) * (|b j| * u j) +
            |b i * b j| * rJI i j := by
          rw [abs_mul]
          ring)
  have hIJc := offDiagonal_two_contraction P
    (fun i => t i * |b i| * u i)
    (fun j => t j * |b j| * u j ^ 2)
    (fun i => |b i| * u i)
    (fun j => |b j| * u j ^ 2)
    (fun i j => |b i * b j| * |μ.covariance (I i) (J j)|)
    (fun i j => |b i * b j| * rIJ i j) C ε hC hε
    (fun i hi => mul_nonneg (mul_nonneg (ht0 i hi) (abs_nonneg _))
      (hu0 i hi))
    (fun j hj => mul_nonneg (mul_nonneg (ht0 j hj) (abs_nonneg _))
      (sq_nonneg _))
    (fun i hi => mul_nonneg (abs_nonneg _) (hu0 i hi))
    (fun j hj => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun i hi j hj => by
      have hij := hIJ i hi j hj
      have hb : 0 ≤ |b i * b j| := abs_nonneg _
      calc
        |b i * b j| * |μ.covariance (I i) (J j)| ≤
            |b i * b j| *
              (C * t i * t j * u i * u j ^ 2 +
                ε * u i * u j ^ 2 + rIJ i j) :=
          mul_le_mul_of_nonneg_left hij hb
        _ = C * (t i * |b i| * u i) *
              (t j * |b j| * u j ^ 2) +
            ε * (|b i| * u i) * (|b j| * u j ^ 2) +
            |b i * b j| * rIJ i j := by
          rw [abs_mul]
          ring)
  have hJJc := offDiagonal_two_contraction P
    (fun i => t i * |b i| * u i ^ 2)
    (fun j => t j * |b j| * u j ^ 2)
    (fun i => |b i| * u i ^ 2)
    (fun j => |b j| * u j ^ 2)
    (fun i j => |b i * b j| * |μ.covariance (J i) (J j)|)
    (fun i j => |b i * b j| * rJJ i j) C ε hC hε
    (fun i hi => mul_nonneg (mul_nonneg (ht0 i hi) (abs_nonneg _))
      (sq_nonneg _))
    (fun j hj => mul_nonneg (mul_nonneg (ht0 j hj) (abs_nonneg _))
      (sq_nonneg _))
    (fun i hi => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun j hj => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    (fun i hi j hj => by
      have hij := hJJ i hi j hj
      have hb : 0 ≤ |b i * b j| := abs_nonneg _
      calc
        |b i * b j| * |μ.covariance (J i) (J j)| ≤
            |b i * b j| *
              (C * t i * t j * u i ^ 2 * u j ^ 2 +
                ε * u i ^ 2 * u j ^ 2 + rJJ i j) :=
          mul_le_mul_of_nonneg_left hij hb
        _ = C * (t i * |b i| * u i ^ 2) *
              (t j * |b j| * u j ^ 2) +
            ε * (|b i| * u i ^ 2) * (|b j| * u j ^ 2) +
            |b i * b j| * rJJ i j := by
          rw [abs_mul]
          ring)
  calc
    (∑ i ∈ P, ∑ j ∈ P.erase i, |b i * b j| *
      (|μ.covariance (J i) (I j)| + |μ.covariance (I i) (J j)| +
        |μ.covariance (J i) (J j)|)) =
      (∑ i ∈ P, ∑ j ∈ P.erase i,
        |b i * b j| * |μ.covariance (J i) (I j)|) +
      (∑ i ∈ P, ∑ j ∈ P.erase i,
        |b i * b j| * |μ.covariance (I i) (J j)|) +
      (∑ i ∈ P, ∑ j ∈ P.erase i,
        |b i * b j| * |μ.covariance (J i) (J j)|) := by
        simp only [mul_add, Finset.sum_add_distrib]
    _ ≤
      (C * (∑ i ∈ P, t i * |b i| * u i ^ 2) *
          (∑ i ∈ P, t i * |b i| * u i) +
        ε * (∑ i ∈ P, |b i| * u i ^ 2) *
          (∑ i ∈ P, |b i| * u i) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, |b i * b j| * rJI i j) +
      (C * (∑ i ∈ P, t i * |b i| * u i) *
          (∑ i ∈ P, t i * |b i| * u i ^ 2) +
        ε * (∑ i ∈ P, |b i| * u i) *
          (∑ i ∈ P, |b i| * u i ^ 2) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, |b i * b j| * rIJ i j) +
      (C * (∑ i ∈ P, t i * |b i| * u i ^ 2) *
          (∑ i ∈ P, t i * |b i| * u i ^ 2) +
        ε * (∑ i ∈ P, |b i| * u i ^ 2) *
          (∑ i ∈ P, |b i| * u i ^ 2) +
        ∑ i ∈ P, ∑ j ∈ P.erase i, |b i * b j| * rJJ i j) := by
        exact add_le_add (add_le_add hJIc hIJc) hJJc
    _ = _ := by
      simp only [Finset.sum_add_distrib, mul_add]
      ring

/-- Pure finite-sum expansion which isolates off-diagonal and diagonal
covariance entries. -/
theorem abs_variance_difference_le_offDiagonal [DecidableEq ι]
    (μ : FiniteProbability Ω) (P : Finset ι) (b : ι → ℝ)
    (V I : ι → Ω → ℝ) :
    |μ.variance (fun ω => ∑ i ∈ P, b i * V i ω) -
        μ.variance (fun ω => ∑ i ∈ P, b i * I i ω)| ≤
      ∑ i ∈ P,
        ((∑ j ∈ P.erase i,
          |b i * b j| *
            |μ.covariance (V i) (V j) - μ.covariance (I i) (I j)|) +
          b i ^ 2 *
            |μ.covariance (V i) (V i) - μ.covariance (I i) (I i)|) := by
  rw [μ.variance_difference_expansion]
  calc
    |∑ i ∈ P, ∑ j ∈ P,
        b i * b j * (μ.covariance (V i) (V j) -
          μ.covariance (I i) (I j))| ≤
      ∑ i ∈ P, |∑ j ∈ P,
        b i * b j * (μ.covariance (V i) (V j) -
          μ.covariance (I i) (I j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P, ∑ j ∈ P,
        |b i * b j * (μ.covariance (V i) (V j) -
          μ.covariance (I i) (I j))| := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ P,
        ((∑ j ∈ P.erase i,
          |b i * b j| *
            |μ.covariance (V i) (V j) - μ.covariance (I i) (I j)|) +
          b i ^ 2 *
            |μ.covariance (V i) (V i) - μ.covariance (I i) (I i)|) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_erase_add P
        (fun j => |b i * b j *
          (μ.covariance (V i) (V j) - μ.covariance (I i) (I j))|) hi]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j hj
        rw [abs_mul, abs_mul]
      · rw [abs_mul, abs_mul_self]
        ring_nf

/-- Finite relative prime-power transfer, the algebraic content of (7.57).

The three local orientation estimates and the second-moment estimate are
the explicit analytic hypotheses.  The conclusion visibly multiplies the
vanishing analytic remainder `ε` by a coefficient depending on `Ccmp`;
it does not reuse the same remainder with an unjustified unit coefficient.
For the paper's prime powers, instantiate `J` with `highPart powers X`;
`abs_covariance_high_base_le`, `abs_covariance_base_high_le`, and
`abs_covariance_high_high_le` derive the three hypotheses from the literal
finite sums over exponents.
-/
theorem relative_primePower_transfer [DecidableEq ι]
    (μ : FiniteProbability Ω) (P : Finset ι)
    (I J : ι → Ω → ℝ) (b t u : ι → ℝ)
    (C ε Ccmp w invW rem : ℝ)
    (rJI rIJ rJJ : ι → ι → ℝ) (rD : ι → ℝ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hCcmp : 0 ≤ Ccmp)
    (hw : 0 ≤ w) (hinv0 : 0 ≤ invW) (hinv1 : invW ≤ 1)
    (ht0 : ∀ i ∈ P, 0 ≤ t i) (ht1 : ∀ i ∈ P, t i ≤ 1)
    (hu0 : ∀ i ∈ P, 0 ≤ u i) (huW : ∀ i ∈ P, u i ≤ invW)
    (hI0 : ∀ i ∈ P, ∀ ω, 0 ≤ I i ω)
    (hI1 : ∀ i ∈ P, ∀ ω, I i ω ≤ 1)
    (hJ0 : ∀ i ∈ P, ∀ ω, 0 ≤ J i ω)
    (hJsq : ∀ i ∈ P, ∀ ω, J i ω ≤ J i ω ^ 2)
    (hIJpoint : ∀ i ∈ P, ∀ ω, I i ω * J i ω = J i ω)
    (hJI : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (I j)| ≤
        C * t i * t j * u i ^ 2 * u j + ε * u i ^ 2 * u j + rJI i j)
    (hIJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (I i) (J j)| ≤
        C * t i * t j * u i * u j ^ 2 + ε * u i * u j ^ 2 + rIJ i j)
    (hJJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (J j)| ≤
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          ε * u i ^ 2 * u j ^ 2 + rJJ i j)
    (hMoment : ∀ i ∈ P,
      μ.expect (fun ω => J i ω ^ 2) ≤ (C + ε) * u i ^ 2 + rD i)
    (hb1 : (∑ i ∈ P, |b i| * u i) ≤ Ccmp * w)
    (hb2 : (∑ i ∈ P, b i ^ 2 * u i) ≤ Ccmp * w ^ 2)
    (hRem :
      (∑ i ∈ P, ∑ j ∈ P.erase i,
        |b i * b j| * (rJI i j + rIJ i j + rJJ i j)) +
        3 * ∑ i ∈ P, b i ^ 2 * rD i ≤ rem * w ^ 2) :
    |μ.variance (fun ω => ∑ i ∈ P, b i * (I i ω + J i ω)) -
        μ.variance (fun ω => ∑ i ∈ P, b i * I i ω)| ≤
      3 * C * (Ccmp ^ 2 + Ccmp) * invW * w ^ 2 +
        3 * (Ccmp ^ 2 + Ccmp) * ε * w ^ 2 + rem * w ^ 2 := by
  have hCcmpw0 : 0 ≤ Ccmp * w := mul_nonneg hCcmp hw
  have hB10 : 0 ≤ ∑ i ∈ P, |b i| * u i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (abs_nonneg _) (hu0 i hi)
  have hA10 : 0 ≤ ∑ i ∈ P, t i * |b i| * u i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (ht0 i hi) (abs_nonneg _)) (hu0 i hi)
  have hA1 : (∑ i ∈ P, t i * |b i| * u i) ≤ Ccmp * w :=
    le_trans (sum_t_abs_le_sum_abs P t b u ht1 hu0) hb1
  have hB2pre : (∑ i ∈ P, |b i| * u i ^ 2) ≤
      invW * ∑ i ∈ P, |b i| * u i :=
    sum_mul_sq_weight_le P u (fun i => |b i|) invW hu0 huW
      (fun i hi => abs_nonneg _)
  have hB2 : (∑ i ∈ P, |b i| * u i ^ 2) ≤ invW * (Ccmp * w) :=
    le_trans hB2pre (mul_le_mul_of_nonneg_left hb1 hinv0)
  have hB20 : 0 ≤ ∑ i ∈ P, |b i| * u i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hA2pre : (∑ i ∈ P, t i * |b i| * u i ^ 2) ≤
      invW * ∑ i ∈ P, t i * |b i| * u i :=
    sum_mul_sq_weight_le P u (fun i => t i * |b i|) invW hu0 huW
      (fun i hi => mul_nonneg (ht0 i hi) (abs_nonneg _))
  have hA2 : (∑ i ∈ P, t i * |b i| * u i ^ 2) ≤ invW * (Ccmp * w) :=
    le_trans hA2pre (mul_le_mul_of_nonneg_left hA1 hinv0)
  have hA20 : 0 ≤ ∑ i ∈ P, t i * |b i| * u i ^ 2 := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (mul_nonneg (ht0 i hi) (abs_nonneg _)) (sq_nonneg _)
  have hDpre : (∑ i ∈ P, b i ^ 2 * u i ^ 2) ≤
      invW * ∑ i ∈ P, b i ^ 2 * u i :=
    sum_mul_sq_weight_le P u (fun i => b i ^ 2) invW hu0 huW
      (fun i hi => sq_nonneg _)
  have hD : (∑ i ∈ P, b i ^ 2 * u i ^ 2) ≤
      invW * (Ccmp * w ^ 2) :=
    le_trans hDpre (mul_le_mul_of_nonneg_left hb2 hinv0)
  have hOrient := productWeighted_orientation_ledger μ P I J b t u C ε
    rJI rIJ rJJ hC hε ht0 hu0 hJI hIJ hJJ
  have hMainContract :
      2 * (∑ i ∈ P, t i * |b i| * u i) *
          (∑ i ∈ P, t i * |b i| * u i ^ 2) +
        (∑ i ∈ P, t i * |b i| * u i ^ 2) ^ 2 ≤
          3 * invW * (Ccmp * w) ^ 2 :=
    two_product_add_square_le _ _ _ _ hA20 hCcmpw0 hinv0 hinv1
      hA1 hA2
  have hErrContract :
      2 * (∑ i ∈ P, |b i| * u i) *
          (∑ i ∈ P, |b i| * u i ^ 2) +
        (∑ i ∈ P, |b i| * u i ^ 2) ^ 2 ≤
          3 * invW * (Ccmp * w) ^ 2 :=
    two_product_add_square_le _ _ _ _ hB20 hCcmpw0 hinv0 hinv1
      hb1 hB2
  have hDiag : ∀ i ∈ P,
      |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I i ω + J i ω) - μ.covariance (I i) (I i)| ≤
        3 * ((C + ε) * u i ^ 2 + rD i) := by
    intro i hi
    calc
      |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I i ω + J i ω) - μ.covariance (I i) (I i)| ≤
          3 * μ.expect (fun ω => J i ω ^ 2) :=
        diagonal_difference_le_three_secondMoment μ (I i) (J i)
          (hI0 i hi) (hI1 i hi) (hJ0 i hi) (hJsq i hi)
          (hIJpoint i hi)
      _ ≤ 3 * ((C + ε) * u i ^ 2 + rD i) :=
        mul_le_mul_of_nonneg_left (hMoment i hi) (by norm_num)
  have hSplit := abs_variance_difference_le_offDiagonal μ P b
    (fun i ω => I i ω + J i ω) I
  have hBookkeeping :
    |μ.variance (fun ω => ∑ i ∈ P, b i * (I i ω + J i ω)) -
        μ.variance (fun ω => ∑ i ∈ P, b i * I i ω)| ≤
      C * (2 * (∑ i ∈ P, t i * |b i| * u i) *
          (∑ i ∈ P, t i * |b i| * u i ^ 2) +
        (∑ i ∈ P, t i * |b i| * u i ^ 2) ^ 2) +
      ε * (2 * (∑ i ∈ P, |b i| * u i) *
          (∑ i ∈ P, |b i| * u i ^ 2) +
        (∑ i ∈ P, |b i| * u i ^ 2) ^ 2) +
      ((∑ i ∈ P, ∑ j ∈ P.erase i,
        |b i * b j| * (rJI i j + rIJ i j + rJJ i j)) +
        3 * (C + ε) * ∑ i ∈ P, b i ^ 2 * u i ^ 2 +
        3 * ∑ i ∈ P, b i ^ 2 * rD i) := by
    calc
      |μ.variance (fun ω => ∑ i ∈ P, b i * (I i ω + J i ω)) -
          μ.variance (fun ω => ∑ i ∈ P, b i * I i ω)| ≤
        ∑ i ∈ P,
          ((∑ j ∈ P.erase i, |b i * b j| *
            |μ.covariance (fun ω => I i ω + J i ω)
                (fun ω => I j ω + J j ω) -
              μ.covariance (I i) (I j)|) +
            b i ^ 2 *
              |μ.covariance (fun ω => I i ω + J i ω)
                  (fun ω => I i ω + J i ω) -
                μ.covariance (I i) (I i)|) := hSplit
      _ ≤ (∑ i ∈ P, ∑ j ∈ P.erase i, |b i * b j| *
          (|μ.covariance (J i) (I j)| + |μ.covariance (I i) (J j)| +
            |μ.covariance (J i) (J j)|)) +
          ∑ i ∈ P, b i ^ 2 * (3 * ((C + ε) * u i ^ 2 + rD i)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro i hi
        apply add_le_add
        · apply Finset.sum_le_sum
          intro j hj
          apply mul_le_mul_of_nonneg_left
          · exact abs_covariance_full_difference_le μ I J i j
          · exact abs_nonneg _
        · apply mul_le_mul_of_nonneg_left (hDiag i hi) (sq_nonneg _)
      _ ≤
        (C * (2 * (∑ i ∈ P, t i * |b i| * u i) *
            (∑ i ∈ P, t i * |b i| * u i ^ 2) +
          (∑ i ∈ P, t i * |b i| * u i ^ 2) ^ 2) +
        ε * (2 * (∑ i ∈ P, |b i| * u i) *
            (∑ i ∈ P, |b i| * u i ^ 2) +
          (∑ i ∈ P, |b i| * u i ^ 2) ^ 2) +
        ∑ i ∈ P, ∑ j ∈ P.erase i,
          |b i * b j| * (rJI i j + rIJ i j + rJJ i j)) +
          ∑ i ∈ P, b i ^ 2 * (3 * ((C + ε) * u i ^ 2 + rD i)) :=
        add_le_add hOrient (le_refl _)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        ring_nf
  calc
    |μ.variance (fun ω => ∑ i ∈ P, b i * (I i ω + J i ω)) -
        μ.variance (fun ω => ∑ i ∈ P, b i * I i ω)| ≤ _ := hBookkeeping
    _ ≤ C * (3 * invW * (Ccmp * w) ^ 2) +
        ε * (3 * invW * (Ccmp * w) ^ 2) +
        3 * (C + ε) * (invW * (Ccmp * w ^ 2)) +
        ((∑ i ∈ P, ∑ j ∈ P.erase i,
          |b i * b j| * (rJI i j + rIJ i j + rJJ i j)) +
          3 * ∑ i ∈ P, b i ^ 2 * rD i) := by
      have hMainScaled := mul_le_mul_of_nonneg_left hMainContract hC
      have hErrScaled := mul_le_mul_of_nonneg_left hErrContract hε
      have hDiagScaled :
          3 * (C + ε) * (∑ i ∈ P, b i ^ 2 * u i ^ 2) ≤
            3 * (C + ε) * (invW * (Ccmp * w ^ 2)) :=
        mul_le_mul_of_nonneg_left hD
          (mul_nonneg (by norm_num) (add_nonneg hC hε))
      nlinarith
    _ ≤ C * (3 * invW * (Ccmp * w) ^ 2) +
        ε * (3 * invW * (Ccmp * w) ^ 2) +
        3 * (C + ε) * (invW * (Ccmp * w ^ 2)) + rem * w ^ 2 := by
      linarith
    _ ≤ 3 * C * (Ccmp ^ 2 + Ccmp) * invW * w ^ 2 +
        3 * (Ccmp ^ 2 + Ccmp) * ε * w ^ 2 + rem * w ^ 2 := by
      have hεdrop : ε * invW ≤ ε :=
        mul_le_of_le_one_right hε hinv1
      have hcoefficient0 : 0 ≤ 3 * (Ccmp ^ 2 + Ccmp) * w ^ 2 :=
        mul_nonneg
          (mul_nonneg (by norm_num) (add_nonneg (sq_nonneg Ccmp) hCcmp))
          (sq_nonneg w)
      have hεscaled :
          (3 * (Ccmp ^ 2 + Ccmp) * w ^ 2) * (ε * invW) ≤
            (3 * (Ccmp ^ 2 + Ccmp) * w ^ 2) * ε :=
        mul_le_mul_of_nonneg_left hεdrop hcoefficient0
      calc
        C * (3 * invW * (Ccmp * w) ^ 2) +
            ε * (3 * invW * (Ccmp * w) ^ 2) +
            3 * (C + ε) * (invW * (Ccmp * w ^ 2)) + rem * w ^ 2 =
          3 * C * (Ccmp ^ 2 + Ccmp) * invW * w ^ 2 +
            (3 * (Ccmp ^ 2 + Ccmp) * w ^ 2) * (ε * invW) +
            rem * w ^ 2 := by ring
        _ ≤ 3 * C * (Ccmp ^ 2 + Ccmp) * invW * w ^ 2 +
            (3 * (Ccmp ^ 2 + Ccmp) * w ^ 2) * ε + rem * w ^ 2 := by
          linarith
        _ = 3 * C * (Ccmp ^ 2 + Ccmp) * invW * w ^ 2 +
            3 * (Ccmp ^ 2 + Ccmp) * ε * w ^ 2 + rem * w ^ 2 := by ring

set_option maxHeartbeats 800000 in
/-- Pointwise form of the weighted row-norm conclusion of Lemma 7.5.
Taking the supremum over `i ∈ P` gives the paper's row norm.  The three
prime-sum hypotheses are precisely the finite versions of the Mertens
inputs used after the analytic local estimates. -/
theorem row_primePower_transfer [DecidableEq ι]
    (μ : FiniteProbability Ω) (P : Finset ι)
    (I J : ι → Ω → ℝ) (t u rowScale : ι → ℝ)
    (C ε invW HT H1 H2 remRow : ℝ)
    (rJI rIJ rJJ : ι → ι → ℝ) (rD : ι → ℝ)
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hinv0 : 0 ≤ invW) (hinv1 : invW ≤ 1)
    (ht0 : ∀ i ∈ P, 0 ≤ t i) (ht1 : ∀ i ∈ P, t i ≤ 1)
    (hu0 : ∀ i ∈ P, 0 ≤ u i) (huW : ∀ i ∈ P, u i ≤ invW)
    (hscale0 : ∀ i ∈ P, 0 ≤ rowScale i)
    (hscale : ∀ i ∈ P, rowScale i * u i = 1)
    (hI0 : ∀ i ∈ P, ∀ ω, 0 ≤ I i ω)
    (hI1 : ∀ i ∈ P, ∀ ω, I i ω ≤ 1)
    (hJ0 : ∀ i ∈ P, ∀ ω, 0 ≤ J i ω)
    (hJsq : ∀ i ∈ P, ∀ ω, J i ω ≤ J i ω ^ 2)
    (hIJpoint : ∀ i ∈ P, ∀ ω, I i ω * J i ω = J i ω)
    (hJI : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (I j)| ≤
        C * t i * t j * u i ^ 2 * u j + ε * u i ^ 2 * u j + rJI i j)
    (hIJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (I i) (J j)| ≤
        C * t i * t j * u i * u j ^ 2 + ε * u i * u j ^ 2 + rIJ i j)
    (hJJ : ∀ i ∈ P, ∀ j ∈ P.erase i,
      |μ.covariance (J i) (J j)| ≤
        C * t i * t j * u i ^ 2 * u j ^ 2 +
          ε * u i ^ 2 * u j ^ 2 + rJJ i j)
    (hMoment : ∀ i ∈ P,
      μ.expect (fun ω => J i ω ^ 2) ≤ (C + ε) * u i ^ 2 + rD i)
    (hTsum : (∑ j ∈ P, t j * u j) ≤ HT)
    (hUsum : (∑ j ∈ P, u j) ≤ H1)
    (hU2sum : (∑ j ∈ P, u j ^ 2) ≤ H2 * invW)
    (hRowRem : ∀ i ∈ P,
      rowScale i *
        ((∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j)) +
          3 * rD i) ≤ remRow) :
    ∀ i ∈ P,
      rowScale i * ∑ j ∈ P,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)| ≤
      C * (HT + 2 * H2 + 3) * invW +
        ε * (H1 + 2 * H2 + 3) * invW + remRow := by
  intro i hi
  have hui0 := hu0 i hi
  have huiW := huW i hi
  have hti0 := ht0 i hi
  have hti1 := ht1 i hi
  have hs0 := hscale0 i hi
  have hsu := hscale i hi
  have hsu2 : rowScale i * u i ^ 2 = u i := by
    calc
      rowScale i * u i ^ 2 = (rowScale i * u i) * u i := by ring
      _ = u i := by rw [hsu]; ring
  have hTU20 : 0 ≤ ∑ j ∈ P, t j * u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j hj) (sq_nonneg _)
  have hU20 : 0 ≤ ∑ j ∈ P, u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact sq_nonneg _
  have hT0 : 0 ≤ ∑ j ∈ P, t j * u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j hj) (hu0 j hj)
  have hU0 : 0 ≤ ∑ j ∈ P, u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hu0 j hj
  have hTU2 : (∑ j ∈ P, t j * u j ^ 2) ≤ H2 * invW := by
    calc
      (∑ j ∈ P, t j * u j ^ 2) ≤ ∑ j ∈ P, u j ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have huj2 : 0 ≤ u j ^ 2 := sq_nonneg _
        calc
          t j * u j ^ 2 ≤ 1 * u j ^ 2 :=
            mul_le_mul_of_nonneg_right (ht1 j hj) huj2
          _ = u j ^ 2 := by ring
      _ ≤ H2 * invW := hU2sum
  have herase {f : ι → ℝ} (hf : ∀ j ∈ P, 0 ≤ f j) :
      (∑ j ∈ P.erase i, f j) ≤ ∑ j ∈ P, f j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i P)
      (fun j hjP hjErase => hf j hjP)
  have hTerase : (∑ j ∈ P.erase i, t j * u j) ≤ HT :=
    le_trans (herase (fun j hj => mul_nonneg (ht0 j hj) (hu0 j hj))) hTsum
  have hUerase : (∑ j ∈ P.erase i, u j) ≤ H1 :=
    le_trans (herase hu0) hUsum
  have hU2erase : (∑ j ∈ P.erase i, u j ^ 2) ≤ H2 * invW :=
    le_trans (herase (fun j hj => sq_nonneg _)) hU2sum
  have hTU2erase : (∑ j ∈ P.erase i, t j * u j ^ 2) ≤ H2 * invW :=
    le_trans (herase (fun j hj =>
      mul_nonneg (ht0 j hj) (sq_nonneg _))) hTU2
  have hTerase0 : 0 ≤ ∑ j ∈ P.erase i, t j * u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j (Finset.mem_of_mem_erase hj))
      (hu0 j (Finset.mem_of_mem_erase hj))
  have hTU2erase0 : 0 ≤ ∑ j ∈ P.erase i, t j * u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ht0 j (Finset.mem_of_mem_erase hj)) (sq_nonneg _)
  have hUerase0 : 0 ≤ ∑ j ∈ P.erase i, u j := by
    apply Finset.sum_nonneg
    intro j hj
    exact hu0 j (Finset.mem_of_mem_erase hj)
  have hU2erase0 : 0 ≤ ∑ j ∈ P.erase i, u j ^ 2 := by
    apply Finset.sum_nonneg
    intro j hj
    exact sq_nonneg _
  have hCJI_sum :
      (∑ j ∈ P.erase i, C * t i * t j * u i ^ 2 * u j) =
        C * t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hCIJ_sum :
      (∑ j ∈ P.erase i, C * t i * t j * u i * u j ^ 2) =
        C * t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hCJJ_sum :
      (∑ j ∈ P.erase i, C * t i * t j * u i ^ 2 * u j ^ 2) =
        C * t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hεJI_sum :
      (∑ j ∈ P.erase i, ε * u i ^ 2 * u j) =
        ε * u i ^ 2 * (∑ j ∈ P.erase i, u j) := by
    rw [Finset.mul_sum]
  have hεIJ_sum :
      (∑ j ∈ P.erase i, ε * u i * u j ^ 2) =
        ε * u i * (∑ j ∈ P.erase i, u j ^ 2) := by
    rw [Finset.mul_sum]
  have hεJJ_sum :
      (∑ j ∈ P.erase i, ε * u i ^ 2 * u j ^ 2) =
        ε * u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2) := by
    rw [Finset.mul_sum]
  have hOff :
      (∑ j ∈ P.erase i,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)|) ≤
      C * (t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j) +
        t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2) +
        t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j ^ 2)) +
      ε * (u i ^ 2 * (∑ j ∈ P.erase i, u j) +
        u i * (∑ j ∈ P.erase i, u j ^ 2) +
        u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) +
      ∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j) := by
    calc
      (∑ j ∈ P.erase i,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)|) ≤
        ∑ j ∈ P.erase i,
          (|μ.covariance (J i) (I j)| + |μ.covariance (I i) (J j)| +
            |μ.covariance (J i) (J j)|) := by
        apply Finset.sum_le_sum
        intro j hj
        exact abs_covariance_full_difference_le μ I J i j
      _ ≤ ∑ j ∈ P.erase i,
          ((C * t i * t j * u i ^ 2 * u j + ε * u i ^ 2 * u j + rJI i j) +
          (C * t i * t j * u i * u j ^ 2 + ε * u i * u j ^ 2 + rIJ i j) +
          (C * t i * t j * u i ^ 2 * u j ^ 2 +
            ε * u i ^ 2 * u j ^ 2 + rJJ i j)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact add_le_add (add_le_add (hJI i hi j hj) (hIJ i hi j hj))
          (hJJ i hi j hj)
      _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [hCJI_sum, hCIJ_sum, hCJJ_sum, hεJI_sum, hεIJ_sum, hεJJ_sum]
        ring
  have hDiag :
      |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I i ω + J i ω) - μ.covariance (I i) (I i)| ≤
        3 * ((C + ε) * u i ^ 2 + rD i) := by
    calc
      |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I i ω + J i ω) - μ.covariance (I i) (I i)| ≤
          3 * μ.expect (fun ω => J i ω ^ 2) :=
        diagonal_difference_le_three_secondMoment μ (I i) (J i)
          (hI0 i hi) (hI1 i hi) (hJ0 i hi) (hJsq i hi)
          (hIJpoint i hi)
      _ ≤ 3 * ((C + ε) * u i ^ 2 + rD i) :=
        mul_le_mul_of_nonneg_left (hMoment i hi) (by norm_num)
  have hrowSplit :
      rowScale i * ∑ j ∈ P,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)| ≤
      rowScale i *
        ((C * (t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j) +
          t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2) +
          t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j ^ 2)) +
        ε * (u i ^ 2 * (∑ j ∈ P.erase i, u j) +
          u i * (∑ j ∈ P.erase i, u j ^ 2) +
          u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) +
        ∑ j ∈ P.erase i, (rJI i j + rIJ i j + rJJ i j)) +
        3 * ((C + ε) * u i ^ 2 + rD i)) := by
    apply mul_le_mul_of_nonneg_left _ hs0
    rw [← Finset.sum_erase_add P
      (fun j => |μ.covariance (fun ω => I i ω + J i ω)
          (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)|) hi]
    exact add_le_add hOff hDiag
  calc
    rowScale i * ∑ j ∈ P,
        |μ.covariance (fun ω => I i ω + J i ω)
            (fun ω => I j ω + J j ω) - μ.covariance (I i) (I j)| ≤ _ := hrowSplit
    _ ≤ C * (HT + 2 * H2 + 3) * invW +
        ε * (H1 + 2 * H2 + 3) * invW + remRow := by
      have hCT1 :
          rowScale i * (t i * u i ^ 2 * (∑ j ∈ P.erase i, t j * u j)) ≤
            invW * HT := by
        have htiuW : t i * u i ≤ invW := by
          calc
            t i * u i ≤ 1 * u i := mul_le_mul_of_nonneg_right hti1 hui0
            _ = u i := one_mul _
            _ ≤ invW := huiW
        calc
          rowScale i * (t i * u i ^ 2 *
              (∑ j ∈ P.erase i, t j * u j)) =
              (t i * u i) * (∑ j ∈ P.erase i, t j * u j) := by
                calc
                  rowScale i * (t i * u i ^ 2 *
                      (∑ j ∈ P.erase i, t j * u j)) =
                      t i * (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, t j * u j) := by ring
                  _ = (t i * u i) * (∑ j ∈ P.erase i, t j * u j) := by
                    rw [hsu2]
          _ ≤ invW * HT :=
            mul_le_mul htiuW hTerase hTerase0 hinv0
      have hCT2 :
          rowScale i * (t i * u i * (∑ j ∈ P.erase i, t j * u j ^ 2)) ≤
            H2 * invW := by
        calc
          rowScale i * (t i * u i *
              (∑ j ∈ P.erase i, t j * u j ^ 2)) =
              t i * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
                calc
                  rowScale i * (t i * u i *
                      (∑ j ∈ P.erase i, t j * u j ^ 2)) =
                      t i * (rowScale i * u i) *
                        (∑ j ∈ P.erase i, t j * u j ^ 2) := by ring
                  _ = t i * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
                    rw [hsu]
                    ring
          _ ≤ 1 * (∑ j ∈ P.erase i, t j * u j ^ 2) :=
            mul_le_mul_of_nonneg_right hti1 hTU2erase0
          _ = ∑ j ∈ P.erase i, t j * u j ^ 2 := one_mul _
          _ ≤ H2 * invW := hTU2erase
      have hCT3 :
          rowScale i * (t i * u i ^ 2 *
            (∑ j ∈ P.erase i, t j * u j ^ 2)) ≤ H2 * invW := by
        have htiu : t i * u i ≤ 1 := by
          calc
            t i * u i ≤ 1 * u i := mul_le_mul_of_nonneg_right hti1 hui0
            _ = u i := by ring
            _ ≤ invW := huiW
            _ ≤ 1 := hinv1
        calc
          rowScale i * (t i * u i ^ 2 *
              (∑ j ∈ P.erase i, t j * u j ^ 2)) =
              (t i * u i) * (∑ j ∈ P.erase i, t j * u j ^ 2) := by
                calc
                  rowScale i * (t i * u i ^ 2 *
                      (∑ j ∈ P.erase i, t j * u j ^ 2)) =
                      t i * (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, t j * u j ^ 2) := by ring
                  _ = (t i * u i) *
                      (∑ j ∈ P.erase i, t j * u j ^ 2) := by rw [hsu2]
          _ ≤ 1 * (∑ j ∈ P.erase i, t j * u j ^ 2) :=
            mul_le_mul_of_nonneg_right htiu hTU2erase0
          _ = ∑ j ∈ P.erase i, t j * u j ^ 2 := one_mul _
          _ ≤ H2 * invW := hTU2erase
      have hEU1 :
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j)) ≤ invW * H1 := by
        calc
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j)) =
              u i * (∑ j ∈ P.erase i, u j) := by
                calc
                  rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j)) =
                      (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, u j) := by ring
                  _ = u i * (∑ j ∈ P.erase i, u j) := by rw [hsu2]
          _ ≤ invW * H1 := mul_le_mul huiW hUerase hUerase0 hinv0
      have hEU2 :
          rowScale i * (u i * (∑ j ∈ P.erase i, u j ^ 2)) ≤ H2 * invW := by
        rw [show rowScale i * (u i * (∑ j ∈ P.erase i, u j ^ 2)) =
          (∑ j ∈ P.erase i, u j ^ 2) by rw [show rowScale i *
            (u i * (∑ j ∈ P.erase i, u j ^ 2)) =
              (rowScale i * u i) * (∑ j ∈ P.erase i, u j ^ 2) by ring,
            hsu, one_mul]]
        exact hU2erase
      have hEU3 :
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) ≤
            H2 * invW := by
        have hui1 : u i ≤ 1 := le_trans huiW hinv1
        calc
          rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) =
              u i * (∑ j ∈ P.erase i, u j ^ 2) := by
                calc
                  rowScale i * (u i ^ 2 * (∑ j ∈ P.erase i, u j ^ 2)) =
                      (rowScale i * u i ^ 2) *
                        (∑ j ∈ P.erase i, u j ^ 2) := by ring
                  _ = u i * (∑ j ∈ P.erase i, u j ^ 2) := by rw [hsu2]
          _ ≤ 1 * (∑ j ∈ P.erase i, u j ^ 2) :=
            mul_le_mul_of_nonneg_right hui1 hU2erase0
          _ = ∑ j ∈ P.erase i, u j ^ 2 := one_mul _
          _ ≤ H2 * invW := hU2erase
      have hDiagMain : rowScale i * (3 * (C + ε) * u i ^ 2) ≤
          3 * (C + ε) * invW := by
        rw [show rowScale i * (3 * (C + ε) * u i ^ 2) =
          3 * (C + ε) * (rowScale i * u i ^ 2) by ring, hsu2]
        exact mul_le_mul_of_nonneg_left huiW
          (mul_nonneg (by norm_num) (add_nonneg hC hε))
      have hR := hRowRem i hi
      nlinarith

end FiniteContraction

end Erdos390.Lemma75
