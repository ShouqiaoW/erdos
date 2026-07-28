import Erdos390.WholePaper.RoughFixedHeadFriableShift
import Erdos390.WholePaper.RoughTransitionBalancedBlock

/-!
# Residual cancellation in the balanced four-endpoint friable block

The closed de Bruijn theorem controls the endpoint residual

`R(X,y) = Psi(X,y) - X * rho(log X / log y)`

by `O(X / log y)`.  Applying that estimate independently at four
endpoints loses one logarithm.  This file avoids that lossy triangle
inequality.  It proves that the literal four-endpoint residual is exactly
two *short residual increments* plus one broad increment whose coefficient
already contains `1/L`.

It also records the exact reverse Buchstab recurrence for `R`, using one
common prime interval for both endpoints.  The remaining missing analytic
input is thereby reduced to a local regularity inequality for `R`; it is
strictly an estimate for the genuine friable counting function and contains
no selector, row, rounding, or feasibility conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The genuine endpoint residual -/

/-- The Dickman main term at one natural endpoint. -/
noncomputable def roughFriableDickmanMain (X y : ℕ) : ℝ :=
  (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)

/-- The actual de Bruijn residual, not an assumed error function. -/
noncomputable def roughFriableResidual (X y : ℕ) : ℝ :=
  (FriableAsymptotic.friableCount X y : ℝ) -
    roughFriableDickmanMain X y

@[simp]
theorem roughFriableDickmanMain_zero (y : ℕ) :
    roughFriableDickmanMain 0 y = 0 := by
  simp [roughFriableDickmanMain]

@[simp]
theorem roughFriableResidual_zero (y : ℕ) :
    roughFriableResidual 0 y = 0 := by
  simp [roughFriableResidual]

/-- The count is exactly its Dickman main term plus the genuine residual. -/
theorem roughFriableCount_eq_main_add_residual (X y : ℕ) :
    (FriableAsymptotic.friableCount X y : ℝ) =
      roughFriableDickmanMain X y + roughFriableResidual X y := by
  unfold roughFriableResidual
  ring

/-- On the exact initial Dickman face the residual vanishes identically. -/
theorem roughFriableResidual_eq_zero_of_le
    {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    roughFriableResidual X y = 0 := by
  unfold roughFriableResidual roughFriableDickmanMain
  rw [FriableAsymptotic.friableCount_eq_dickman_initial hX hy hXy]
  ring

/-- Closed uniform endpoint control inherited from the proved de Bruijn
estimate.  This theorem is intentionally recorded for comparison with the
strictly stronger local increment bound isolated below. -/
theorem exists_uniform_roughFriableResidual_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableResidual X y| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hmain⟩ :=
    FriableAsymptotic.exists_uniform_friableCount_dickman_bound_all_faces
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y hY hX hlog
  simpa only [roughFriableResidual, roughFriableDickmanMain] using
    hmain hY hX hlog

/-! ## Exact reverse Buchstab recurrence for the residual -/

/-- The common prime interval `y < p <= Z` used to reverse the largest
prime-factor recurrence at every endpoint `X <= Z`. -/
def roughReversePrimeInterval (y Z : ℕ) : Finset ℕ :=
  (Z + 1).primesBelow \ (y + 1).primesBelow

/-- The deterministic main-term defect in the reverse Buchstab recurrence.
Every term is explicit in `rho`; no counting error is hidden in this
definition. -/
noncomputable def roughFriableReverseMainDefect
    (X y Z : ℕ) : ℝ :=
  (X : ℝ) - roughFriableDickmanMain X y -
    ∑ p ∈ roughReversePrimeInterval y Z,
      roughFriableDickmanMain (X / p) p

/-- Exact reverse recurrence for the genuine residual.  Choosing one cap
`Z >= X` makes the top count exact, while every recursive quotient has
smaller size. -/
theorem roughFriableResidual_reverseRecurrence
    {X y Z : ℕ} (hX : 0 < X) (hyZ : y ≤ Z) (hXZ : X ≤ Z) :
    roughFriableResidual X y =
      roughFriableReverseMainDefect X y Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughFriableResidual (X / p) p := by
  have hrec := FriableAsymptotic.friableCount_prime_interval X hX hyZ
  rw [FriableAsymptotic.friableCount_eq_self hXZ] at hrec
  have hrecReal := congrArg (fun n : ℕ ↦ (n : ℝ)) hrec
  simp only [Nat.cast_add, Nat.cast_sum] at hrecReal
  unfold roughFriableResidual roughFriableReverseMainDefect
  rw [Finset.sum_sub_distrib]
  dsimp only [roughReversePrimeInterval] at hrecReal ⊢
  linarith

/-- Total version of the reverse recurrence, including the zero endpoint
which is needed when a quotient interval is born at one prime. -/
theorem roughFriableResidual_reverseRecurrence_all
    {X y Z : ℕ} (hyZ : y ≤ Z) (hXZ : X ≤ Z) :
    roughFriableResidual X y =
      roughFriableReverseMainDefect X y Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughFriableResidual (X / p) p := by
  by_cases hX : X = 0
  · subst X
    simp [roughFriableReverseMainDefect]
  · exact roughFriableResidual_reverseRecurrence
      (Nat.pos_of_ne_zero hX) hyZ hXZ

/-- Subtracting the reverse recurrence at two endpoints keeps the prime
interval common.  This is the exact finite-difference identity needed for
an inductive proof of transition regularity. -/
theorem roughFriableResidual_difference_reverseRecurrence
    {X₀ X₁ y Z : ℕ}
    (hX₀ : 0 < X₀) (hX₁ : 0 < X₁)
    (hyZ : y ≤ Z) (hX₀Z : X₀ ≤ Z) (hX₁Z : X₁ ≤ Z) :
    roughFriableResidual X₁ y - roughFriableResidual X₀ y =
      (roughFriableReverseMainDefect X₁ y Z -
          roughFriableReverseMainDefect X₀ y Z) -
        ∑ p ∈ roughReversePrimeInterval y Z,
          (roughFriableResidual (X₁ / p) p -
            roughFriableResidual (X₀ / p) p) := by
  rw [roughFriableResidual_reverseRecurrence hX₁ hyZ hX₁Z,
    roughFriableResidual_reverseRecurrence hX₀ hyZ hX₀Z,
    Finset.sum_sub_distrib]
  ring

/-- Total common-cutoff difference recurrence, with no positivity
restriction on the lower endpoint. -/
theorem roughFriableResidual_difference_reverseRecurrence_all
    {X₀ X₁ y Z : ℕ}
    (hyZ : y ≤ Z) (hX₀Z : X₀ ≤ Z) (hX₁Z : X₁ ≤ Z) :
    roughFriableResidual X₁ y - roughFriableResidual X₀ y =
      (roughFriableReverseMainDefect X₁ y Z -
          roughFriableReverseMainDefect X₀ y Z) -
        ∑ p ∈ roughReversePrimeInterval y Z,
          (roughFriableResidual (X₁ / p) p -
            roughFriableResidual (X₀ / p) p) := by
  rw [roughFriableResidual_reverseRecurrence_all hyZ hX₁Z,
    roughFriableResidual_reverseRecurrence_all hyZ hX₀Z,
    Finset.sum_sub_distrib]
  ring

/-! ## Verified regularity of the Dickman main term -/

/-- Symmetric compact one-Lipschitz control of the already constructed
Dickman function. -/
theorem roughRho_abs_sub_le_abs_of_le_five
    {a b : ℝ} (ha5 : a ≤ 5) (hb5 : b ≤ 5) :
    |rho a - rho b| ≤ |a - b| := by
  by_cases hab : a ≤ b
  · have h := FriableAsymptotic.rho_lipschitz_of_le_five hab hb5
    rw [abs_sub_comm (rho a), abs_sub_comm a]
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hab)).symm
  · have hba : b ≤ a := le_of_not_ge hab
    have h := FriableAsymptotic.rho_lipschitz_of_le_five hba ha5
    exact h.trans_eq (abs_of_nonneg (sub_nonneg.mpr hba)).symm

/-- A balanced finite family of natural endpoints has a Dickman main term
controlled only by its exact coordinate displacements from one base point.
This is the verified transition part; no estimate for the residual enters. -/
theorem roughBalancedFriableMain_abs_le
    {ι : Type*} (I : Finset ι)
    (coeff : ι → ℝ) (endpoint : ι → ℕ) (base y : ℕ)
    (hbalance : ∑ i ∈ I, coeff i * (endpoint i : ℝ) = 0)
    (hendpoint5 : ∀ i ∈ I,
      FriableAsymptotic.dickmanU (endpoint i) y ≤ 5)
    (hbase5 : FriableAsymptotic.dickmanU base y ≤ 5) :
    |∑ i ∈ I,
        coeff i * roughFriableDickmanMain (endpoint i) y| ≤
      ∑ i ∈ I,
        |coeff i| * (endpoint i : ℝ) *
          |FriableAsymptotic.dickmanU (endpoint i) y -
            FriableAsymptotic.dickmanU base y| := by
  have hcenter :
      (∑ i ∈ I,
          coeff i * roughFriableDickmanMain (endpoint i) y) =
        ∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y)) := by
    unfold roughFriableDickmanMain
    calc
      ∑ i ∈ I,
          coeff i *
            ((endpoint i : ℝ) *
              rho (FriableAsymptotic.dickmanU (endpoint i) y)) =
        ∑ i ∈ I,
          (coeff i * (endpoint i : ℝ) *
              (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
                rho (FriableAsymptotic.dickmanU base y)) +
            rho (FriableAsymptotic.dickmanU base y) *
              (coeff i * (endpoint i : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = (∑ i ∈ I,
            coeff i * (endpoint i : ℝ) *
              (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
                rho (FriableAsymptotic.dickmanU base y))) +
          rho (FriableAsymptotic.dickmanU base y) *
            ∑ i ∈ I, coeff i * (endpoint i : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ i ∈ I,
            coeff i * (endpoint i : ℝ) *
              (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
                rho (FriableAsymptotic.dickmanU base y)) := by
        rw [hbalance, mul_zero, add_zero]
  rw [hcenter]
  calc
    |∑ i ∈ I,
        coeff i * (endpoint i : ℝ) *
          (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
            rho (FriableAsymptotic.dickmanU base y))| ≤
      ∑ i ∈ I,
        |coeff i * (endpoint i : ℝ) *
          (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
            rho (FriableAsymptotic.dickmanU base y))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I,
        |coeff i| * (endpoint i : ℝ) *
          |FriableAsymptotic.dickmanU (endpoint i) y -
            FriableAsymptotic.dickmanU base y| := by
      apply Finset.sum_le_sum
      intro i hi
      have hendpointAbs : |(endpoint i : ℝ)| = (endpoint i : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [abs_mul, abs_mul, hendpointAbs]
      exact mul_le_mul_of_nonneg_left
        (roughRho_abs_sub_le_abs_of_le_five
          (hendpoint5 i hi) hbase5)
        (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))

/-- Floor endpoints need not retain the real first-moment balance exactly.
The same centering argument keeps the complete imbalance as one explicit
endpoint term.  On the positive compact Dickman range its coefficient has
absolute value at most one. -/
theorem roughFriableMain_abs_le_with_balanceError
    {ι : Type*} (I : Finset ι)
    (coeff : ι → ℝ) (endpoint : ι → ℕ) (base y : ℕ)
    (hendpoint5 : ∀ i ∈ I,
      FriableAsymptotic.dickmanU (endpoint i) y ≤ 5)
    (hbase0 : 0 ≤ FriableAsymptotic.dickmanU base y)
    (hbase5 : FriableAsymptotic.dickmanU base y ≤ 5) :
    |∑ i ∈ I,
        coeff i * roughFriableDickmanMain (endpoint i) y| ≤
      (∑ i ∈ I,
        |coeff i| * (endpoint i : ℝ) *
          |FriableAsymptotic.dickmanU (endpoint i) y -
            FriableAsymptotic.dickmanU base y|) +
      |∑ i ∈ I, coeff i * (endpoint i : ℝ)| := by
  have hcenter :
      (∑ i ∈ I,
          coeff i * roughFriableDickmanMain (endpoint i) y) =
        (∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))) +
        rho (FriableAsymptotic.dickmanU base y) *
          ∑ i ∈ I, coeff i * (endpoint i : ℝ) := by
    unfold roughFriableDickmanMain
    calc
      ∑ i ∈ I,
          coeff i *
            ((endpoint i : ℝ) *
              rho (FriableAsymptotic.dickmanU (endpoint i) y)) =
        ∑ i ∈ I,
          (coeff i * (endpoint i : ℝ) *
              (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
                rho (FriableAsymptotic.dickmanU base y)) +
            rho (FriableAsymptotic.dickmanU base y) *
              (coeff i * (endpoint i : ℝ))) := by
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hcenterBound :
      |∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))| ≤
        ∑ i ∈ I,
          |coeff i| * (endpoint i : ℝ) *
            |FriableAsymptotic.dickmanU (endpoint i) y -
              FriableAsymptotic.dickmanU base y| := by
    calc
      _ ≤ ∑ i ∈ I,
          |coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ I,
          |coeff i| * (endpoint i : ℝ) *
            |FriableAsymptotic.dickmanU (endpoint i) y -
              FriableAsymptotic.dickmanU base y| := by
        apply Finset.sum_le_sum
        intro i hi
        have hendpointAbs : |(endpoint i : ℝ)| = (endpoint i : ℝ) :=
          abs_of_nonneg (Nat.cast_nonneg _)
        rw [abs_mul, abs_mul, hendpointAbs]
        exact mul_le_mul_of_nonneg_left
          (roughRho_abs_sub_le_abs_of_le_five
            (hendpoint5 i hi) hbase5)
          (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hrhoPos : 0 < rho (FriableAsymptotic.dickmanU base y) :=
    rho_pos_on_zero_five hbase0 hbase5
  have hrhoLe : rho (FriableAsymptotic.dickmanU base y) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hbase5
  rw [hcenter]
  calc
    |(∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))) +
        rho (FriableAsymptotic.dickmanU base y) *
          ∑ i ∈ I, coeff i * (endpoint i : ℝ)| ≤
      |∑ i ∈ I,
          coeff i * (endpoint i : ℝ) *
            (rho (FriableAsymptotic.dickmanU (endpoint i) y) -
              rho (FriableAsymptotic.dickmanU base y))| +
        |rho (FriableAsymptotic.dickmanU base y) *
          ∑ i ∈ I, coeff i * (endpoint i : ℝ)| := abs_add_le _ _
    _ ≤ (∑ i ∈ I,
          |coeff i| * (endpoint i : ℝ) *
            |FriableAsymptotic.dickmanU (endpoint i) y -
              FriableAsymptotic.dickmanU base y|) +
        |∑ i ∈ I, coeff i * (endpoint i : ℝ)| := by
      apply add_le_add hcenterBound
      rw [abs_mul, abs_of_pos hrhoPos]
      calc
        rho (FriableAsymptotic.dickmanU base y) *
            |∑ i ∈ I, coeff i * (endpoint i : ℝ)| ≤
          1 * |∑ i ∈ I, coeff i * (endpoint i : ℝ)| :=
            mul_le_mul_of_nonneg_right hrhoLe (abs_nonneg _)
        _ = |∑ i ∈ I, coeff i * (endpoint i : ℝ)| := one_mul _

/-! ## The literal four-endpoint residual collapse -/

/-- Natural endpoints corresponding to the paper's ordered tuple
`(X_+, X, X_-, X_{1/2})`. -/
def roughPhysicalNatEndpoint
    (Xplus X Xminus Xhalf : ℕ) : Fin 4 → ℕ :=
  ![Xplus, X, Xminus, Xhalf]

/-- The genuine four-endpoint friable combination with the exact paper
coefficients. -/
noncomputable def roughPhysicalFriableCombination
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  ∑ i : Fin 4,
    roughPhysicalBlockCoefficient δ α β L i *
      (FriableAsymptotic.friableCount
        (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y : ℝ)

/-- The corresponding four-endpoint Dickman main combination. -/
noncomputable def roughPhysicalDickmanCombination
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  ∑ i : Fin 4,
    roughPhysicalBlockCoefficient δ α β L i *
      roughFriableDickmanMain
        (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y

/-- After expanding the paper coefficients, all order-one endpoint
residuals cancel into two local increments.  Only the broad increment
remains endpointwise, and it carries the explicit coefficient `δ β/L`. -/
noncomputable def roughPhysicalResidualTransition
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) : ℝ :=
  (roughFriableResidual Xplus y - roughFriableResidual X y) -
    δ * α *
      (roughFriableResidual X y - roughFriableResidual Xminus y) +
    δ * (β / L) *
      (roughFriableResidual Xhalf y - roughFriableResidual Xminus y)

/-- Exact main-plus-transition decomposition of the literal four endpoint
count.  In particular, no triangle inequality has yet been applied to the
four de Bruijn residuals. -/
theorem roughPhysicalFriableCombination_eq_main_add_residualTransition
    (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) :
    roughPhysicalFriableCombination δ α β L
        Xplus X Xminus Xhalf y =
      roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y := by
  simp only [roughPhysicalFriableCombination,
    roughPhysicalDickmanCombination, Fin.sum_univ_four]
  simp [roughPhysicalBlockCoefficient, roughPhysicalNatEndpoint]
  unfold roughPhysicalResidualTransition roughFriableResidual
  ring

/-! ## The one remaining analytic inequality -/

/-- Local Lipschitz regularity of the *actual* de Bruijn residual.  This is
the precise analytic statement not supplied by the current libraries.
It is substantially below the selector conclusion: it concerns two
natural endpoints of `Psi`, has no head conditions, and has no rowwise or
rounding content. -/
def RoughFriableResidualLocalRegularity (C : ℝ) (y : ℕ) : Prop :=
  ∀ {A B : ℕ},
    0 < A → A ≤ B →
    Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ) →
    |roughFriableResidual B y - roughFriableResidual A y| ≤
      C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) + 1

/-- On the exact initial face, the missing local regularity estimate holds
with zero residual and hence with zero analytic cost. -/
theorem roughFriableResidual_localRegularity_initial
    {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hy : 1 < y) (hBy : B ≤ y) :
    |roughFriableResidual B y - roughFriableResidual A y| = 0 := by
  rw [roughFriableResidual_eq_zero_of_le (hA.trans_le hAB) hy hBy,
    roughFriableResidual_eq_zero_of_le hA hy (hAB.trans hBy)]
  norm_num

/-- Strongest transition-complete reduction available from the verified
library.  The Dickman main term is controlled by proved compact
Lipschitz regularity.  The broad residual difference is controlled by the
closed de Bruijn theorem and gains the explicit factor `|δ β/L|`.  The
only unproved input is `RoughFriableResidualLocalRegularity`, used at the
two short endpoint pairs.

At the paper scale, both gaps are `O(X/L)`, `log y` is comparable with
`L`, and `|β/L| = O(1/L)`, so every term after the Dickman ledger is
`O(X/L^2 + 1)`. -/
theorem exists_uniform_roughPhysicalFourTransition_reduction :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ,
      ∀ {δ α β L C : ℝ} {Xplus X Xminus Xhalf y : ℕ},
      Y₀ ≤ y → 0 ≤ C →
      0 < Xhalf → Xhalf ≤ Xminus → Xminus ≤ X → X ≤ Xplus →
      (∀ i : Fin 4,
        Real.log
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) ≤
          5 * Real.log (y : ℝ)) →
      RoughFriableResidualLocalRegularity C y →
      |roughPhysicalFriableCombination δ α β L
          Xplus X Xminus Xhalf y| ≤
        (∑ i : Fin 4,
          |roughPhysicalBlockCoefficient δ α β L i| *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
              |FriableAsymptotic.dickmanU
                    (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
                FriableAsymptotic.dickmanU X y|) +
        |∑ i : Fin 4,
          roughPhysicalBlockCoefficient δ α β L i *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)| +
        (C * ((Xplus - X : ℕ) : ℝ) / Real.log (y : ℝ) + 1) +
        |δ * α| *
          (C * ((X - Xminus : ℕ) : ℝ) / Real.log (y : ℝ) + 1) +
        |δ * (β / L)| *
          (K * ((Xhalf : ℝ) + (Xminus : ℝ)) /
            Real.log (y : ℝ)) := by
  obtain ⟨K, hK, Y₁, hresidual⟩ :=
    exists_uniform_roughFriableResidual_bound
  let Y₀ : ℕ := max 2 Y₁
  refine ⟨K, hK, Y₀, ?_⟩
  intro δ α β L C Xplus X Xminus Xhalf y hY hC
    hhalf hHalfMinus hMinusX hXPlus hlogs hlocal
  have hy2 : 2 ≤ y :=
    (le_max_left 2 Y₁).trans (by simpa only [Y₀] using hY)
  have hY₁ : Y₁ ≤ y :=
    (le_max_right 2 Y₁).trans (by simpa only [Y₀] using hY)
  have hminus : 0 < Xminus := hhalf.trans_le hHalfMinus
  have hx : 0 < X := hminus.trans_le hMinusX
  have hplus : 0 < Xplus := hx.trans_le hXPlus
  have hlogY : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcoordinate5 : ∀ i : Fin 4,
      FriableAsymptotic.dickmanU
          (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y ≤ 5 := by
    intro i
    simp only [FriableAsymptotic.dickmanU]
    exact (div_le_iff₀ hlogY).2 (hlogs i)
  have hbase5 : FriableAsymptotic.dickmanU X y ≤ 5 := by
    have h := hcoordinate5 (1 : Fin 4)
    simpa only [roughPhysicalNatEndpoint] using h
  have hbase0 : 0 ≤ FriableAsymptotic.dickmanU X y := by
    simp only [FriableAsymptotic.dickmanU]
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega)))
      hlogY.le
  have hmain := roughFriableMain_abs_le_with_balanceError
    (I := Finset.univ)
    (coeff := roughPhysicalBlockCoefficient δ α β L)
    (endpoint := roughPhysicalNatEndpoint Xplus X Xminus Xhalf)
    (base := X) (y := y)
    (fun i _hi ↦ hcoordinate5 i) hbase0 hbase5
  have hupper :
      |roughFriableResidual Xplus y - roughFriableResidual X y| ≤
        C * ((Xplus - X : ℕ) : ℝ) / Real.log (y : ℝ) + 1 :=
    hlocal hx hXPlus (hlogs (0 : Fin 4))
  have hlower :
      |roughFriableResidual X y - roughFriableResidual Xminus y| ≤
        C * ((X - Xminus : ℕ) : ℝ) / Real.log (y : ℝ) + 1 :=
    hlocal hminus hMinusX (hlogs (1 : Fin 4))
  have hhalfResidual :
      |roughFriableResidual Xhalf y| ≤
        K * (Xhalf : ℝ) / Real.log (y : ℝ) := by
    apply hresidual hY₁ hhalf
    exact hlogs (3 : Fin 4)
  have hminusResidual :
      |roughFriableResidual Xminus y| ≤
        K * (Xminus : ℝ) / Real.log (y : ℝ) := by
    apply hresidual hY₁ hminus
    exact hlogs (2 : Fin 4)
  have hbroad :
      |roughFriableResidual Xhalf y - roughFriableResidual Xminus y| ≤
        K * ((Xhalf : ℝ) + (Xminus : ℝ)) /
          Real.log (y : ℝ) := by
    calc
      _ ≤ |roughFriableResidual Xhalf y| +
          |roughFriableResidual Xminus y| := abs_sub _ _
      _ ≤ K * (Xhalf : ℝ) / Real.log (y : ℝ) +
          K * (Xminus : ℝ) / Real.log (y : ℝ) :=
        add_le_add hhalfResidual hminusResidual
      _ = K * ((Xhalf : ℝ) + (Xminus : ℝ)) /
          Real.log (y : ℝ) := by ring
  rw [roughPhysicalFriableCombination_eq_main_add_residualTransition]
  calc
    |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y +
        roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| ≤
      |roughPhysicalDickmanCombination δ α β L
          Xplus X Xminus Xhalf y| +
        |roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| := abs_add_le _ _
    _ ≤ (∑ i : Fin 4,
          |roughPhysicalBlockCoefficient δ α β L i| *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
              |FriableAsymptotic.dickmanU
                    (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
                FriableAsymptotic.dickmanU X y|) +
        |∑ i : Fin 4,
          roughPhysicalBlockCoefficient δ α β L i *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)| +
        |roughPhysicalResidualTransition δ α β L
          Xplus X Xminus Xhalf y| :=
      add_le_add hmain le_rfl
    _ ≤ (∑ i : Fin 4,
          |roughPhysicalBlockCoefficient δ α β L i| *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
              |FriableAsymptotic.dickmanU
                    (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
                FriableAsymptotic.dickmanU X y|) +
        |∑ i : Fin 4,
          roughPhysicalBlockCoefficient δ α β L i *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)| +
        ((C * ((Xplus - X : ℕ) : ℝ) / Real.log (y : ℝ) + 1) +
          |δ * α| *
            (C * ((X - Xminus : ℕ) : ℝ) / Real.log (y : ℝ) + 1) +
          |δ * (β / L)| *
            (K * ((Xhalf : ℝ) + (Xminus : ℝ)) /
              Real.log (y : ℝ))) := by
      apply add_le_add le_rfl
      unfold roughPhysicalResidualTransition
      calc
        |(roughFriableResidual Xplus y - roughFriableResidual X y) -
            δ * α *
              (roughFriableResidual X y - roughFriableResidual Xminus y) +
            δ * (β / L) *
              (roughFriableResidual Xhalf y -
                roughFriableResidual Xminus y)| ≤
          |roughFriableResidual Xplus y - roughFriableResidual X y| +
            |δ * α| *
              |roughFriableResidual X y - roughFriableResidual Xminus y| +
            |δ * (β / L)| *
              |roughFriableResidual Xhalf y -
                roughFriableResidual Xminus y| := by
          calc
            _ ≤ |(roughFriableResidual Xplus y -
                    roughFriableResidual X y) -
                  δ * α *
                    (roughFriableResidual X y -
                      roughFriableResidual Xminus y)| +
                |δ * (β / L) *
                  (roughFriableResidual Xhalf y -
                    roughFriableResidual Xminus y)| := abs_add_le _ _
            _ ≤ (|roughFriableResidual Xplus y -
                    roughFriableResidual X y| +
                  |δ * α *
                    (roughFriableResidual X y -
                      roughFriableResidual Xminus y)|) +
                |δ * (β / L) *
                  (roughFriableResidual Xhalf y -
                    roughFriableResidual Xminus y)| := by
              exact add_le_add (abs_sub _ _) le_rfl
            _ = _ := by simp only [abs_mul]
        _ ≤ (C * ((Xplus - X : ℕ) : ℝ) /
                Real.log (y : ℝ) + 1) +
            |δ * α| *
              (C * ((X - Xminus : ℕ) : ℝ) /
                Real.log (y : ℝ) + 1) +
            |δ * (β / L)| *
              (K * ((Xhalf : ℝ) + (Xminus : ℝ)) /
                Real.log (y : ℝ)) := by
          exact add_le_add
            (add_le_add hupper
              (mul_le_mul_of_nonneg_left hlower (abs_nonneg _)))
            (mul_le_mul_of_nonneg_left hbroad (abs_nonneg _))
    _ = (∑ i : Fin 4,
          |roughPhysicalBlockCoefficient δ α β L i| *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ) *
              |FriableAsymptotic.dickmanU
                    (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y -
                FriableAsymptotic.dickmanU X y|) +
        |∑ i : Fin 4,
          roughPhysicalBlockCoefficient δ α β L i *
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i : ℝ)| +
        (C * ((Xplus - X : ℕ) : ℝ) / Real.log (y : ℝ) + 1) +
        |δ * α| *
          (C * ((X - Xminus : ℕ) : ℝ) / Real.log (y : ℝ) + 1) +
        |δ * (β / L)| *
          (K * ((Xhalf : ℝ) + (Xminus : ℝ)) /
            Real.log (y : ℝ)) := by ring

end

end Erdos390.WholePaper
