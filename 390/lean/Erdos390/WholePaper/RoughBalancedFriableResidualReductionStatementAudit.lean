import Erdos390.WholePaper.RoughBalancedFriableResidualReduction

/-! # Expanded statement audit for balanced friable residual cancellation -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

example {X y : ℕ} (hX : 0 < X) (hy : 1 < y) (hXy : X ≤ y) :
    (FriableAsymptotic.friableCount X y : ℝ) -
        (X : ℝ) * rho (FriableAsymptotic.dickmanU X y) = 0 := by
  simpa only [roughFriableResidual, roughFriableDickmanMain] using
    roughFriableResidual_eq_zero_of_le hX hy hXy

example {X₀ X₁ y Z : ℕ}
    (hX₀ : 0 < X₀) (hX₁ : 0 < X₁)
    (hyZ : y ≤ Z) (hX₀Z : X₀ ≤ Z) (hX₁Z : X₁ ≤ Z) :
    roughFriableResidual X₁ y - roughFriableResidual X₀ y =
      (roughFriableReverseMainDefect X₁ y Z -
          roughFriableReverseMainDefect X₀ y Z) -
        ∑ p ∈ ((Z + 1).primesBelow \ (y + 1).primesBelow),
          (roughFriableResidual (X₁ / p) p -
            roughFriableResidual (X₀ / p) p) := by
  simpa only [roughReversePrimeInterval] using
    roughFriableResidual_difference_reverseRecurrence
      hX₀ hX₁ hyZ hX₀Z hX₁Z

example (δ α β L : ℝ) (Xplus X Xminus Xhalf y : ℕ) :
    (∑ i : Fin 4,
        roughPhysicalBlockCoefficient δ α β L i *
          (FriableAsymptotic.friableCount
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y : ℝ)) =
      (∑ i : Fin 4,
        roughPhysicalBlockCoefficient δ α β L i *
          roughFriableDickmanMain
            (roughPhysicalNatEndpoint Xplus X Xminus Xhalf i) y) +
      ((roughFriableResidual Xplus y - roughFriableResidual X y) -
        δ * α *
          (roughFriableResidual X y - roughFriableResidual Xminus y) +
        δ * (β / L) *
          (roughFriableResidual Xhalf y -
            roughFriableResidual Xminus y)) := by
  simpa only [roughPhysicalFriableCombination,
    roughPhysicalDickmanCombination, roughPhysicalResidualTransition] using
    roughPhysicalFriableCombination_eq_main_add_residualTransition
      δ α β L Xplus X Xminus Xhalf y

example :
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
            Real.log (y : ℝ)) :=
  exists_uniform_roughPhysicalFourTransition_reduction

/-! ## Supporting public API -/

example (y : ℕ) : roughFriableDickmanMain 0 y = 0 :=
  roughFriableDickmanMain_zero y

example (y : ℕ) : roughFriableResidual 0 y = 0 :=
  roughFriableResidual_zero y

example (X y : ℕ) :
    (FriableAsymptotic.friableCount X y : ℝ) =
      roughFriableDickmanMain X y + roughFriableResidual X y :=
  roughFriableCount_eq_main_add_residual X y

example :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableResidual X y| ≤
        K * (X : ℝ) / Real.log (y : ℝ) :=
  exists_uniform_roughFriableResidual_bound

example {X y Z : ℕ} (hX : 0 < X) (hyZ : y ≤ Z) (hXZ : X ≤ Z) :
    roughFriableResidual X y =
      roughFriableReverseMainDefect X y Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughFriableResidual (X / p) p :=
  roughFriableResidual_reverseRecurrence hX hyZ hXZ

example {X y Z : ℕ} (hyZ : y ≤ Z) (hXZ : X ≤ Z) :
    roughFriableResidual X y =
      roughFriableReverseMainDefect X y Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughFriableResidual (X / p) p :=
  roughFriableResidual_reverseRecurrence_all hyZ hXZ

example {X₀ X₁ y Z : ℕ}
    (hyZ : y ≤ Z) (hX₀Z : X₀ ≤ Z) (hX₁Z : X₁ ≤ Z) :
    roughFriableResidual X₁ y - roughFriableResidual X₀ y =
      (roughFriableReverseMainDefect X₁ y Z -
          roughFriableReverseMainDefect X₀ y Z) -
        ∑ p ∈ roughReversePrimeInterval y Z,
          (roughFriableResidual (X₁ / p) p -
            roughFriableResidual (X₀ / p) p) :=
  roughFriableResidual_difference_reverseRecurrence_all hyZ hX₀Z hX₁Z

example {a b : ℝ} (ha5 : a ≤ 5) (hb5 : b ≤ 5) :
    |rho a - rho b| ≤ |a - b| :=
  roughRho_abs_sub_le_abs_of_le_five ha5 hb5

example {ι : Type*} (I : Finset ι)
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
            FriableAsymptotic.dickmanU base y| :=
  roughBalancedFriableMain_abs_le I coeff endpoint base y
    hbalance hendpoint5 hbase5

example {ι : Type*} (I : Finset ι)
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
      |∑ i ∈ I, coeff i * (endpoint i : ℝ)| :=
  roughFriableMain_abs_le_with_balanceError I coeff endpoint base y
    hendpoint5 hbase0 hbase5

example {A B y : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (hy : 1 < y) (hBy : B ≤ y) :
    |roughFriableResidual B y - roughFriableResidual A y| = 0 :=
  roughFriableResidual_localRegularity_initial hA hAB hy hBy

end

end Erdos390.WholePaper
