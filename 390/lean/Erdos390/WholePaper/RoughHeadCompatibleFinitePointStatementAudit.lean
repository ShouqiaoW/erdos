import Erdos390.WholePaper.RoughHeadCompatibleFinitePoint

/-! # Expanded statement audit for the head-compatible finite point -/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full.StructuredCells

noncomputable section

example {n h K : ℕ} (hKh : K * h ≤ n) :
    (Finset.Ioc (2 * n - K * h) (2 * n) ∪
        Finset.Ioc n (2 * n - K * h) = Finset.Ioc n (2 * n)) ∧
      Disjoint (Finset.Ioc (2 * n) (2 * n + h))
        (Finset.Ioc (2 * n - K * h) (2 * n) ∪
          Finset.Ioc n (2 * n - K * h)) ∧
      (Finset.Ioc (2 * n) (2 * n + h)).card = h ∧
      (Finset.Ioc (2 * n - K * h) (2 * n)).card = K * h ∧
      (Finset.Ioc n (2 * n - K * h)).card = n - K * h := by
  exact ⟨roughRawCandidateSet_eq_Ioc hKh,
    roughUpperBlock_disjoint_rawCandidateSet n h K,
    roughUpperBlock_card n h,
    roughHighLowerBlock_card hKh,
    roughBroadLowerBlock_card hKh⟩

example (W n h K : ℕ) (α β L : ℝ) :
    ∑ a ∈
        (Finset.Ioc (2 * n - K * h) (2 * n) ∪
          Finset.Ioc n (2 * n - K * h)),
      (if Nat.Coprime a ((primesUpTo W).prod id) then
        α * (if a ∈ Finset.Ioc (2 * n - K * h) (2 * n) then 1 else 0) +
          (β / L) *
            (if a ∈ Finset.Ioc n (2 * n - K * h) then 1 else 0)
       else 0) =
      α * ((((Finset.Ioc (2 * n - K * h) (2 * n)).filter
        (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) +
      (β / L) * ((((Finset.Ioc n (2 * n - K * h)).filter
        (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) := by
  simpa only [roughRawCandidateSet, roughHighLowerBlock,
    roughBroadLowerBlock, roughHeadCompatibleRawWeight,
    roughFiniteIndicator, roughHeadFree, roughHeadModulus] using
    sum_roughHeadCompatibleRawWeight W n h K α β L

example {W n h K : ℕ} {β L : ℝ}
    (hKh : K * h ≤ n) (hKhPos : 0 < K * h) :
    (((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
        (((primesUpTo W).prod id : ℕ) : ℝ)) *
      (((((h : ℕ) : ℝ) /
              (((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
                (((primesUpTo W).prod id : ℕ) : ℝ)) -
            (β / L) * (((n - K * h : ℕ) : ℝ))) /
          (((K * h : ℕ) : ℝ))) *
          ((Finset.Ioc (2 * n - K * h) (2 * n)).card : ℝ) +
        (β / L) *
          ((Finset.Ioc n (2 * n - K * h)).card : ℝ)) =
      ((Finset.Ioc (2 * n) (2 * n + h)).card : ℝ) := by
  simpa only [roughHeadBalancedAlpha, roughHeadDensity, roughHeadModulus,
    roughHighLowerBlock, roughBroadLowerBlock, roughUpperBlock] using
    roughHeadBalancedAlpha_card_normalization
      (W := W) (beta := β) (L := L) hKh hKhPos

example {W n h K : ℕ} {α β L : ℝ} (hKh : K * h ≤ n) :
    ∑ a ∈ Finset.Ioc n (2 * n),
      (if Nat.Coprime a ((primesUpTo W).prod id) then
        α * (if a ∈ Finset.Ioc (2 * n - K * h) (2 * n) then 1 else 0) +
          (β / L) *
            (if a ∈ Finset.Ioc n (2 * n - K * h) then 1 else 0)
       else 0) =
      α * ((((Finset.Ioc (2 * n - K * h) (2 * n)).filter
        (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) +
      (β / L) * ((((Finset.Ioc n (2 * n - K * h)).filter
        (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) := by
  simpa only [roughHighLowerBlock, roughBroadLowerBlock,
    roughHeadCompatibleRawWeight, roughFiniteIndicator, roughHeadFree,
    roughHeadModulus] using
    sum_roughHeadCompatibleRawWeight_Ioc
      (W := W) (α := α) (β := β) (L := L) hKh

example {W n h K : ℕ} {beta L : ℝ}
    (hα : 0 ≤ roughHeadBalancedAlpha W n h K beta L ∧
      roughHeadBalancedAlpha W n h K beta L ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (a : ↑(Finset.Ioc (2 * n - K * h) (2 * n) ∪
      Finset.Ioc n (2 * n - K * h))) :
    0 ≤ roughHeadCompatibleRawPoint W n h K beta L a ∧
      roughHeadCompatibleRawPoint W n h K beta L a ≤ 1 := by
  exact roughHeadCompatibleRawPoint_mem_unitInterval hα hbeta a

example (W n h K y : ℕ) (α β L : ℝ) :
    ∑ a ∈ roughRawCandidateSet n h K,
        roughHeadCompatibleRawWeight W n h K α β L a =
      ∑ label ∈ completeRoughLabelSet y (roughRawCandidateSet n h K),
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) label,
          roughHeadCompatibleRawWeight W n h K α β L a :=
  sum_roughHeadCompatibleRawRowMass W n h K y α β L

example (W : ℕ) (A : Finset ℕ) :
    (((A.filter (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card :
        ℕ) : ℤ) =
      ∑ d ∈ ((primesUpTo W).prod id).divisors,
        ArithmeticFunction.moebius d *
          (((A.filter (d ∣ ·)).card : ℕ) : ℤ) := by
  simpa only [roughHeadFree, roughHeadModulus] using
    roughHeadFree_card_eq_moebiusDivisorCounts W A

example {W lo hi y : ℕ} (hWy : W ≤ y) :
    ((((smoothInterval lo hi y).filter
        (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) :
          ℤ) =
      ∑ d ∈ ((primesUpTo W).prod id).divisors,
        ArithmeticFunction.moebius d *
          (((smoothInterval (lo / d) (hi / d) y).card : ℕ) : ℤ) := by
  simpa only [roughHeadFreeSmoothInterval, roughHeadFree,
    roughHeadModulus] using
    roughHeadFreeSmoothInterval_card_eq_divisorShift hWy

example {W lo split hi y : ℕ} {α broad : ℝ}
    (hWy : W ≤ y) :
    α * ((((smoothInterval split hi y).filter
          (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) :
            ℝ) +
        broad * ((((smoothInterval lo split y).filter
          (fun a ↦ Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) :
            ℝ) =
      ∑ d ∈ ((primesUpTo W).prod id).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          (α * ((smoothInterval (split / d) (hi / d) y).card : ℝ) +
            broad *
              ((smoothInterval (lo / d) (split / d) y).card : ℝ)) := by
  simpa only [roughHeadFreeSmoothPhysicalBlock,
    roughHeadFreeSmoothInterval, roughHeadFree, roughHeadModulus,
    roughSmoothPhysicalBlock] using
    roughHeadFreeSmoothPhysicalBlock_eq_divisorShift
      (W := W) (lo := lo) (split := split) (hi := hi) (y := y)
        (α := α) (broad := broad) hWy

/-! ## Direct coverage of the remaining public theorem surfaces -/

example (n h K : ℕ) :
    Disjoint (roughHighLowerBlock n h K)
      (roughBroadLowerBlock n h K) :=
  roughHighLowerBlock_disjoint_roughBroadLowerBlock n h K

example (W : ℕ) :
    (roughHeadZeroPattern W).modulus = roughHeadModulus W :=
  roughHeadZeroPattern_modulus W

example (W : ℕ) :
    (roughHeadZeroPattern W).factor = 1 :=
  roughHeadZeroPattern_factor W

example (W : ℕ) :
    0 < roughHeadModulus W :=
  roughHeadModulus_pos W

example (W : ℕ) :
    0 < roughHeadDensity W :=
  roughHeadDensity_pos W

example {W n h K : ℕ} {beta L : ℝ} (hKhPos : 0 < K * h) :
    roughHeadDensity W *
        (roughHeadBalancedAlpha W n h K beta L *
            (((K * h : ℕ) : ℝ)) +
          (beta / L) * (((n - K * h : ℕ) : ℝ))) =
      ((h : ℕ) : ℝ) :=
  roughHeadBalancedAlpha_length_normalization hKhPos

example {W a : ℕ} {A : Finset ℕ} :
    a ∈ roughHeadFree W A ↔
      a ∈ A ∧ Nat.Coprime a (roughHeadModulus W) :=
  mem_roughHeadFree

example (W n h K : ℕ) (beta L : ℝ)
    (a : ↑(roughRawCandidateSet n h K)) :
    roughHeadCompatibleRawPoint W n h K beta L a =
      roughHeadCompatibleRawWeight W n h K
        (roughHeadBalancedAlpha W n h K beta L) beta L a.1 :=
  roughHeadCompatibleRawPoint_apply W n h K beta L a

example {W n h K a : ℕ} {α β L : ℝ}
    (ha : a ∉ roughRawCandidateSet n h K) :
    roughHeadCompatibleRawWeight W n h K α β L a = 0 :=
  roughHeadCompatibleRawWeight_eq_zero_of_not_mem ha

example {W n h K a : ℕ} {α β L : ℝ}
    (hKh : K * h ≤ n) (ha : a ∉ Finset.Ioc n (2 * n)) :
    roughHeadCompatibleRawWeight W n h K α β L a = 0 :=
  roughHeadCompatibleRawWeight_eq_zero_of_not_mem_Ioc hKh ha

example {W n h K : ℕ} {α β L : ℝ}
    (hα : 0 ≤ α ∧ α ≤ 1)
    (hβ : 0 ≤ β / L ∧ β / L ≤ 1)
    (a : ℕ) :
    0 ≤ roughHeadCompatibleRawWeight W n h K α β L a ∧
      roughHeadCompatibleRawWeight W n h K α β L a ≤ 1 :=
  roughHeadCompatibleRawWeight_mem_unitInterval hα hβ a

example {W y : ℕ} (hWy : W ≤ y) :
    roughHeadModulus W ∈ Nat.smoothNumbers (y + 1) :=
  roughHeadModulus_mem_smoothNumbers hWy

example {W lo hi y : ℕ} (hWy : W ≤ y) :
    ((roughHeadFreeSmoothInterval W lo hi y).card : ℝ) =
      ∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : ℝ) *
          ((smoothInterval (lo / d) (hi / d) y).card : ℝ) :=
  roughHeadFreeSmoothInterval_card_real_eq_divisorShift hWy

end

end Erdos390.WholePaper
