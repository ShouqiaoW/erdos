import Erdos390.WholePaper.RoughFixedHeadFriableShift

/-! # Expanded statement audit for the available fixed-head friable shift -/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

example (A : ℕ) {r p : ℝ}
    (hA : 1 ≤ A) (hAr : (A : ℝ) ≤ r) (hrA : r < (A : ℝ) + 1)
    (hp : (2 : ℝ) ≤ p)
    (hb5 : Real.log r / Real.log p ≤ 5) :
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| ≤ 3 :=
  roughRhoFloorKernel_stability A hA hAr hrA hp hb5

example {X y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdX : d ≤ X)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((X / d : ℕ) : ℝ) *
          rho (FriableAsymptotic.dickmanU (X / d) y) -
        ((X : ℝ) * rho (FriableAsymptotic.dickmanU X y)) / (d : ℝ)| ≤
      3 + (X : ℝ) * Real.log (d : ℝ) /
        ((d : ℝ) * Real.log (y : ℝ)) :=
  roughFriableMain_fixedDivisorShift hy hd hdX hlogX

example (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y d : ℕ},
      Y₀ ≤ y →
      d ∈ ((primesUpTo W).prod id).divisors →
      d ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(FriableAsymptotic.friableCount (X / d) y : ℝ) -
          (FriableAsymptotic.friableCount X y : ℝ) / (d : ℝ)| ≤
        K * (X : ℝ) / ((d : ℝ) * Real.log (y : ℝ)) + 3 := by
  simpa only [roughHeadModulus] using
    exists_uniform_roughFixedHead_friableCount_shift_bound W

example {lo split hi y : ℕ} {alpha broad : ℝ}
    (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi) :
    roughSmoothPhysicalBlock lo split hi y alpha broad =
      alpha *
          ((FriableAsymptotic.friableCount hi y : ℝ) -
            (FriableAsymptotic.friableCount split y : ℝ)) +
        broad *
          ((FriableAsymptotic.friableCount split y : ℝ) -
            (FriableAsymptotic.friableCount lo y : ℝ)) :=
  roughSmoothPhysicalBlock_eq_friableEndpoints hloSplit hSplitHi

example (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ,
      ∀ {lo split hi y d : ℕ} {alpha broad : ℝ},
      Y₀ ≤ y →
      d ∈ ((primesUpTo W).prod id).divisors →
      d ≤ lo → lo ≤ split → split ≤ hi →
      Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      K *
          (|alpha| * ((hi : ℝ) + (split : ℝ)) +
            |broad| * ((split : ℝ) + (lo : ℝ))) /
        ((d : ℝ) * Real.log (y : ℝ)) +
      6 * (|alpha| + |broad|) := by
  simpa only [roughHeadModulus] using
    exists_uniform_roughFixedHead_smoothPhysicalBlock_shift_bound W

example (W : ℕ) :
    (∑ d ∈ ((primesUpTo W).prod id).divisors,
        (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
      ((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
        (((primesUpTo W).prod id : ℕ) : ℝ) := by
  simpa only [roughHeadModulus, roughHeadDensity] using
    roughHead_moebius_inv_sum_eq_density W

example (W : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ,
      ∀ {lo split hi y : ℕ} {alpha broad : ℝ},
      Y₀ ≤ y → W ≤ y → ((primesUpTo W).prod id) ≤ lo →
      lo ≤ split → split ≤ hi →
      Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughHeadFreeSmoothPhysicalBlock W lo split hi y alpha broad -
          (((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
            (((primesUpTo W).prod id : ℕ) : ℝ)) *
            roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
        ∑ d ∈ ((primesUpTo W).prod id).divisors,
          |(ArithmeticFunction.moebius d : ℝ)| *
            (K *
                (|alpha| * ((hi : ℝ) + (split : ℝ)) +
                  |broad| * ((split : ℝ) + (lo : ℝ))) /
              ((d : ℝ) * Real.log (y : ℝ)) +
            6 * (|alpha| + |broad|)) := by
  simpa only [roughHeadModulus, roughHeadDensity] using
    exists_uniform_roughHeadFree_smoothPhysicalBlock_density_bound W

end

end Erdos390.WholePaper
