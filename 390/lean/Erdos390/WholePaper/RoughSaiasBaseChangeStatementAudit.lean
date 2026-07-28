import Erdos390.WholePaper.RoughSaiasBaseChange

/-! Statement checks for the exact base-free sawtooth substitution. -/

open scoped Interval

namespace Erdos390.WholePaper

open Set
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

example (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t =
      (Real.log (q : ℝ) - Real.log t) / Real.log (m : ℝ) :=
  roughSaiasBaseFreeDickmanCoordinate_eq_sub_div q m t

example {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t) (htq : t ≤ (q : ℝ)) :
    roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤
      roughSaiasBaseFreeDickmanCoordinate q m t :=
  roughSaiasBaseFreeDickmanCoordinate_succ_le hm2 htpos htq

example (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t -
        roughSaiasBaseFreeDickmanCoordinate q (m + 1) t =
      (Real.log (q : ℝ) - Real.log t) *
        (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
  roughSaiasBaseFreeDickmanCoordinate_sub_succ q m t

example {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t) (ht : t ≤ (q : ℝ) / (m : ℝ)) :
    1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t :=
  one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div hm2 htpos ht

example (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeFractionalKernel q m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasScaledDickmanKernel q m t :=
  roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled q m t

example (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeFractionalKernel q (m + 1) t -
        roughSaiasBaseFreeFractionalKernel q m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t) :=
  roughSaiasBaseFreeFractionalKernel_succ_sub q m t

example (q m : ℕ) (t : ℝ) :
    roughSaiasScaledDickmanKernel q (m + 1) t -
        roughSaiasScaledDickmanKernel q m t =
      (roughSaiasDickmanDerivative
          (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t) -
        roughSaiasDickmanDerivative
          (roughSaiasBaseFreeDickmanCoordinate q m t)) /
          Real.log ((m + 1 : ℕ) : ℝ) +
        roughSaiasDickmanDerivative
            (roughSaiasBaseFreeDickmanCoordinate q m t) *
          (1 / Real.log ((m + 1 : ℕ) : ℝ) -
            1 / Real.log (m : ℝ)) :=
  roughSaiasScaledDickmanKernel_succ_sub q m t

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasBaseFreeFractionalKernel q m t = 0 :=
  roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt hq1 hm2 ht

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) :
    Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤
      Real.log (q : ℝ) / Real.log (m : ℝ) :=
  roughSaiasNatQuotientLogRatio_succ_le hq1 hm2

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    (q : ℝ) / ((m + 1 : ℕ) : ℝ) < (m : ℝ) ^ (5 : ℝ) :=
  roughSaiasNatQuotient_div_succ_lt_rpow_five hq1 hm2 hu5

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    (∫ t in (m : ℝ) ^ (5 : ℝ)..
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
      roughSaiasBaseFreeFractionalKernel q (m + 1) t) = 0 :=
  roughSaiasBaseFreeFractionalKernel_succ_tail_eq_zero hq1 hm2 hu5

example {q m : ℕ} (hm2 : 2 ≤ m) (v : ℝ) :
    (Real.log (m : ℝ) * (m : ℝ) ^ v) *
        roughSaiasBaseFreeFractionalKernel q m ((m : ℝ) ^ v) =
      roughSaiasDickmanDerivative
          (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
        roughSaiasFractionalWeight m v :=
  roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian hm2 v

example {q m : ℕ} (hm2 : 2 ≤ m) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
      roughSaiasBaseFreeFractionalIntegral q m :=
  roughSaiasFractionalIntegral_eq_baseFree hm2

example {q m : ℕ} (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable (roughSaiasBaseFreeFractionalKernel q m)
      MeasureTheory.volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) :=
  roughSaiasBaseFreeFractionalKernel_intervalIntegrable hm2 hu5

example {q m : ℕ} (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5)
    (husucc5 :
      Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (roughSaiasBaseFreeFractionalKernel q (m + 1) t -
            roughSaiasBaseFreeFractionalKernel q m t)) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t :=
  roughSaiasBaseFreeFractionalIntegral_succ_sub hm2 hum5 husucc5

example {q m : ℕ} (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5)
    (husucc5 :
      Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q (m + 1) t -
              roughSaiasScaledDickmanKernel q m t)) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t :=
  roughSaiasBaseFreeFractionalIntegral_succ_sub_factored
    hm2 hum5 husucc5

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t) :=
  roughSaiasBaseFreeFractionalIntegral_succ_sub_eq_common
    hq1 hm2 hum5

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (((roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t) -
              roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q m t)) /
              Real.log ((m + 1 : ℕ) : ℝ)) +
            roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q m t) *
              (1 / Real.log ((m + 1 : ℕ) : ℝ) -
                1 / Real.log (m : ℝ))) :=
  roughSaiasBaseFreeFractionalIntegral_succ_sub_eq_translation
    hq1 hm2 hum5

example {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasG m
        (Real.log (q : ℝ) / Real.log (m : ℝ)) =
      rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
        roughSaiasBaseFreeFractionalIntegral q m :=
  roughSaiasG_at_natQuotient_eq_baseFree hm2

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasG (m + 1)
          (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
        roughSaiasG m
          (Real.log (q : ℝ) / Real.log (m : ℝ)) =
      (rho (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
        rho (Real.log (q : ℝ) / Real.log (m : ℝ))) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q (m + 1) t -
              roughSaiasScaledDickmanKernel q m t) :=
  roughSaiasG_at_natQuotient_succ_sub_eq_common hq1 hm2 hum5

example {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalMain q m =
      (q : ℝ) *
        (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
          roughSaiasBaseFreeFractionalIntegral q m) :=
  roughSaiasNaturalMain_eq_rho_sub_baseFree hm2

example {X m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight (X / m) m :=
  roughSaiasNaturalQuotientThetaWeight_eq_baseFree hm2

example {X m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeNaturalThetaWeight (X / m) m :=
  roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree hm2

example {X q m : ℕ} (hm2 : 2 ≤ m)
    (hnext : X / (m + 1) = q) (hnow : X / m = q) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
        roughSaiasBaseFreeNaturalThetaWeight q m :=
  roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree_on_block
    hm2 hnext hnow

example {X y Z : ℕ} (hy1 : 1 ≤ y) (hyZ : y < Z) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      roughSaiasBaseFreeIntegerConsistency X y Z :=
  roughSaiasNaturalIntegerAbelConsistencyDefect_eq_baseFree hy1 hyZ

example {X y Z : ℕ} (hy1 : 1 ≤ y) (hyZ : y < Z) :
    roughSaiasSignedAbelCenter X y Z =
      roughSaiasBaseFreeIntegerConsistency X y Z +
        roughSaiasFractionalThetaErrorTransfer X y Z :=
  roughSaiasSignedAbelCenter_eq_baseFree_add_fractionalTheta hy1 hyZ

end

end Erdos390.WholePaper
