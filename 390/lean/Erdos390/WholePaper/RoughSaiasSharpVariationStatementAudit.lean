import Erdos390.WholePaper.RoughSaiasSharpVariation

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set
open Erdos390.Full.DickmanBasic

#check roughSaiasScaledDickmanKernel_abs_le_inv_log
#check roughSaiasScaledDickmanKernel_nonpos_of_active
#check roughSaiasScaledDickmanKernel_sum_abs_succ_sub_eq

example {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t) :
    roughSaiasScaledDickmanKernel q m t =
      -rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) /
        (Real.log (q : ℝ) - Real.log t) :=
  roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub hm2 hu1

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t)
    (htactive : t ≤ (q : ℝ) / ((m + 1 : ℕ) : ℝ))
    (hum5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    roughSaiasScaledDickmanKernel q (m + 1) t ≤
      roughSaiasScaledDickmanKernel q m t :=
  roughSaiasScaledDickmanKernel_succ_le_of_active
    hq1 hm2 htpos htactive hum5

example {q₁ q₀ m : ℕ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₀) (hm2 : 2 ≤ m)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ (q₁ : ℝ) / (m : ℝ))
    (hu₀5 : roughSaiasBaseFreeDickmanCoordinate q₀ m t ≤ 5) :
    roughSaiasScaledDickmanKernel q₁ m t ≤
      roughSaiasScaledDickmanKernel q₀ m t :=
  roughSaiasScaledDickmanKernel_le_of_quotient_le_of_active
    hq₁ hq hm2 htpos htactive hu₀5

example {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ ((X / (m + 1) : ℕ) : ℝ) /
      ((m + 1 : ℕ) : ℝ))
    (hum5 : roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
      roughSaiasScaledDickmanKernel (X / m) m t :=
  roughSaiasScaledDickmanKernel_hyperbola_succ_le_of_active
    hm2 hnextX htpos htactive hum5

example {q₁ q₀ m : ℕ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₀) (hm2 : 2 ≤ m)
    (hu₀5 : Real.log (q₀ : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q₁ (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q₀ m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
            roughSaiasScaledDickmanKernel q₀ m t) :=
  roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common
    hq₁ hq hm2 hu₀5

example {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    (hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeFractionalIntegral (X / m) m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t) :=
  roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_common
    hm2 hnextX hum5

example {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    (hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t))
      MeasureTheory.volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) :=
  roughSaiasHyperbolaFractionalTransition_intervalIntegrable
    hm2 hnextX hum5

example {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      1 / Real.log (a : ℝ) :=
  roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_inv_log
    ha2 hab hbX htpos hactive hface

example {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) =
      roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t :=
  roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_eq
    ha2 hab hbX htpos hactive hface

example {X a c b : ℕ} (ha2 : 2 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
    (hbX : b ≤ X) {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a c,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a c,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5)
    (hinactive : ∀ m ∈ Finset.Ioc c b,
      ((X / m : ℕ) : ℝ) / (m : ℝ) < t) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      2 / Real.log (a : ℝ) :=
  roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff
    ha2 hac hcb hbX htpos hactive hface hinactive

example {X m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ((X / n : ℕ) : ℝ) / (n : ℝ) ≤
      ((X / m : ℕ) : ℝ) / (m : ℝ) :=
  roughSaiasNaturalHyperbolaSupport_antitone hm hmn

example {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5 :=
  roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
    ha2 ham hmX ht1 hu5

example {X a : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
  roughSaiasNat_le_rpow_five hX ha2 hu5

example {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 :=
  roughSaiasNatHyperbolaLogRatio_le_five ha2 ham hmX hu5

example {X a b m : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeFractionalIntegral (X / m) m =
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t) :=
  roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_firstCap
    ha2 hab hbX hm hu5

example {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      2 / Real.log (a : ℝ) :=
  roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log
    ha2 hab hbX ht1 hu5

example {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X) :
    Real.log ((X / (m + 1) : ℕ) : ℝ) /
        Real.log ((m + 1 : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
  roughSaiasNatHyperbolaLogRatio_succ_le hm2 hnextX

example {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
              Real.log ((m + 1 : ℕ) : ℝ)) -
          rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) ≤
      1 :=
  sum_abs_rho_natHyperbolaLogRatio_succ_sub_le_one
    ha2 hab hbX hu5

example {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m|) ≤
      2 / Real.log (a : ℝ) :=
  roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log
    ha2 hab hbX hu5

example {q a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) {t : ℝ}
    (htpos : 0 < t) (htq : t ≤ (q : ℝ)) :
    roughSaiasBaseFreeDickmanCoordinate q b t ≤
      roughSaiasBaseFreeDickmanCoordinate q a t :=
  roughSaiasBaseFreeDickmanCoordinate_antitone_base
    ha2 hab htpos htq

example {q a b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a) (hab : a ≤ b)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ (q : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) ≤
      1 / Real.log (a : ℝ) :=
  roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_inv_log
    hq1 ha2 hab htpos hactive hface

example {q a b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a) (hab : a ≤ b)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ (q : ℝ) / (b : ℝ))
    (hua5 : roughSaiasBaseFreeDickmanCoordinate q a t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) ≤
      1 / Real.log (a : ℝ) :=
  roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_inv_log_of_last_active
    hq1 ha2 hab htpos htactive hua5

example {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasScaledDickmanKernel q m t = 0 :=
  roughSaiasScaledDickmanKernel_eq_zero_of_div_lt hq1 hm2 ht

example {q a c b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a)
    (hac : a ≤ c) (hcb : c ≤ b) {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a c,
      t ≤ (q : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a c,
      roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5)
    (hinactive : ∀ m ∈ Finset.Ioc c b,
      (q : ℝ) / (m : ℝ) < t) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) ≤
      2 / Real.log (a : ℝ) :=
  roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_two_inv_log_of_cutoff
    hq1 ha2 hac hcb htpos hactive hface hinactive

#check roughSaiasFullyRealHyperbolaCoordinate
#check roughSaiasFullyRealHyperbolaScaledDickmanKernel
#check roughSaiasFullyRealHyperbolaCellKernelOscillation
#check roughSaiasFullyRealHyperbolaCellFractionalOscillation
#check roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
#check roughSaiasFullyRealHyperbolaCoordinate_le_five
#check roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
#check sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log

example {X a : ℕ} {s t : ℝ} (hX : 0 < X) (ha2 : 2 ≤ a)
    (has : (a : ℝ) ≤ s) (hsX : s ≤ (X : ℝ)) (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5 :=
  roughSaiasFullyRealHyperbolaCoordinate_le_five
    hX ha2 has hsX ht1 hu5

example {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s -
        roughSaiasFullyRealBaseFreeFractionalIntegral
          ((X : ℝ) / (m + 1 : ℕ)) (m + 1 : ℕ)| ≤
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m :=
  roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
    hX ha2 hab hbX hm hu5 hs

example {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) ≤
      2 / Real.log (a : ℝ) :=
  sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log
    hX ha2 hab hbX hu5

end Erdos390.WholePaper
