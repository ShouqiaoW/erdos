import Erdos390.WholePaper.RoughSaiasBaseChange
import Erdos390.WholePaper.RoughSaiasFullyRealNormalForm

/-!
# Sharp active-face variation of the base-free Saias kernel

On the active Dickman faces the apparently competing changes in the
Dickman coordinate and in `1 / log m` cancel algebraically.  If

`u_m(t) = (log q - log t) / log m`,

then

`rho'(u_m(t)) / log m = -rho (u_m(t) - 1) / (log q - log t)`.

The denominator on the right is independent of `m`.  Consequently, while
`t <= q / m` and the coordinates remain on the five constructed faces, the
scaled kernel is antitone as the base increases.  Its absolute consecutive
variation on an all-active finite block therefore telescopes exactly.  No
triangle inequality between the coordinate and coefficient changes is used.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- Elementary evaluation of the inverse-square majorant on a positive
interval.  This is proved directly from the fundamental theorem so the
sharp-variation argument does not depend on a particular exported name for
the integer-power integral formula. -/
private theorem roughSaias_integral_one_div_sq_eq
    {A : ℝ} (hA : 1 ≤ A) :
    (∫ t in (1 : ℝ)..A, 1 / t ^ (2 : ℕ)) = 1 - 1 / A := by
  have hzeroNotMem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) A :=
    Set.notMem_uIcc_of_lt (by norm_num) (zero_lt_one.trans_le hA)
  have hint : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) A := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := A) (n := (-2 : ℤ))
        (Or.inr hzeroNotMem))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => -(x⁻¹))
    (f' := fun x : ℝ => 1 / x ^ (2 : ℕ))
    (a := (1 : ℝ)) (b := A) (fun x hx => by
      rw [Set.uIcc_of_le hA] at hx
      have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans_le hx.1)
      convert (hasDerivAt_inv hx0).neg using 1
      all_goals simp [one_div]) hint
  simp only [one_div]
  calc
    (∫ t in (1 : ℝ)..A, (t ^ (2 : ℕ))⁻¹) = -A⁻¹ + 1 := by
      simpa [one_div] using hfund
    _ = 1 - A⁻¹ := by ring

/-- On an active face, `u_m(t) * log m = log q - log t` cancels the
base logarithm in the scaled Dickman kernel. -/
theorem roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t) :
    roughSaiasScaledDickmanKernel q m t =
      -rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) /
        (Real.log (q : ℝ) - Real.log t) := by
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hcoordinate :
      roughSaiasBaseFreeDickmanCoordinate q m t *
          Real.log (m : ℝ) =
        Real.log (q : ℝ) - Real.log t := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    exact div_mul_cancel₀ _ hlogm
  unfold roughSaiasScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1, div_div, hcoordinate]

/-- Uniform envelope for the scaled kernel on the five constructed faces. -/
theorem roughSaiasScaledDickmanKernel_abs_le_inv_log
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    |roughSaiasScaledDickmanKernel q m t| ≤
      1 / Real.log (m : ℝ) := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  unfold roughSaiasScaledDickmanKernel
  rw [abs_div, abs_of_pos hlogm]
  exact div_le_div_of_nonneg_right
    (roughSaiasDickmanDerivative_abs_le_one hu5) hlogm.le

/-- The scaled kernel is nonpositive on an active constructed face. -/
theorem roughSaiasScaledDickmanKernel_nonpos_of_active
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (hu1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t)
    (hu5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    roughSaiasScaledDickmanKernel q m t ≤ 0 := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hrho :
      0 ≤ rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  unfold roughSaiasScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1]
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho)
      (by linarith)) hlogm.le

/-- The transformed Dickman coordinate is antitone in the natural base on
the positive segment `t ≤ q`.  This is the arbitrary-base version of the
consecutive-coordinate lemma in `RoughSaiasBaseChange`. -/
theorem roughSaiasBaseFreeDickmanCoordinate_antitone_base
    {q a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) {t : ℝ}
    (htpos : 0 < t) (htq : t ≤ (q : ℝ)) :
    roughSaiasBaseFreeDickmanCoordinate q b t ≤
      roughSaiasBaseFreeDickmanCoordinate q a t := by
  have hnumerator : 0 ≤ Real.log (q : ℝ) - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log htpos htq)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast hab)
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
    roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  exact div_le_div_of_nonneg_left hnumerator hloga hlogab

/-- On an active face, decreasing the quotient while holding the base fixed
makes the scaled kernel more negative.  This is the quotient-direction
counterpart of `roughSaiasScaledDickmanKernel_succ_le_of_active`. -/
theorem roughSaiasScaledDickmanKernel_le_of_quotient_le_of_active
    {q₁ q₀ m : ℕ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₀) (hm2 : 2 ≤ m)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ (q₁ : ℝ) / (m : ℝ))
    (hu₀5 : roughSaiasBaseFreeDickmanCoordinate q₀ m t ≤ 5) :
    roughSaiasScaledDickmanKernel q₁ m t ≤
      roughSaiasScaledDickmanKernel q₀ m t := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hq₁pos : 0 < (q₁ : ℝ) := by
    exact_mod_cast (show 0 < q₁ by omega)
  have hq₀pos : 0 < (q₀ : ℝ) := by
    exact_mod_cast (show 0 < q₀ by omega)
  have htq₁ : t ≤ (q₁ : ℝ) :=
    htactive.trans (div_le_self hq₁pos.le
      (by exact_mod_cast (show 1 ≤ m by omega)))
  have htq₀ : t ≤ (q₀ : ℝ) :=
    htq₁.trans (by exact_mod_cast hq)
  have hactive₀ : t ≤ (q₀ : ℝ) / (m : ℝ) := by
    exact htactive.trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hq) hmpos.le)
  have hu₁1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q₁ m t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hm2 htpos htactive
  have hu₀1 : 1 ≤ roughSaiasBaseFreeDickmanCoordinate q₀ m t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hm2 htpos hactive₀
  have hcoord : roughSaiasBaseFreeDickmanCoordinate q₁ m t ≤
      roughSaiasBaseFreeDickmanCoordinate q₀ m t := by
    have hlogq : Real.log (q₁ : ℝ) ≤ Real.log (q₀ : ℝ) :=
      Real.log_le_log hq₁pos (by exact_mod_cast hq)
    have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
      roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    exact div_le_div_of_nonneg_right
      (sub_le_sub_right hlogq (Real.log t)) hlogm.le
  have hu₁5 : roughSaiasBaseFreeDickmanCoordinate q₁ m t ≤ 5 :=
    hcoord.trans hu₀5
  have hrho :
      rho (roughSaiasBaseFreeDickmanCoordinate q₀ m t - 1) ≤
        rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) := by
    exact roughRho_antitoneOn_zero_five
      (show roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (show roughSaiasBaseFreeDickmanCoordinate q₀ m t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (by linarith)
  have htq₁lt : t < (q₁ : ℝ) := by
    exact htactive.trans_lt (div_lt_self hq₁pos hmone)
  have hdenom₁ : 0 < Real.log (q₁ : ℝ) - Real.log t := by
    exact sub_pos.mpr (Real.strictMonoOn_log htpos hq₁pos htq₁lt)
  have hdenom₀ : 0 < Real.log (q₀ : ℝ) - Real.log t := by
    exact sub_pos.mpr
      (Real.strictMonoOn_log htpos hq₀pos (htq₁lt.trans_le
        (by exact_mod_cast hq)))
  have hdenomLe : Real.log (q₁ : ℝ) - Real.log t ≤
      Real.log (q₀ : ℝ) - Real.log t := by
    exact sub_le_sub_right (Real.log_le_log hq₁pos
      (by exact_mod_cast hq)) _
  have hrhoNonneg :
      0 ≤ rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  rw [roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub hm2 hu₁1,
    roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub hm2 hu₀1]
  rw [neg_div, neg_div]
  apply neg_le_neg
  calc
    rho (roughSaiasBaseFreeDickmanCoordinate q₀ m t - 1) /
          (Real.log (q₀ : ℝ) - Real.log t) ≤
        rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) /
          (Real.log (q₀ : ℝ) - Real.log t) :=
      div_le_div_of_nonneg_right hrho hdenom₀.le
    _ ≤ rho (roughSaiasBaseFreeDickmanCoordinate q₁ m t - 1) /
          (Real.log (q₁ : ℝ) - Real.log t) :=
      div_le_div_of_nonneg_left hrhoNonneg hdenom₁ hdenomLe

/-- The scaled kernel itself vanishes beyond its natural support `q / m`.
This is the smooth-factor analogue of
`roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt`; it does not use the
sawtooth factor. -/
theorem roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasScaledDickmanKernel q m t = 0 := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htpos : 0 < t :=
    (div_pos hqpos hmpos).trans ht
  have hq_lt_tm : (q : ℝ) < t * (m : ℝ) :=
    (div_lt_iff₀ hmpos).mp ht
  have hloglt :
      Real.log (q : ℝ) < Real.log t + Real.log (m : ℝ) := by
    have h := Real.strictMonoOn_log hqpos (mul_pos htpos hmpos) hq_lt_tm
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  have harg : roughSaiasBaseFreeDickmanCoordinate q m t < 1 := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
      div_lt_one (Real.log_pos hmone)]
    linarith
  unfold roughSaiasScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

/-- Consecutive scaled kernels are antitone as long as the next base is
still active.  The proof uses the common-denominator identity above, so the
coordinate change and the `1 / log m` change are not estimated separately. -/
theorem roughSaiasScaledDickmanKernel_succ_le_of_active
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t)
    (htactive : t ≤ (q : ℝ) / ((m + 1 : ℕ) : ℝ))
    (hum5 : roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    roughSaiasScaledDickmanKernel q (m + 1) t ≤
      roughSaiasScaledDickmanKernel q m t := by
  have hdivMono :
      (q : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (q : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast (show m ≤ m + 1 by omega))
  have htactiveNow : t ≤ (q : ℝ) / (m : ℝ) :=
    htactive.trans hdivMono
  have htq : t ≤ (q : ℝ) := by
    exact htactive.trans
      (div_le_self (by positivity)
        (by exact_mod_cast (show 1 ≤ m + 1 by omega)))
  have huNow1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hm2 htpos htactiveNow
  have huNext1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate q (m + 1) t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      (by omega) htpos htactive
  have huNextNow :
      roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤
        roughSaiasBaseFreeDickmanCoordinate q m t :=
    roughSaiasBaseFreeDickmanCoordinate_succ_le hm2 htpos htq
  have huNext5 :
      roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤ 5 :=
    huNextNow.trans hum5
  have hrho :
      rho (roughSaiasBaseFreeDickmanCoordinate q m t - 1) ≤
        rho (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t - 1) := by
    exact roughRho_antitoneOn_zero_five
      (show roughSaiasBaseFreeDickmanCoordinate q (m + 1) t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (show roughSaiasBaseFreeDickmanCoordinate q m t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (by linarith)
  have hlogNext : Real.log (((m + 1 : ℕ) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.log_pos
      (by exact_mod_cast (show 1 < m + 1 by omega)))
  have hcoordinateNext :
      roughSaiasBaseFreeDickmanCoordinate q (m + 1) t *
          Real.log (((m + 1 : ℕ) : ℝ)) =
        Real.log (q : ℝ) - Real.log t := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    exact div_mul_cancel₀ _ hlogNext
  have hdenom : 0 < Real.log (q : ℝ) - Real.log t := by
    rw [← hcoordinateNext]
    exact mul_pos (lt_of_lt_of_le zero_lt_one huNext1)
      (Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega)))
  rw [roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub
      (m := m + 1) (by omega) huNext1,
    roughSaiasScaledDickmanKernel_eq_neg_rho_div_log_sub
      (m := m) hm2 huNow1]
  exact div_le_div_of_nonneg_right (neg_le_neg hrho) hdenom.le

/-- Consecutive monotonicity along the natural hyperbola path
`m ↦ (X/m,m)`.  Both the quotient decrease and the base increase reinforce
the same signed kernel variation while the next point remains active. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_succ_le_of_active
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ ((X / (m + 1) : ℕ) : ℝ) /
      ((m + 1 : ℕ) : ℝ))
    (hum5 : roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
      roughSaiasScaledDickmanKernel (X / m) m t := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) :=
    Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  have hdiv : ((X / (m + 1) : ℕ) : ℝ) /
        ((m + 1 : ℕ) : ℝ) ≤
      ((X / (m + 1) : ℕ) : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity)
      (by exact_mod_cast hmPos) (by exact_mod_cast (Nat.le_succ m))
  have htactiveNow : t ≤ ((X / (m + 1) : ℕ) : ℝ) / (m : ℝ) :=
    htactive.trans hdiv
  have hfaceNextNow :
      roughSaiasBaseFreeDickmanCoordinate (X / (m + 1)) m t ≤ 5 := by
    have hcoord :
        roughSaiasBaseFreeDickmanCoordinate (X / (m + 1)) m t ≤
          roughSaiasBaseFreeDickmanCoordinate (X / m) m t := by
      have hqNextPosR : 0 < ((X / (m + 1) : ℕ) : ℝ) := by positivity
      have hlogq : Real.log ((X / (m + 1) : ℕ) : ℝ) ≤
          Real.log ((X / m : ℕ) : ℝ) :=
        Real.log_le_log hqNextPosR (by exact_mod_cast hqLe)
      have hlogm : 0 < Real.log (m : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < m by omega))
      rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
        roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
      exact div_le_div_of_nonneg_right
        (sub_le_sub_right hlogq (Real.log t)) hlogm.le
    exact hcoord.trans hum5
  calc
    roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
        roughSaiasScaledDickmanKernel (X / (m + 1)) m t :=
      roughSaiasScaledDickmanKernel_succ_le_of_active
        hqNext hm2 htpos htactive hfaceNextNow
    _ ≤ roughSaiasScaledDickmanKernel (X / m) m t :=
      roughSaiasScaledDickmanKernel_le_of_quotient_le_of_active
        hqNext hqLe hm2 htpos htactiveNow hum5

/-- A simultaneous quotient drop and base increment has one exact
common-range correction integral.  The artificial endpoint tail still
vanishes: it is enough that the larger old quotient lies on the five
constructed faces. -/
theorem roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common
    {q₁ q₀ m : ℕ} (hq₁ : 1 ≤ q₁) (hq : q₁ ≤ q₀) (hm2 : 2 ≤ m)
    (hu₀5 : Real.log (q₀ : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q₁ (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q₀ m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
            roughSaiasScaledDickmanKernel q₀ m t) := by
  have hq₁pos : 0 < (q₁ : ℝ) := by
    exact_mod_cast (show 0 < q₁ by omega)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogq : Real.log (q₁ : ℝ) ≤ Real.log (q₀ : ℝ) :=
    Real.log_le_log hq₁pos (by exact_mod_cast hq)
  have hu₁5 : Real.log (q₁ : ℝ) / Real.log (m : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_right hlogq hlogm.le).trans hu₀5
  have husucc5 :
      Real.log (q₁ : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5 :=
    (roughSaiasNatQuotientLogRatio_succ_le hq₁ hm2).trans hu₁5
  have hnow :=
    roughSaiasBaseFreeFractionalKernel_intervalIntegrable hm2 hu₀5
  have hnext :=
    roughSaiasBaseFreeFractionalKernel_intervalIntegrable
      (m := m + 1) (q := q₁) (by omega) husucc5
  have huNow : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have huNext :
      (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ m + 1 by omega)) (by norm_num)
  have hupper :
      (m : ℝ) ^ (5 : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  have hnextCommon : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel q₁ (m + 1)) volume
      (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le huNow, uIcc_of_le huNext]
    exact Icc_subset_Icc le_rfl hupper
  have hnextTail : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel q₁ (m + 1)) volume
      ((m : ℝ) ^ (5 : ℝ))
      (((m + 1 : ℕ) : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le hupper, uIcc_of_le huNext]
    exact Icc_subset_Icc huNow le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hnextCommon hnextTail
  have hdiff := intervalIntegral.integral_sub hnextCommon hnow
  have htail := roughSaiasBaseFreeFractionalKernel_succ_tail_eq_zero
    hq₁ hm2 hu₁5
  unfold roughSaiasBaseFreeFractionalIntegral
  calc
    (∫ t in (1 : ℝ)..((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
        roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₀ m t =
      ((∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₀ m t := by
      rw [hsplit]
    _ = (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q₀ m t := by
      rw [htail, add_zero]
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t -
          roughSaiasBaseFreeFractionalKernel q₀ m t) := by
      rw [hdiff]
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
            roughSaiasScaledDickmanKernel q₀ m t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change
        roughSaiasBaseFreeFractionalKernel q₁ (m + 1) t -
            roughSaiasBaseFreeFractionalKernel q₀ m t =
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q₁ (m + 1) t -
              roughSaiasScaledDickmanKernel q₀ m t)
      rw [roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
          q₁ (m + 1) t,
        roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled q₀ m t]
      ring

/-- The preceding exact common-range identity specialized to the natural
hyperbola path. -/
theorem roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_common
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    (hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeFractionalIntegral (X / m) m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t) := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) :=
    Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  exact roughSaiasBaseFreeFractionalIntegral_quotient_succ_sub_eq_common
    hqNext hqLe hm2 hum5

/-- Integrability of the common sawtooth transition on one hyperbola edge. -/
theorem roughSaiasHyperbolaFractionalTransition_intervalIntegrable
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X)
    (hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t))
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) :=
    Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  have hqNextPosR : 0 < ((X / (m + 1) : ℕ) : ℝ) := by positivity
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogq : Real.log ((X / (m + 1) : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_le_log hqNextPosR (by exact_mod_cast hqLe)
  have huNextNow5 : Real.log ((X / (m + 1) : ℕ) : ℝ) /
      Real.log (m : ℝ) ≤ 5 :=
    (div_le_div_of_nonneg_right hlogq hlogm.le).trans hum5
  have huNext5 : Real.log ((X / (m + 1) : ℕ) : ℝ) /
      Real.log ((m + 1 : ℕ) : ℝ) ≤ 5 :=
    (roughSaiasNatQuotientLogRatio_succ_le hqNext hm2).trans huNextNow5
  have hnow := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X / m) hm2 hum5
  have hnext := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X / (m + 1)) (m := m + 1) (by omega) huNext5
  have huNow : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have huNext : (1 : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ m + 1 by omega)) (by norm_num)
  have hupper : (m : ℝ) ^ (5 : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  have hnextCommon : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel (X / (m + 1)) (m + 1))
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le huNow, uIcc_of_le huNext]
    exact Icc_subset_Icc le_rfl hupper
  apply (hnextCommon.sub hnow).congr
  intro t _ht
  change
    roughSaiasBaseFreeFractionalKernel (X / (m + 1)) (m + 1) t -
        roughSaiasBaseFreeFractionalKernel (X / m) m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t)
  rw [roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
      (X / (m + 1)) (m + 1) t,
    roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
      (X / m) m t]
  ring

/-- Exact telescoping of the absolute scaled-kernel variation along the
natural hyperbola path `m ↦ (X / m,m)` on an all-active block. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_eq
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) =
      roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t := by
  have hmono : ∀ m ∈ Finset.Ico a b,
      roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t ≤
        roughSaiasScaledDickmanKernel (X / m) m t := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmNow : m ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    have hmNext : m + 1 ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    exact roughSaiasScaledDickmanKernel_hyperbola_succ_le_of_active
      (by omega) (by omega) htpos
      (hactive (m + 1) hmNext) (hface m hmNow)
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) =
        ∑ m ∈ Finset.Ico a b,
          (roughSaiasScaledDickmanKernel (X / m) m t -
            roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono m hm))]
      ring
    _ = roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t := by
      clear hmono hactive hface hbX
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ b hab ih =>
          rw [Finset.sum_Ico_succ_top hab, ih]
          ring

/-- Quantitative all-active variation along the hyperbola path.  Quotient
jumps and base increments have the same sign, so their combined variation
still costs only one inverse logarithm. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_inv_log
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      1 / Real.log (a : ℝ) := by
  have haMem : a ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, hab⟩
  have hbMem : b ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    exact ⟨hab, le_rfl⟩
  have hb2 : 2 ≤ b := ha2.trans hab
  have huA1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate (X / a) a t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      ha2 htpos (hactive a haMem)
  have huB1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate (X / b) b t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hb2 htpos (hactive b hbMem)
  have hA_nonpos : roughSaiasScaledDickmanKernel (X / a) a t ≤ 0 :=
    roughSaiasScaledDickmanKernel_nonpos_of_active
      ha2 huA1 (hface a haMem)
  have hB_nonpos : roughSaiasScaledDickmanKernel (X / b) b t ≤ 0 :=
    roughSaiasScaledDickmanKernel_nonpos_of_active
      hb2 huB1 (hface b hbMem)
  have hBabs : |roughSaiasScaledDickmanKernel (X / b) b t| ≤
      1 / Real.log (b : ℝ) :=
    roughSaiasScaledDickmanKernel_abs_le_inv_log
      hb2 (hface b hbMem)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast hab)
  rw [roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_eq
      ha2 hab hbX htpos hactive hface]
  calc
    roughSaiasScaledDickmanKernel (X / a) a t -
        roughSaiasScaledDickmanKernel (X / b) b t ≤
      -roughSaiasScaledDickmanKernel (X / b) b t := by linarith
    _ = |roughSaiasScaledDickmanKernel (X / b) b t| :=
      (abs_of_nonpos hB_nonpos).symm
    _ ≤ 1 / Real.log (b : ℝ) := hBabs
    _ ≤ 1 / Real.log (a : ℝ) :=
      one_div_le_one_div_of_le hloga hlogab

/-- One-cutoff variation along the hyperbola path.  Once
`t > (X / m) / m`, every later kernel is zero; the unique reset costs a
second inverse logarithm. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff
    {X a c b : ℕ} (ha2 : 2 ≤ a) (hac : a ≤ c) (hcb : c ≤ b)
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
      2 / Real.log (a : ℝ) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hactiveBound :
      (∑ m ∈ Finset.Ico a c,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) ≤
        1 / Real.log (a : ℝ) :=
    roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_inv_log
      ha2 hac (hcb.trans hbX) htpos hactive hface
  rcases hcb.eq_or_lt with rfl | hcbLt
  · exact hactiveBound.trans (by
      have hinv : 0 ≤ 1 / Real.log (a : ℝ) := by positivity
      calc
        1 / Real.log (a : ℝ) ≤
            2 * (1 / Real.log (a : ℝ)) := by linarith
        _ = 2 / Real.log (a : ℝ) := by ring)
  · have hc2 : 2 ≤ c := ha2.trans hac
    have hcMem : c ∈ Finset.Icc a c := by
      rw [Finset.mem_Icc]
      exact ⟨hac, le_rfl⟩
    have hcNextMem : c + 1 ∈ Finset.Ioc c b := by
      rw [Finset.mem_Ioc]
      omega
    have hcNextLeX : c + 1 ≤ X := by omega
    have hcNextPos : 0 < c + 1 := by omega
    have hqNext : 1 ≤ X / (c + 1) :=
      Nat.div_pos hcNextLeX hcNextPos
    have hcNextZero :
        roughSaiasScaledDickmanKernel (X / (c + 1)) (c + 1) t = 0 :=
      roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
        hqNext (by omega) (hinactive (c + 1) hcNextMem)
    have htailZero :
        (∑ m ∈ Finset.Ico (c + 1) b,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hmMem : m ∈ Finset.Ioc c b := by
        rw [Finset.mem_Ioc]
        omega
      have hmNextMem : m + 1 ∈ Finset.Ioc c b := by
        rw [Finset.mem_Ioc]
        omega
      have hqm : 1 ≤ X / m :=
        Nat.div_pos (by omega) (by omega)
      have hqmNext : 1 ≤ X / (m + 1) :=
        Nat.div_pos (by omega) (by omega)
      have hmZero : roughSaiasScaledDickmanKernel (X / m) m t = 0 :=
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqm (by omega) (hinactive m hmMem)
      have hmNextZero :
          roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t = 0 :=
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqmNext (by omega) (hinactive (m + 1) hmNextMem)
      rw [hmZero, hmNextZero, sub_self, abs_zero]
    have htail :
        (∑ m ∈ Finset.Ico c b,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) =
          |roughSaiasScaledDickmanKernel (X / c) c t| := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hcbLt, hcNextZero,
        zero_sub, abs_neg, htailZero, add_zero]
    have hcAbs : |roughSaiasScaledDickmanKernel (X / c) c t| ≤
        1 / Real.log (c : ℝ) :=
      roughSaiasScaledDickmanKernel_abs_le_inv_log
        hc2 (hface c hcMem)
    have hlogac : Real.log (a : ℝ) ≤ Real.log (c : ℝ) :=
      Real.log_le_log
        (by exact_mod_cast (show 0 < a by omega))
        (by exact_mod_cast hac)
    have hcAbs' : |roughSaiasScaledDickmanKernel (X / c) c t| ≤
        1 / Real.log (a : ℝ) :=
      hcAbs.trans (one_div_le_one_div_of_le hloga hlogac)
    rw [← Finset.sum_Ico_consecutive _ hac hcb, htail]
    calc
      (∑ m ∈ Finset.Ico a c,
          |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t|) +
          |roughSaiasScaledDickmanKernel (X / c) c t| ≤
        1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
          add_le_add hactiveBound hcAbs'
      _ = 2 / Real.log (a : ℝ) := by ring

/-- The natural support scale `(X / m) / m` is antitone in `m`. -/
theorem roughSaiasNaturalHyperbolaSupport_antitone
    {X m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    ((X / n : ℕ) : ℝ) / (n : ℝ) ≤
      ((X / m : ℕ) : ℝ) / (m : ℝ) := by
  have hn : 0 < n := hm.trans_le hmn
  have hq : X / n ≤ X / m :=
    Nat.div_le_div_left (a := X) hmn hm
  calc
    ((X / n : ℕ) : ℝ) / (n : ℝ) ≤
        ((X / m : ℕ) : ℝ) / (n : ℝ) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hq)
        (by exact_mod_cast hn.le)
    _ ≤ ((X / m : ℕ) : ℝ) / (m : ℝ) :=
      div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast hm) (by exact_mod_cast hmn)

/-- The global five-face hypothesis at the first base propagates to every
natural hyperbola quotient and every sawtooth variable `t ≥ 1`. -/
theorem roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5 := by
  have hm2 : 2 ≤ m := ha2.trans ham
  have hmposNat : 0 < m := by omega
  have hqpos : 0 < X / m := Nat.div_pos hmX hmposNat
  have hqX : X / m ≤ X := Nat.div_le_self X m
  have hapos : 0 < (a : ℝ) := by positivity
  have hqposR : 0 < ((X / m : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hXposR : 0 < (X : ℝ) := by exact_mod_cast (hmposNat.trans_le hmX)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogqX : Real.log ((X / m : ℕ) : ℝ) ≤ Real.log (X : ℝ) :=
    Real.log_le_log hqposR (by exact_mod_cast hqX)
  have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hapos (by exact_mod_cast ham)
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  calc
    (Real.log ((X / m : ℕ) : ℝ) - Real.log t) /
          Real.log (m : ℝ) ≤
        Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right (by linarith) hlogm.le
    _ ≤ Real.log (X : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_right hlogqX hlogm.le
    _ ≤ Real.log (X : ℝ) / Real.log (a : ℝ) :=
      div_le_div_of_nonneg_left hlogX0 hloga hlogam
    _ ≤ 5 := hu5

/-- The five-face hypothesis at `a` gives its equivalent real power cap. -/
theorem roughSaiasNat_le_rpow_five
    {X a : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have haR : 0 < (a : ℝ) := by positivity
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hpow : 0 < (a : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos haR 5
  apply (Real.log_le_log_iff hXR hpow).mp
  rw [Real.log_rpow haR]
  exact (div_le_iff₀ hloga).mp hu5

/-- Log-ratio form of five-face propagation along natural hyperbola
quotients. -/
theorem roughSaiasNatHyperbolaLogRatio_le_five
    {X a m : ℕ} (ha2 : 2 ≤ a) (ham : a ≤ m) (hmX : m ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 := by
  simpa [roughSaiasBaseFreeDickmanCoordinate] using
    (roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
      ha2 ham hmX (t := (1 : ℝ)) (by norm_num) hu5)

/-- Every hyperbola transition may be placed on the single smallest cap
`a^5`.  The part between `a^5` and the edge's native cap `m^5` is beyond
both natural supports and hence vanishes identically. -/
theorem roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_firstCap
    {X a b m : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeFractionalIntegral (X / m) m =
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
            roughSaiasScaledDickmanKernel (X / m) m t) := by
  have hmData := Finset.mem_Ico.mp hm
  have hm2 : 2 ≤ m := ha2.trans hmData.1
  have hnextX : m + 1 ≤ X := by omega
  have hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 :=
    roughSaiasNatHyperbolaLogRatio_le_five
      ha2 hmData.1 (by omega) hu5
  have hedge :=
    roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_common
      hm2 hnextX hum5
  let f : ℝ → ℝ := fun t => (Int.fract t / t ^ (2 : ℕ)) *
    (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
      roughSaiasScaledDickmanKernel (X / m) m t)
  have hf : IntervalIntegrable f volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    simpa only [f] using roughSaiasHyperbolaFractionalTransition_intervalIntegrable
      hm2 hnextX hum5
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have haCapM : (a : ℝ) ^ (5 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmData.1) (by norm_num)
  have htailInt : IntervalIntegrable f volume
      ((a : ℝ) ^ (5 : ℝ)) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hf.mono_set
    rw [uIcc_of_le haCapM, uIcc_of_le
      (haCapOne.trans haCapM)]
    exact Icc_subset_Icc haCapOne le_rfl
  have hXpos : 0 < X := by omega
  have hXcap : (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    roughSaiasNat_le_rpow_five hXpos ha2 hu5
  have hXrealPos : 0 < (X : ℝ) := by exact_mod_cast hXpos
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hqNowLeX : ((X / m : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast Nat.div_le_self X m
  have hsupportNow : ((X / m : ℕ) : ℝ) / (m : ℝ) <
      (a : ℝ) ^ (5 : ℝ) := by
    calc
      ((X / m : ℕ) : ℝ) / (m : ℝ) ≤
          (X : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_right hqNowLeX (by positivity)
      _ < (X : ℝ) := div_lt_self hXrealPos hmone
      _ ≤ (a : ℝ) ^ (5 : ℝ) := hXcap
  have hsupportNext :
      ((X / (m + 1) : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) <
        (a : ℝ) ^ (5 : ℝ) :=
    (roughSaiasNaturalHyperbolaSupport_antitone
      (by omega) (Nat.le_succ m)).trans_lt hsupportNow
  have hqNow : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
  have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX (by omega)
  have htailZero :
      (∫ t in (a : ℝ) ^ (5 : ℝ)..(m : ℝ) ^ (5 : ℝ), f t) = 0 := by
    calc
      (∫ t in (a : ℝ) ^ (5 : ℝ)..(m : ℝ) ^ (5 : ℝ), f t) =
          ∫ _t in (a : ℝ) ^ (5 : ℝ)..(m : ℝ) ^ (5 : ℝ),
            (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc ((a : ℝ) ^ (5 : ℝ))
            ((m : ℝ) ^ (5 : ℝ)) := by
          simpa only [Set.uIcc_of_le haCapM] using ht
        have hnowZero : roughSaiasScaledDickmanKernel (X / m) m t = 0 :=
          roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
            hqNow hm2 (hsupportNow.trans_le htI.1)
        have hnextZero :
            roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t = 0 :=
          roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
            hqNext (by omega) (hsupportNext.trans_le htI.1)
        simp [f, hnowZero, hnextZero]
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.mono_set (by
      rw [uIcc_of_le haCapOne, uIcc_of_le (haCapOne.trans haCapM)]
      exact Icc_subset_Icc le_rfl haCapM)) htailInt
  rw [hedge]
  change (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ), f t) =
    ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), f t
  rw [← hsplit, htailZero, add_zero]

/-- Unconditional pointwise hyperbola-path variation on the full compact
range.  The active indices automatically form an initial segment because
the support scale is antitone; no cutoff index is required as input. -/
theorem roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log
    {X a b : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t|) ≤
      2 / Real.log (a : ℝ) := by
  classical
  let active : Finset ℕ := (Finset.Icc a b).filter
    (fun m => t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ))
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  by_cases hactiveNonempty : active.Nonempty
  · let c : ℕ := active.max' hactiveNonempty
    have hcActive : c ∈ active := Finset.max'_mem active hactiveNonempty
    have hcData : c ∈ Finset.Icc a b ∧
        t ≤ ((X / c : ℕ) : ℝ) / (c : ℝ) := by
      simpa only [active, Finset.mem_filter] using hcActive
    have hac : a ≤ c := (Finset.mem_Icc.mp hcData.1).1
    have hcb : c ≤ b := (Finset.mem_Icc.mp hcData.1).2
    have hactive : ∀ m ∈ Finset.Icc a c,
        t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ) := by
      intro m hm
      have hmData := Finset.mem_Icc.mp hm
      exact hcData.2.trans
        (roughSaiasNaturalHyperbolaSupport_antitone
          (by omega) hmData.2)
    have hface : ∀ m ∈ Finset.Icc a c,
        roughSaiasBaseFreeDickmanCoordinate (X / m) m t ≤ 5 := by
      intro m hm
      have hmData := Finset.mem_Icc.mp hm
      exact roughSaiasBaseFreeDickmanCoordinate_natHyperbola_le_five
        ha2 hmData.1 (hmData.2.trans (hcb.trans hbX)) ht1 hu5
    have hinactive : ∀ m ∈ Finset.Ioc c b,
        ((X / m : ℕ) : ℝ) / (m : ℝ) < t := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      apply lt_of_not_ge
      intro hmActive
      have hmMem : m ∈ active := by
        simp only [active, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hac.trans hm.1.le, hm.2⟩, hmActive⟩
      have hmc : m ≤ c := Finset.le_max' active m hmMem
      omega
    exact
      roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log_of_cutoff
        ha2 hac hcb hbX htpos hactive hface hinactive
  · have hzero : ∀ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
          roughSaiasScaledDickmanKernel (X / m) m t| = 0 := by
      intro m hm
      have hmData := Finset.mem_Ico.mp hm
      have hmNow : m ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc]
        omega
      have hmNext : m + 1 ∈ Finset.Icc a b := by
        rw [Finset.mem_Icc]
        omega
      have hmNotActive :
          ¬t ≤ ((X / m : ℕ) : ℝ) / (m : ℝ) := by
        intro hmActive
        apply hactiveNonempty
        exact ⟨m, by
          simp only [active, Finset.mem_filter]
          exact ⟨hmNow, hmActive⟩⟩
      have hmNextNotActive :
          ¬t ≤ ((X / (m + 1) : ℕ) : ℝ) /
            ((m + 1 : ℕ) : ℝ) := by
        intro hmActive
        apply hactiveNonempty
        exact ⟨m + 1, by
          simp only [active, Finset.mem_filter]
          exact ⟨hmNext, hmActive⟩⟩
      have hqm : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
      have hqmNext : 1 ≤ X / (m + 1) :=
        Nat.div_pos (by omega) (by omega)
      rw [roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqm (by omega) (lt_of_not_ge hmNotActive),
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hqmNext (by omega) (lt_of_not_ge hmNextNotActive),
        sub_self, abs_zero]
    rw [Finset.sum_eq_zero hzero]
    positivity

/-- The Dickman coordinate at `t = 1` is antitone along the natural
hyperbola path. -/
theorem roughSaiasNatHyperbolaLogRatio_succ_le
    {X m : ℕ} (hm2 : 2 ≤ m) (hnextX : m + 1 ≤ X) :
    Real.log ((X / (m + 1) : ℕ) : ℝ) /
        Real.log ((m + 1 : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) := by
  have hmPos : 0 < m := by omega
  have hnextPos : 0 < m + 1 := by omega
  have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX hnextPos
  have hqLe : X / (m + 1) ≤ X / m :=
    Nat.div_le_div_left (a := X) (Nat.le_succ m) hmPos
  have hqNextPosR : 0 < ((X / (m + 1) : ℕ) : ℝ) := by positivity
  have hqNowOne : 1 ≤ X / m := hqNext.trans hqLe
  have hlogqNow0 : 0 ≤ Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hqNowOne)
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmLe : Real.log (m : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
  have hlogqLe : Real.log ((X / (m + 1) : ℕ) : ℝ) ≤
      Real.log ((X / m : ℕ) : ℝ) :=
    Real.log_le_log hqNextPosR (by exact_mod_cast hqLe)
  calc
    Real.log ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) ≤
        Real.log ((X / m : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hlogqLe (by positivity)
    _ ≤ Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) :=
      div_le_div_of_nonneg_left hlogqNow0 hlogm hlogmLe

/-- The rho component has total hyperbola-path variation at most one. -/
theorem sum_abs_rho_natHyperbolaLogRatio_succ_sub_le_one
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
              Real.log ((m + 1 : ℕ) : ℝ)) -
          rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) ≤
      1 := by
  have hmono : ∀ m ∈ Finset.Ico a b,
      rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ)) ≤
        rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := ha2.trans hmData.1
    have hnextX : m + 1 ≤ X := by omega
    have hqNow : 1 ≤ X / m := Nat.div_pos (by omega) (by omega)
    have hqNext : 1 ≤ X / (m + 1) := Nat.div_pos hnextX (by omega)
    have huNow0 : 0 ≤ Real.log ((X / m : ℕ) : ℝ) /
        Real.log (m : ℝ) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hqNow)) (by positivity)
    have huNext0 : 0 ≤ Real.log ((X / (m + 1) : ℕ) : ℝ) /
        Real.log ((m + 1 : ℕ) : ℝ) :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast hqNext)) (by positivity)
    have huNow5 := roughSaiasNatHyperbolaLogRatio_le_five
      ha2 hmData.1 (by omega) hu5
    have huNext5 := roughSaiasNatHyperbolaLogRatio_le_five (m := m + 1)
      ha2 (by omega) (by omega) hu5
    exact roughRho_antitoneOn_zero_five
      ⟨huNext0, huNext5⟩ ⟨huNow0, huNow5⟩
      (roughSaiasNatHyperbolaLogRatio_succ_le hm2 hnextX)
  have htelescope :
      (∑ m ∈ Finset.Ico a b,
          |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) =
        rho (Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ)) -
          rho (Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ)) := by
    calc
      (∑ m ∈ Finset.Ico a b,
          |rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))|) =
        ∑ m ∈ Finset.Ico a b,
          (rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                Real.log ((m + 1 : ℕ) : ℝ)) -
            rho (Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ))) := by
          apply Finset.sum_congr rfl
          intro m hm
          rw [abs_of_nonneg (sub_nonneg.mpr (hmono m hm))]
      _ = rho (Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ)) -
          rho (Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ)) := by
        clear hmono hbX
        induction b, hab using Nat.le_induction with
        | base => simp
        | succ b hab ih =>
            rw [Finset.sum_Ico_succ_top hab, ih]
            ring
  have haX : a ≤ X := hab.trans hbX
  have hqA : 1 ≤ X / a := Nat.div_pos haX (by omega)
  have hqB : 1 ≤ X / b := Nat.div_pos hbX (by omega)
  have huA0 : 0 ≤ Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hqA)) (by positivity)
  have huB0 : 0 ≤ Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hqB)) (by positivity)
  have huA5 := roughSaiasNatHyperbolaLogRatio_le_five
    ha2 le_rfl haX hu5
  have huB5 := roughSaiasNatHyperbolaLogRatio_le_five
    ha2 hab hbX hu5
  have hrhoA0 : 0 ≤
      rho (Real.log ((X / a : ℕ) : ℝ) / Real.log (a : ℝ)) :=
    (rho_pos_on_zero_five huA0 huA5).le
  have hrhoB1 :
      rho (Real.log ((X / b : ℕ) : ℝ) / Real.log (b : ℝ)) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five huB5
  rw [htelescope]
  linarith

/-- Total variation of the transformed fractional correction along a
natural hyperbola block.  All edge integrals are first moved to the same
smallest cap `a^5`; finite summation then passes under the integral, where
the pointwise `2 / log a` kernel-variation estimate applies. -/
theorem roughSaiasBaseFreeFractionalIntegral_hyperbola_sum_abs_succ_sub_le_two_inv_log
    {X a b : ℕ} (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m|) ≤
      2 / Real.log (a : ℝ) := by
  let f : ℕ → ℝ → ℝ := fun m t =>
    (Int.fract t / t ^ (2 : ℕ)) *
      (roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
        roughSaiasScaledDickmanKernel (X / m) m t)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hfactorNonneg : 0 ≤ 2 / Real.log (a : ℝ) := by positivity
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have hf : ∀ m ∈ Finset.Ico a b,
      IntervalIntegrable (f m) volume
        (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := ha2.trans hmData.1
    have hnextX : m + 1 ≤ X := by omega
    have hum5 : Real.log ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ 5 :=
      roughSaiasNatHyperbolaLogRatio_le_five
        ha2 hmData.1 (by omega) hu5
    have hfull : IntervalIntegrable (f m) volume
        (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
      simpa only [f] using
        (roughSaiasHyperbolaFractionalTransition_intervalIntegrable
          hm2 hnextX hum5)
    have haCapM : (a : ℝ) ^ (5 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmData.1) (by norm_num)
    apply hfull.mono_set
    rw [uIcc_of_le haCapOne, uIcc_of_le (haCapOne.trans haCapM)]
    exact Icc_subset_Icc le_rfl haCapM
  have hedge : ∀ m ∈ Finset.Ico a b,
      roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m =
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), f m t := by
    intro m hm
    simpa only [f] using
      (roughSaiasBaseFreeFractionalIntegral_hyperbola_succ_sub_eq_firstCap
        ha2 hab hbX hm hu5)
  have hedgeBound : ∀ m ∈ Finset.Ico a b,
      |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m| ≤
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), |f m t| := by
    intro m hm
    rw [hedge m hm]
    exact intervalIntegral.abs_integral_le_integral_abs haCapOne
  have hsumInt : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ Finset.Ico a b, |f m t|) volume
      (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply (IntervalIntegrable.sum (Finset.Ico a b)
      (fun m hm => (hf m hm).abs)).congr
    intro t _ht
    simp only [Finset.sum_apply]
  have hzeroNotMem : (0 : ℝ) ∉
      Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    Set.notMem_uIcc_of_lt (by norm_num) (by positivity)
  have hinvSqInt : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := (a : ℝ) ^ (5 : ℝ))
        (n := (-2 : ℤ)) (Or.inr hzeroNotMem))
  have hmajorInt : IntervalIntegrable
      (fun t : ℝ => (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    hinvSqInt.const_mul _
  have hpoint : ∀ t ∈ Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)),
      (∑ m ∈ Finset.Ico a b, |f m t|) ≤
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by
    intro t ht
    rw [Set.uIcc_of_le haCapOne] at ht
    have htpos : 0 < t := zero_lt_one.trans_le ht.1
    have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
    have hwNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
      div_nonneg (Int.fract_nonneg t) htSqPos.le
    have hwLe : Int.fract t / t ^ (2 : ℕ) ≤ 1 / t ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right (Int.fract_lt_one t).le htSqPos.le
    have hvariation :=
      roughSaiasScaledDickmanKernel_hyperbola_sum_abs_succ_sub_le_two_inv_log
        ha2 hab hbX ht.1 hu5
    calc
      (∑ m ∈ Finset.Ico a b, |f m t|) =
          (Int.fract t / t ^ (2 : ℕ)) *
            ∑ m ∈ Finset.Ico a b,
              |roughSaiasScaledDickmanKernel (X / (m + 1)) (m + 1) t -
                roughSaiasScaledDickmanKernel (X / m) m t| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _hm
        simp only [f, abs_mul, abs_of_nonneg hwNonneg]
      _ ≤ (Int.fract t / t ^ (2 : ℕ)) *
          (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hvariation hwNonneg
      _ ≤ (1 / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_right hwLe hfactorNonneg
      _ = (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by ring
  have hsumIntegral :
      (∑ m ∈ Finset.Ico a b,
          ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), |f m t|) =
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          ∑ m ∈ Finset.Ico a b, |f m t| := by
    symm
    exact intervalIntegral.integral_finset_sum
      (fun m hm => (hf m hm).abs)
  have hmono :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          ∑ m ∈ Finset.Ico a b, |f m t|) ≤
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by
    exact intervalIntegral.integral_mono_on
      haCapOne hsumInt hmajorInt (fun t ht => hpoint t (by
        simpa only [Set.uIcc_of_le haCapOne] using ht))
  have hinvSqIntegral :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        1 / t ^ (2 : ℕ)) =
      1 - 1 / ((a : ℝ) ^ (5 : ℝ)) := by
    exact roughSaias_integral_one_div_sq_eq haCapOne
  have hmajorBound :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ))) ≤
        2 / Real.log (a : ℝ) := by
    rw [intervalIntegral.integral_const_mul, hinvSqIntegral]
    have hcapInvNonneg : 0 ≤ 1 / ((a : ℝ) ^ (5 : ℝ)) := by positivity
    calc
      (2 / Real.log (a : ℝ)) *
          (1 - 1 / ((a : ℝ) ^ (5 : ℝ))) ≤
        (2 / Real.log (a : ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hfactorNonneg
      _ = 2 / Real.log (a : ℝ) := by ring
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
          roughSaiasBaseFreeFractionalIntegral (X / m) m|) ≤
      ∑ m ∈ Finset.Ico a b,
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), |f m t| :=
      Finset.sum_le_sum hedgeBound
    _ = ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        ∑ m ∈ Finset.Ico a b, |f m t| := hsumIntegral
    _ ≤ ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := hmono
    _ ≤ 2 / Real.log (a : ℝ) := hmajorBound

/-! ## The genuinely real hyperbola path inside natural cells -/

/-- The Dickman coordinate occurring when both the quotient `X / s` and
the smoothness base `s` move continuously along the real hyperbola. -/
noncomputable def roughSaiasFullyRealHyperbolaCoordinate
    (X : ℕ) (s t : ℝ) : ℝ :=
  (Real.log ((X : ℝ) / s) - Real.log t) / Real.log s

/-- The Dickman derivative divided by the moving base logarithm on the
genuinely real hyperbola path.  The fully real base-free kernel is this
quantity times the common nonnegative sawtooth factor
`fract(t) / t^2`. -/
noncomputable def roughSaiasFullyRealHyperbolaScaledDickmanKernel
    (X : ℕ) (s t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      (roughSaiasFullyRealHyperbolaCoordinate X s t) /
    Real.log s

/-- A deterministic envelope for the oscillation from a point in the
natural cell `[m,m+1]` to its right endpoint.  On a fully active cell it is
the exact endpoint drop.  On the unique cell that can cross the support
boundary it is the uniform inverse-log envelope, and after the boundary it
vanishes. -/
noncomputable def roughSaiasFullyRealHyperbolaCellKernelOscillation
    (X m : ℕ) (t : ℝ) : ℝ :=
  if t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) then
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t -
      roughSaiasFullyRealHyperbolaScaledDickmanKernel
        X ((m + 1 : ℕ) : ℝ) t
  else if t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) then
    1 / Real.log (m : ℝ)
  else 0

/-- Algebraic factorization of the fully real base-free kernel along the
real hyperbola. -/
private theorem roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq
    (X : ℕ) (s t : ℝ) :
    roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s t =
      (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t := by
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
    roughSaiasFullyRealHyperbolaScaledDickmanKernel
    roughSaiasFullyRealHyperbolaCoordinate
  ring

/-- Logarithmic normal form of the real-hyperbola coordinate. -/
private theorem roughSaiasFullyRealHyperbolaCoordinate_eq
    {X : ℕ} {s t : ℝ} (hX : 0 < X) (hs : 1 < s) :
    roughSaiasFullyRealHyperbolaCoordinate X s t =
      (Real.log (X : ℝ) - Real.log t) / Real.log s - 1 := by
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  have hlogs : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  unfold roughSaiasFullyRealHyperbolaCoordinate
  rw [Real.log_div hXR.ne' hspos.ne']
  field_simp [hlogs]
  ring

/-- Every real-hyperbola coordinate in the compact block remains on the
five constructed faces. -/
theorem roughSaiasFullyRealHyperbolaCoordinate_le_five
    {X a : ℕ} {s t : ℝ} (hX : 0 < X) (ha2 : 2 ≤ a)
    (has : (a : ℝ) ≤ s) (_hsX : s ≤ (X : ℝ)) (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5 := by
  have hapos : (0 : ℝ) < (a : ℝ) := by positivity
  have hsone : 1 < s :=
    (by exact_mod_cast (show 1 < a by omega) : (1 : ℝ) < (a : ℝ)).trans_le has
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogs : 0 < Real.log s :=
    Real.log_pos ((by exact_mod_cast (show 1 < a by omega) :
      (1 : ℝ) < (a : ℝ)).trans_le has)
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ X by omega))
  have hlogt0 : 0 ≤ Real.log t := Real.log_nonneg ht1
  have hlogas : Real.log (a : ℝ) ≤ Real.log s :=
    Real.log_le_log hapos has
  have hratio : Real.log (X : ℝ) / Real.log s ≤
      Real.log (X : ℝ) / Real.log (a : ℝ) :=
    div_le_div_of_nonneg_left hlogX0 hloga hlogas
  rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hsone]
  calc
    (Real.log (X : ℝ) - Real.log t) / Real.log s - 1 ≤
        Real.log (X : ℝ) / Real.log s := by
      have hsub :
          (Real.log (X : ℝ) - Real.log t) / Real.log s ≤
            Real.log (X : ℝ) / Real.log s :=
        div_le_div_of_nonneg_right
          (sub_le_self (Real.log (X : ℝ)) hlogt0) hlogs.le
      linarith
    _ ≤ Real.log (X : ℝ) / Real.log (a : ℝ) := hratio
    _ ≤ 5 := hu5

/-- Uniform inverse-log envelope for the continuously moving scaled
Dickman kernel on the five constructed faces. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
    {X : ℕ} {s t : ℝ} (hs : 1 < s)
    (hu5 : roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5) :
    |roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t| ≤
      1 / Real.log s := by
  have hlogs : 0 < Real.log s := Real.log_pos hs
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [abs_div, abs_of_pos hlogs]
  exact div_le_div_of_nonneg_right
    (roughSaiasDickmanDerivative_abs_le_one hu5) hlogs.le

/-- The moving scaled kernel is nonpositive while it lies on an active
constructed face. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_nonpos_of_active
    {X : ℕ} {s t : ℝ} (hs : 1 < s)
    (hu1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t)
    (hu5 : roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t ≤ 0 := by
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hrho :
      0 ≤ rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1]
  exact div_nonpos_of_nonpos_of_nonneg
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrho)
      (by linarith)) hlogs.le

/-- Active-face cancellation for the real-hyperbola scaled kernel. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_neg_rho_div
    {X : ℕ} {s t : ℝ} (hX : 0 < X) (hs : 1 < s)
    (hu1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t =
      -rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) /
        (Real.log (X : ℝ) - Real.log t - Real.log s) := by
  have hlogs : Real.log s ≠ 0 := (Real.log_pos hs).ne'
  have hcoordinate :
      roughSaiasFullyRealHyperbolaCoordinate X s t * Real.log s =
        Real.log (X : ℝ) - Real.log t - Real.log s := by
    rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hs]
    field_simp [hlogs]
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_one_le hu1, div_div, hcoordinate]

/-- The support inequality `t ≤ X/s²` is exactly the active-face condition
for the real-hyperbola coordinate. -/
private theorem one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
    {X : ℕ} {s t : ℝ} (_hX : 0 < X) (hs : 1 < s) (htpos : 0 < t)
    (htactive : t ≤ (X : ℝ) / s ^ (2 : ℕ)) :
    1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t := by
  have hspos : 0 < s := zero_lt_one.trans hs
  unfold roughSaiasFullyRealHyperbolaCoordinate
  rw [one_le_div (Real.log_pos hs)]
  have hts : t * s ≤ (X : ℝ) / s := by
    rw [le_div_iff₀ hspos, mul_assoc]
    simpa only [pow_two] using
      ((le_div_iff₀ (sq_pos_of_pos hspos)).mp htactive)
  have hlog := Real.log_le_log (mul_pos htpos hspos) hts
  rw [Real.log_mul htpos.ne' hspos.ne'] at hlog
  linarith

/-- The scaled kernel vanishes after the continuously moving support
`X / s^2`. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
    {X : ℕ} {s t : ℝ} (hX : 0 < X) (hs : 1 < s)
    (ht : (X : ℝ) / s ^ (2 : ℕ) < t) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t = 0 := by
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hspos : 0 < s := zero_lt_one.trans hs
  have hsupportPos : 0 < (X : ℝ) / s ^ (2 : ℕ) := by positivity
  have htpos : 0 < t := hsupportPos.trans ht
  have hquotLt : (X : ℝ) / s < t * s := by
    rw [div_lt_iff₀ hspos]
    have := (div_lt_iff₀ (sq_pos_of_pos hspos)).mp ht
    nlinarith
  have hlogLt : Real.log ((X : ℝ) / s) <
      Real.log t + Real.log s := by
    have hquotPos : 0 < (X : ℝ) / s := div_pos hXR hspos
    have h := Real.strictMonoOn_log hquotPos (mul_pos htpos hspos) hquotLt
    rwa [Real.log_mul htpos.ne' hspos.ne'] at h
  have hcoord : roughSaiasFullyRealHyperbolaCoordinate X s t < 1 := by
    unfold roughSaiasFullyRealHyperbolaCoordinate
    rw [div_lt_one (Real.log_pos hs)]
    linarith
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
  rw [roughSaiasDickmanDerivative_of_lt_one hcoord]
  simp

/-- Along an active part of the genuinely real hyperbola the scaled kernel
is antitone in the moving base.  The quotient decrease and the base increase
reinforce one another. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_le_of_le_of_active
    {X : ℕ} {s r t : ℝ} (hX : 0 < X) (hs : 1 < s)
    (hsr : s ≤ r) (htpos : 0 < t)
    (htactive : t ≤ (X : ℝ) / r ^ (2 : ℕ))
    (hus5 : roughSaiasFullyRealHyperbolaCoordinate X s t ≤ 5) :
    roughSaiasFullyRealHyperbolaScaledDickmanKernel X r t ≤
      roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t := by
  have hspos : 0 < s := zero_lt_one.trans hs
  have hrone : 1 < r := hs.trans_le hsr
  have hrpos : 0 < r := zero_lt_one.trans hrone
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hlogr : 0 < Real.log r := Real.log_pos hrone
  have hlogsr : Real.log s ≤ Real.log r :=
    Real.log_le_log hspos hsr
  have htrSq : t * r ^ (2 : ℕ) ≤ (X : ℝ) :=
    (le_div_iff₀ (sq_pos_of_pos hrpos)).mp htactive
  have htX : t ≤ (X : ℝ) := by
    have hrSqOne : (1 : ℝ) ≤ r ^ (2 : ℕ) := by nlinarith
    nlinarith
  have hA0 : 0 ≤ Real.log (X : ℝ) - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log htpos htX)
  have hcoord : roughSaiasFullyRealHyperbolaCoordinate X r t ≤
      roughSaiasFullyRealHyperbolaCoordinate X s t := by
    rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hrone,
      roughSaiasFullyRealHyperbolaCoordinate_eq hX hs]
    exact sub_le_sub_right
      (div_le_div_of_nonneg_left hA0 hlogs hlogsr) 1
  have huR1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X r t :=
    one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
      hX hrone htpos htactive
  have huS1 : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X s t :=
    huR1.trans hcoord
  have huR5 : roughSaiasFullyRealHyperbolaCoordinate X r t ≤ 5 :=
    hcoord.trans hus5
  have hrho :
      rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) ≤
        rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) :=
    roughRho_antitoneOn_zero_five
      (show roughSaiasFullyRealHyperbolaCoordinate X r t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (show roughSaiasFullyRealHyperbolaCoordinate X s t - 1 ∈
          Icc (0 : ℝ) 5 by constructor <;> linarith)
      (by linarith)
  have hdenomS : 0 < Real.log (X : ℝ) - Real.log t - Real.log s := by
    have hidentity :
        roughSaiasFullyRealHyperbolaCoordinate X s t * Real.log s =
          Real.log (X : ℝ) - Real.log t - Real.log s := by
      rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hs]
      field_simp [hlogs.ne']
    rw [← hidentity]
    exact mul_pos (zero_lt_one.trans_le huS1) hlogs
  have hdenomR : 0 < Real.log (X : ℝ) - Real.log t - Real.log r := by
    have hidentity :
        roughSaiasFullyRealHyperbolaCoordinate X r t * Real.log r =
          Real.log (X : ℝ) - Real.log t - Real.log r := by
      rw [roughSaiasFullyRealHyperbolaCoordinate_eq hX hrone]
      field_simp [hlogr.ne']
    rw [← hidentity]
    exact mul_pos (zero_lt_one.trans_le huR1) hlogr
  have hdenomLe :
      Real.log (X : ℝ) - Real.log t - Real.log r ≤
        Real.log (X : ℝ) - Real.log t - Real.log s := by
    linarith
  have hrhoNonneg :
      0 ≤ rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) :=
    (rho_pos_on_zero_five (by linarith) (by linarith)).le
  rw [roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_neg_rho_div
      hX hrone huR1,
    roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_neg_rho_div
      hX hs huS1]
  rw [neg_div, neg_div]
  apply neg_le_neg
  calc
    rho (roughSaiasFullyRealHyperbolaCoordinate X s t - 1) /
          (Real.log (X : ℝ) - Real.log t - Real.log s) ≤
        rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) /
          (Real.log (X : ℝ) - Real.log t - Real.log s) :=
      div_le_div_of_nonneg_right hrho hdenomS.le
    _ ≤ rho (roughSaiasFullyRealHyperbolaCoordinate X r t - 1) /
          (Real.log (X : ℝ) - Real.log t - Real.log r) :=
      div_le_div_of_nonneg_left hrhoNonneg hdenomR hdenomLe

/-- The cell envelope indeed dominates every within-cell oscillation to
the right endpoint. -/
private theorem roughSaiasFullyRealHyperbolaScaledDickmanKernel_cell_abs_sub_le
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s t : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ))
    (ht1 : 1 ≤ t) :
    |roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t -
        roughSaiasFullyRealHyperbolaScaledDickmanKernel
          X ((m + 1 : ℕ) : ℝ) t| ≤
      roughSaiasFullyRealHyperbolaCellKernelOscillation X m t := by
  have hmData := Finset.mem_Ico.mp hm
  have hnextX : m + 1 ≤ X := by omega
  have hmone : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hsone : 1 < s := hmone.trans_le hs.1
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
  have hmXR : (m : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast (show m ≤ X by omega)
  have hnextXR : ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast hnextX
  have hfaceM := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := (m : ℝ)) hX ha2 hamR hmXR ht1 hu5
  have hfaceS := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := s) hX ha2 (hamR.trans hs.1) (hs.2.trans hnextXR) ht1 hu5
  by_cases hright :
      t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  · have hnextS :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_le_of_le_of_active
        hX hsone hs.2 htpos hright hfaceS
    have hSm :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_le_of_le_of_active
        hX hmone hs.1 htpos (hright.trans (by
          exact div_le_div_of_nonneg_left (by positivity)
            (sq_pos_of_pos (by positivity : (0 : ℝ) < s))
            (by nlinarith [hs.2]))) hfaceM
    rw [roughSaiasFullyRealHyperbolaCellKernelOscillation, if_pos hright,
      abs_of_nonneg (sub_nonneg.mpr hnextS)]
    linarith
  · have hrightLt := lt_of_not_ge hright
    have hnextZero :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
        hX hnextOne hrightLt
    by_cases hleft : t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ))
    · have hlogsM : 0 < Real.log (m : ℝ) := Real.log_pos hmone
      have hlogMS : Real.log (m : ℝ) ≤ Real.log s :=
        Real.log_le_log (zero_lt_one.trans hmone) hs.1
      have hinv : 1 / Real.log s ≤ 1 / Real.log (m : ℝ) :=
        one_div_le_one_div_of_le hlogsM hlogMS
      have hSabs :
          |roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t| ≤
            1 / Real.log (m : ℝ) := by
        by_cases hsactive : t ≤ (X : ℝ) / s ^ (2 : ℕ)
        · exact (roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
              hsone hfaceS).trans hinv
        · rw [roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
              hX hsone (lt_of_not_ge hsactive), abs_zero]
          positivity
      rw [hnextZero, sub_zero,
        roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_pos hleft]
      exact hSabs
    · have hleftLt := lt_of_not_ge hleft
      have hSsupport : (X : ℝ) / s ^ (2 : ℕ) < t := by
        exact (div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos (by positivity : (0 : ℝ) < (m : ℝ)))
          (by nlinarith [hs.1])).trans_lt hleftLt
      have hSzero :=
        roughSaiasFullyRealHyperbolaScaledDickmanKernel_eq_zero_of_support_lt
          hX hsone hSsupport
      rw [hSzero, hnextZero, sub_self, abs_zero,
        roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_neg hleft]

/-- The within-cell envelopes have total pointwise mass at most two inverse
logarithms.  Active endpoints form an initial segment; its monotone drops
telescope, and the single possible support-boundary cell costs the second
inverse logarithm. -/
private theorem sum_roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) ≤
      2 / Real.log (a : ℝ) := by
  classical
  let active : Finset ℕ := (Finset.Icc a b).filter
    (fun m => t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)))
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hsupportAntitone : ∀ {m n : ℕ}, a ≤ m → m ≤ n →
      (X : ℝ) / ((n : ℝ) ^ (2 : ℕ)) ≤
        (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) := by
    intro m n _ham hmn
    exact div_le_div_of_nonneg_left (by positivity)
      (sq_pos_of_pos (by exact_mod_cast (show 0 < m by omega)))
      (by exact_mod_cast (Nat.pow_le_pow_left hmn 2))
  by_cases hactiveNonempty : active.Nonempty
  · let c : ℕ := active.max' hactiveNonempty
    have hcActive : c ∈ active := Finset.max'_mem active hactiveNonempty
    have hcData : c ∈ Finset.Icc a b ∧
        t ≤ (X : ℝ) / ((c : ℝ) ^ (2 : ℕ)) := by
      simpa only [active, Finset.mem_filter] using hcActive
    have hac : a ≤ c := (Finset.mem_Icc.mp hcData.1).1
    have hcb : c ≤ b := (Finset.mem_Icc.mp hcData.1).2
    have hactiveLe : ∀ m, a ≤ m → m ≤ c →
        t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) := by
      intro m ham hmc
      exact hcData.2.trans (hsupportAntitone ham hmc)
    have hinactiveGt : ∀ m, c < m → m ≤ b →
        (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) < t := by
      intro m hcm hmb
      apply lt_of_not_ge
      intro hmActive
      have hmMem : m ∈ active := by
        simp only [active, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hac.trans hcm.le, hmb⟩, hmActive⟩
      have hmc : m ≤ c := Finset.le_max' active m hmMem
      omega
    have hfaceA := roughSaiasFullyRealHyperbolaCoordinate_le_five
      hX ha2 le_rfl (by exact_mod_cast (hac.trans (hcb.trans hbX))) ht1 hu5
    have htel :
        (∑ m ∈ Finset.Ico a c,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) =
          roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t := by
      calc
        (∑ m ∈ Finset.Ico a c,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) =
          ∑ m ∈ Finset.Ico a c,
            (roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t -
              roughSaiasFullyRealHyperbolaScaledDickmanKernel
                X ((m + 1 : ℕ) : ℝ) t) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hmData := Finset.mem_Ico.mp hm
            have hright := hactiveLe (m + 1) (by omega) (by omega)
            rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
              if_pos hright]
        _ = roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t := by
          simpa only [neg_sub_neg] using
            (Finset.sum_Ico_sub
              (fun m =>
                -roughSaiasFullyRealHyperbolaScaledDickmanKernel
                  X (m : ℝ) t) hac)
    have hcOne : (1 : ℝ) < (c : ℝ) := by exact_mod_cast (show 1 < c by omega)
    have hacR : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast hac
    have hcXR : (c : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (hcb.trans hbX)
    have hfaceC := roughSaiasFullyRealHyperbolaCoordinate_le_five
      (s := (c : ℝ)) hX ha2 hacR hcXR ht1 hu5
    have hcCoordOne : 1 ≤ roughSaiasFullyRealHyperbolaCoordinate X (c : ℝ) t :=
      one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
        hX hcOne htpos hcData.2
    have hcNonpos :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_nonpos_of_active
        hcOne hcCoordOne hfaceC
    have hcAbs :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
        hcOne hfaceC
    have hlogac : Real.log (a : ℝ) ≤ Real.log (c : ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hac)
    have hinvC : 1 / Real.log (c : ℝ) ≤ 1 / Real.log (a : ℝ) :=
      one_div_le_one_div_of_le hloga hlogac
    have htelBound :
        (∑ m ∈ Finset.Ico a c,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) ≤
          1 / Real.log (a : ℝ) := by
      rw [htel]
      calc
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t ≤
          -roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t := by
            have haOne : (1 : ℝ) < (a : ℝ) := by
              exact_mod_cast (show 1 < a by omega)
            have haCoordOne :
                1 ≤ roughSaiasFullyRealHyperbolaCoordinate X (a : ℝ) t :=
              one_le_roughSaiasFullyRealHyperbolaCoordinate_of_le_support
                hX haOne htpos (hactiveLe a le_rfl hac)
            have haNonpos :=
              roughSaiasFullyRealHyperbolaScaledDickmanKernel_nonpos_of_active
                haOne haCoordOne hfaceA
            linarith
        _ = |roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t| :=
          (abs_of_nonpos hcNonpos).symm
        _ ≤ 1 / Real.log (c : ℝ) := hcAbs
        _ ≤ 1 / Real.log (a : ℝ) := hinvC
    rcases hcb.eq_or_lt with hcbEq | hcbLt
    · have htelBound' :
          (∑ m ∈ Finset.Ico a b,
              roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) ≤
            1 / Real.log (a : ℝ) := by
        simpa only [hcbEq] using htelBound
      exact htelBound'.trans (by
        have hinvA : 0 ≤ 1 / Real.log (a : ℝ) := by positivity
        calc
          1 / Real.log (a : ℝ) ≤
              1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
            le_add_of_nonneg_right hinvA
          _ = 2 / Real.log (a : ℝ) := by ring)
    · have hcross :
          roughSaiasFullyRealHyperbolaCellKernelOscillation X c t =
            1 / Real.log (c : ℝ) := by
        have hright := hinactiveGt (c + 1) (by omega) (by omega)
        have hrightNot :
            ¬t ≤ (X : ℝ) / (((c + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
          not_le.mpr hright
        rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
          if_neg hrightNot, if_pos hcData.2]
      have htail :
          (∑ m ∈ Finset.Ico (c + 1) b,
              roughSaiasFullyRealHyperbolaCellKernelOscillation X m t) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        have hmData := Finset.mem_Ico.mp hm
        have hleft := hinactiveGt m (by omega) hmData.2.le
        have hright :
            (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) < t :=
          (hsupportAntitone (hac.trans (by omega)) (Nat.le_succ m)).trans_lt hleft
        have hrightNot :
            ¬t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) :=
          not_le.mpr hright
        have hleftNot : ¬t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) :=
          not_le.mpr hleft
        rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
          if_neg hrightNot, if_neg hleftNot]
      have htelExprBound :
          roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
              roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t ≤
            1 / Real.log (a : ℝ) := by
        rw [← htel]
        exact htelBound
      rw [← Finset.sum_Ico_consecutive _ hac hcbLt.le,
        ← Finset.sum_Ico_consecutive _ (Nat.le_succ c)
          (show c + 1 ≤ b by omega), htel, htail]
      simp only [Finset.sum_Ico_succ_top le_rfl, Finset.Ico_self,
        Finset.sum_empty, zero_add, add_zero]
      rw [hcross]
      calc
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X (a : ℝ) t -
              roughSaiasFullyRealHyperbolaScaledDickmanKernel X (c : ℝ) t +
            1 / Real.log (c : ℝ) ≤
          1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
            add_le_add htelExprBound hinvC
        _ = 2 / Real.log (a : ℝ) := by ring
  · have hzero : ∀ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellKernelOscillation X m t = 0 := by
      intro m hm
      have hmData := Finset.mem_Ico.mp hm
      have hmNot : ¬t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ)) := by
        intro hmActive
        apply hactiveNonempty
        exact ⟨m, by
          simp only [active, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hmData.1, hmData.2.le⟩, hmActive⟩⟩
      have hrightNot :
          ¬t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        intro hright
        exact hmNot (hright.trans (hsupportAntitone hmData.1 (Nat.le_succ m)))
      rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hrightNot, if_neg hmNot]
    rw [Finset.sum_eq_zero hzero]
    positivity

/-- The sawtooth-weighted version of the real-hyperbola cell envelope. -/
noncomputable def roughSaiasFullyRealHyperbolaCellFractionalOscillation
    (X m : ℕ) (t : ℝ) : ℝ :=
  (Int.fract t / t ^ (2 : ℕ)) *
    roughSaiasFullyRealHyperbolaCellKernelOscillation X m t

/-- The integrated sawtooth envelope on the common smallest cap. -/
noncomputable def roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
    (X a m : ℕ) : ℝ :=
  ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
    roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t

/-- Measurability of the moving scaled kernel in the sawtooth variable. -/
private theorem measurable_roughSaiasFullyRealHyperbolaScaledDickmanKernel
    (X : ℕ) (s : ℝ) :
    Measurable (roughSaiasFullyRealHyperbolaScaledDickmanKernel X s) := by
  unfold roughSaiasFullyRealHyperbolaScaledDickmanKernel
    roughSaiasFullyRealHyperbolaCoordinate
  exact (measurable_roughSaiasDickmanDerivative.comp
      ((measurable_const.sub measurable_id.log).div measurable_const)).div
    measurable_const

/-- Measurability of one deterministic cell envelope. -/
private theorem measurable_roughSaiasFullyRealHyperbolaCellKernelOscillation
    (X m : ℕ) :
    Measurable (roughSaiasFullyRealHyperbolaCellKernelOscillation X m) := by
  unfold roughSaiasFullyRealHyperbolaCellKernelOscillation
  apply Measurable.ite measurableSet_Iic
  · exact
      (measurable_roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ)).sub
        (measurable_roughSaiasFullyRealHyperbolaScaledDickmanKernel
          X ((m + 1 : ℕ) : ℝ))
  · exact Measurable.ite measurableSet_Iic measurable_const measurable_const

/-- Measurability of the weighted cell envelope. -/
private theorem measurable_roughSaiasFullyRealHyperbolaCellFractionalOscillation
    (X m : ℕ) :
    Measurable (roughSaiasFullyRealHyperbolaCellFractionalOscillation X m) := by
  unfold roughSaiasFullyRealHyperbolaCellFractionalOscillation
  exact (measurable_id.fract.div (measurable_id.pow_const _)).mul
    (measurable_roughSaiasFullyRealHyperbolaCellKernelOscillation X m)

/-- Each cell envelope is nonnegative. -/
private theorem roughSaiasFullyRealHyperbolaCellKernelOscillation_nonneg
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b) {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    0 ≤ roughSaiasFullyRealHyperbolaCellKernelOscillation X m t := by
  have hbound :=
    roughSaiasFullyRealHyperbolaScaledDickmanKernel_cell_abs_sub_le
      hX ha2 hab hbX hm hu5
        (s := (m : ℝ)) (t := t)
        ⟨le_rfl, by exact_mod_cast (Nat.le_succ m)⟩ ht1
  exact (abs_nonneg _).trans hbound

/-- A single cell envelope is bounded by two inverse logarithms of the
first base. -/
private theorem roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b) {t : ℝ} (ht1 : 1 ≤ t)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealHyperbolaCellKernelOscillation X m t ≤
      2 / Real.log (a : ℝ) := by
  have hmData := Finset.mem_Ico.mp hm
  have hnextX : m + 1 ≤ X := by omega
  have hmOne : (1 : ℝ) < (m : ℝ) := by exact_mod_cast (show 1 < m by omega)
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogam : Real.log (a : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hmData.1)
  have hlogmnext : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_succ m))
  have hinvM : 1 / Real.log (m : ℝ) ≤ 1 / Real.log (a : ℝ) :=
    one_div_le_one_div_of_le hloga hlogam
  have hinvNext : 1 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      1 / Real.log (a : ℝ) :=
    (one_div_le_one_div_of_le (Real.log_pos hmOne) hlogmnext).trans hinvM
  by_cases hright :
      t ≤ (X : ℝ) / (((m + 1 : ℕ) : ℝ) ^ (2 : ℕ))
  · have hamR : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmData.1
    have hmXR : (m : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast (show m ≤ X by omega)
    have haNextR : (a : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show a ≤ m + 1 by omega)
    have hnextXR : ((m + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
      exact_mod_cast hnextX
    have hfaceM := roughSaiasFullyRealHyperbolaCoordinate_le_five
      (s := (m : ℝ)) hX ha2 hamR hmXR ht1 hu5
    have hfaceNext := roughSaiasFullyRealHyperbolaCoordinate_le_five
      (s := ((m + 1 : ℕ) : ℝ)) hX ha2 haNextR hnextXR ht1 hu5
    have hMabs :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
        hmOne hfaceM
    have hNextAbs :=
      roughSaiasFullyRealHyperbolaScaledDickmanKernel_abs_le_inv_log
        hnextOne hfaceNext
    rw [roughSaiasFullyRealHyperbolaCellKernelOscillation, if_pos hright]
    calc
      roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t -
          roughSaiasFullyRealHyperbolaScaledDickmanKernel
            X ((m + 1 : ℕ) : ℝ) t ≤
        |roughSaiasFullyRealHyperbolaScaledDickmanKernel X (m : ℝ) t| +
          |roughSaiasFullyRealHyperbolaScaledDickmanKernel
            X ((m + 1 : ℕ) : ℝ) t| := by
              exact (le_abs_self _).trans (abs_sub _ _)
      _ ≤ 1 / Real.log (m : ℝ) +
          1 / Real.log ((m + 1 : ℕ) : ℝ) := add_le_add hMabs hNextAbs
      _ ≤ 1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
        add_le_add hinvM hinvNext
      _ = 2 / Real.log (a : ℝ) := by ring
  · by_cases hleft : t ≤ (X : ℝ) / ((m : ℝ) ^ (2 : ℕ))
    · rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_pos hleft]
      have hinvA : 0 ≤ 1 / Real.log (a : ℝ) :=
        (one_div_pos.mpr hloga).le
      exact hinvM.trans (by
        calc
          1 / Real.log (a : ℝ) ≤
              1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
            le_add_of_nonneg_right hinvA
          _ = 2 / Real.log (a : ℝ) := by ring)
    · rw [roughSaiasFullyRealHyperbolaCellKernelOscillation,
        if_neg hright, if_neg hleft]
      exact div_nonneg (by norm_num) hloga.le

/-- The weighted envelope is interval-integrable on the common cap. -/
private theorem roughSaiasFullyRealHyperbolaCellFractionalOscillation_intervalIntegrable
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealHyperbolaCellFractionalOscillation X m)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have hzeroNotMem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    Set.notMem_uIcc_of_lt (by norm_num) (by positivity)
  have hinvSq : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := (a : ℝ) ^ (5 : ℝ))
        (n := (-2 : ℤ)) (Or.inr hzeroNotMem))
  have hmajor := hinvSq.const_mul (2 / Real.log (a : ℝ))
  apply hmajor.mono_fun'
    (measurable_roughSaiasFullyRealHyperbolaCellFractionalOscillation
      X m).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
  have htI : t ∈ Set.Icc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    rw [← Set.uIcc_of_le haCapOne]
    exact Set.uIoc_subset_uIcc ht
  have htpos : 0 < t := zero_lt_one.trans_le htI.1
  have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
  have hfactorNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
    div_nonneg (Int.fract_nonneg t) htSqPos.le
  have hfactorLe : Int.fract t / t ^ (2 : ℕ) ≤ 1 / t ^ (2 : ℕ) :=
    div_le_div_of_nonneg_right (Int.fract_lt_one t).le htSqPos.le
  have hoscNonneg :=
    roughSaiasFullyRealHyperbolaCellKernelOscillation_nonneg
      hX ha2 hab hbX hm htI.1 hu5
  have hoscBound :=
    roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
      hX ha2 hab hbX hm htI.1 hu5
  unfold roughSaiasFullyRealHyperbolaCellFractionalOscillation
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hfactorNonneg hoscNonneg)]
  calc
    (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaCellKernelOscillation X m t ≤
      (Int.fract t / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hoscBound hfactorNonneg
    _ ≤ (1 / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactorLe (by positivity)
    _ = (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by ring

/-- The integrated real-hyperbola cell ledgers have total mass at most
`2/log a`. -/
theorem sum_roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger_le_two_inv_log
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) ≤
      2 / Real.log (a : ℝ) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have hint : ∀ m ∈ Finset.Ico a b,
      IntervalIntegrable
        (roughSaiasFullyRealHyperbolaCellFractionalOscillation X m)
        volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    intro m hm
    exact
      roughSaiasFullyRealHyperbolaCellFractionalOscillation_intervalIntegrable
        hX ha2 hab hbX hm hu5
  have hsumInt : IntervalIntegrable
      (fun t : ℝ => ∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply (IntervalIntegrable.sum (Finset.Ico a b) hint).congr
    intro t _ht
    simp only [Finset.sum_apply]
  have hzeroNotMem : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) :=
    Set.notMem_uIcc_of_lt (by norm_num) (by positivity)
  have hinvSq : IntervalIntegrable (fun t : ℝ => 1 / t ^ (2 : ℕ))
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    simpa [one_div, zpow_neg] using
      (intervalIntegral.intervalIntegrable_zpow
        (a := (1 : ℝ)) (b := (a : ℝ) ^ (5 : ℝ))
        (n := (-2 : ℤ)) (Or.inr hzeroNotMem))
  have hmajorInt := hinvSq.const_mul (2 / Real.log (a : ℝ))
  have hpoint : ∀ t ∈ Set.Icc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)),
      (∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t) ≤
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by
    intro t ht
    have htpos : 0 < t := zero_lt_one.trans_le ht.1
    have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
    have hfactorNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
      div_nonneg (Int.fract_nonneg t) htSqPos.le
    have hfactorLe : Int.fract t / t ^ (2 : ℕ) ≤ 1 / t ^ (2 : ℕ) :=
      div_le_div_of_nonneg_right (Int.fract_lt_one t).le htSqPos.le
    have hosc :=
      sum_roughSaiasFullyRealHyperbolaCellKernelOscillation_le_two_inv_log
        hX ha2 hab hbX ht.1 hu5
    calc
      (∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t) =
        (Int.fract t / t ^ (2 : ℕ)) *
          ∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealHyperbolaCellKernelOscillation X m t := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro m _hm
              rfl
      _ ≤ (Int.fract t / t ^ (2 : ℕ)) *
          (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_left hosc hfactorNonneg
      _ ≤ (1 / t ^ (2 : ℕ)) * (2 / Real.log (a : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactorLe (by positivity)
      _ = (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := by ring
  have hmono := intervalIntegral.integral_mono_on
    haCapOne hsumInt hmajorInt hpoint
  have hsumIntegral :
      (∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m) =
        ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
          ∑ m ∈ Finset.Ico a b,
            roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t := by
    unfold roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger
    symm
    exact intervalIntegral.integral_finset_sum hint
  have hinvSqIntegral :
      (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ), 1 / t ^ (2 : ℕ)) =
        1 - 1 / ((a : ℝ) ^ (5 : ℝ)) := by
    exact roughSaias_integral_one_div_sq_eq haCapOne
  rw [hsumIntegral]
  calc
    (∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        ∑ m ∈ Finset.Ico a b,
          roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t) ≤
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (2 / Real.log (a : ℝ)) * (1 / t ^ (2 : ℕ)) := hmono
    _ = (2 / Real.log (a : ℝ)) *
        (1 - 1 / ((a : ℝ) ^ (5 : ℝ))) := by
      rw [intervalIntegral.integral_const_mul, hinvSqIntegral]
    _ ≤ (2 / Real.log (a : ℝ)) * 1 := by
      apply mul_le_mul_of_nonneg_left _
        (div_nonneg (by norm_num) hloga.le)
      have hpowPos : 0 < (a : ℝ) ^ (5 : ℝ) := by positivity
      have hinvPow : 0 ≤ 1 / ((a : ℝ) ^ (5 : ℝ)) :=
        div_nonneg zero_le_one hpowPos.le
      linarith
    _ = 2 / Real.log (a : ℝ) := by ring

/-- On a compact real-hyperbola block, the fully real fractional integral
may be placed on the single smallest cap `a^5`. -/
private theorem roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_eq_firstCap
    {X a b : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (_hab : a ≤ b)
    (hbX : b ≤ X) {s : ℝ} (hs : s ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s =
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t := by
  have haOne : (1 : ℝ) < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hsOne : 1 < s := haOne.trans_le hs.1
  have hspos : 0 < s := zero_lt_one.trans hsOne
  have hXreal : 0 < (X : ℝ) := by exact_mod_cast hX
  have hbXR : (b : ℝ) ≤ (X : ℝ) := by exact_mod_cast hbX
  have hface := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := s) (t := (1 : ℝ)) hX ha2 hs.1 (hs.2.trans hbXR)
      (by norm_num) hu5
  have hratio : Real.log ((X : ℝ) / s) / Real.log s ≤ 5 := by
    simpa [roughSaiasFullyRealHyperbolaCoordinate] using hface
  have hnative := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := (X : ℝ) / s) hsOne hratio
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  have haCapS : (a : ℝ) ^ (5 : ℝ) ≤ s ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hs.1 (by norm_num)
  have hcommon : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply hnative.mono_set
    rw [Set.uIcc_of_le haCapOne,
      Set.uIcc_of_le (haCapOne.trans haCapS)]
    exact Set.Icc_subset_Icc le_rfl haCapS
  have htail : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s)
      volume ((a : ℝ) ^ (5 : ℝ)) (s ^ (5 : ℝ)) := by
    apply hnative.mono_set
    rw [Set.uIcc_of_le haCapS,
      Set.uIcc_of_le (haCapOne.trans haCapS)]
    exact Set.Icc_subset_Icc haCapOne le_rfl
  have hXcap : (X : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    roughSaiasFullyReal_le_rpow_five hXreal haOne hu5
  have hsupport : ((X : ℝ) / s) / s < (a : ℝ) ^ (5 : ℝ) := by
    calc
      ((X : ℝ) / s) / s < (X : ℝ) / s :=
        div_lt_self (div_pos hXreal hspos) hsOne
      _ < (X : ℝ) := div_lt_self hXreal hsOne
      _ ≤ (a : ℝ) ^ (5 : ℝ) := hXcap
  have htailZero :
      (∫ t in (a : ℝ) ^ (5 : ℝ)..s ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s t) = 0 := by
    calc
      (∫ t in (a : ℝ) ^ (5 : ℝ)..s ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel ((X : ℝ) / s) s t) =
        ∫ _t in (a : ℝ) ^ (5 : ℝ)..s ^ (5 : ℝ), (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htI : t ∈ Set.Icc ((a : ℝ) ^ (5 : ℝ)) (s ^ (5 : ℝ)) := by
            rw [Set.uIcc_of_le haCapS] at ht
            exact ht
          exact roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
            (div_pos hXreal hspos) hsOne (hsupport.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hcommon htail
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  rw [← hsplit, htailZero, add_zero]
  apply intervalIntegral.integral_congr
  intro t _ht
  exact roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq X s t

/-- One within-cell fully real fractional-integral displacement is bounded
by its deterministic integrated oscillation ledger. -/
theorem roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_cell_abs_sub_le
    {X a b m : ℕ} (hX : 0 < X) (ha2 : 2 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5)
    {s : ℝ} (hs : s ∈ Set.Icc (m : ℝ) (m + 1 : ℕ)) :
    |roughSaiasFullyRealBaseFreeFractionalIntegral ((X : ℝ) / s) s -
        roughSaiasFullyRealBaseFreeFractionalIntegral
          ((X : ℝ) / (m + 1 : ℕ)) (m + 1 : ℕ)| ≤
      roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
  have hmData := Finset.mem_Ico.mp hm
  have hsmem : s ∈ Set.Icc (a : ℝ) (b : ℝ) := by
    constructor
    · exact (by exact_mod_cast hmData.1 : (a : ℝ) ≤ (m : ℝ)).trans hs.1
    · exact hs.2.trans (by exact_mod_cast (show m + 1 ≤ b by omega))
  have hnextmem : ((m + 1 : ℕ) : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
    constructor
    · exact_mod_cast (show a ≤ m + 1 by omega)
    · exact_mod_cast (show m + 1 ≤ b by omega)
  have hsEq := roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_eq_firstCap
    hX ha2 hab hbX hsmem hu5
  have hnextEq :=
    roughSaiasFullyRealBaseFreeFractionalIntegral_hyperbola_eq_firstCap
      hX ha2 hab hbX hnextmem hu5
  have hsOne : 1 < s :=
    (by exact_mod_cast (show 1 < a by omega) : (1 : ℝ) < (a : ℝ)).trans_le hsmem.1
  have hnextOne : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < m + 1 by omega)
  have hbXR : (b : ℝ) ≤ (X : ℝ) := by exact_mod_cast hbX
  have hfaceS := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := s) (t := (1 : ℝ)) hX ha2 hsmem.1
      (hsmem.2.trans hbXR) (by norm_num) hu5
  have hfaceNext := roughSaiasFullyRealHyperbolaCoordinate_le_five
    (s := ((m + 1 : ℕ) : ℝ)) (t := (1 : ℝ)) hX ha2
      hnextmem.1 (hnextmem.2.trans hbXR) (by norm_num) hu5
  have hcapS :=
    (roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
      (x := (X : ℝ) / s) hsOne
      (by simpa [roughSaiasFullyRealHyperbolaCoordinate] using hfaceS)).mono_set
      (by
        have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
        have haCapS : (a : ℝ) ^ (5 : ℝ) ≤ s ^ (5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hsmem.1 (by norm_num)
        rw [Set.uIcc_of_le haCapOne, Set.uIcc_of_le (haCapOne.trans haCapS)]
        exact Set.Icc_subset_Icc le_rfl haCapS)
  have hcapNext :=
    (roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
      (x := (X : ℝ) / (m + 1 : ℕ)) hnextOne
      (by simpa [roughSaiasFullyRealHyperbolaCoordinate] using hfaceNext)).mono_set
      (by
        have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
          Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
        have haCapNext : (a : ℝ) ^ (5 : ℝ) ≤
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hnextmem.1 (by norm_num)
        rw [Set.uIcc_of_le haCapOne,
          Set.uIcc_of_le (haCapOne.trans haCapNext)]
        exact Set.Icc_subset_Icc le_rfl haCapNext)
  have hcapSWeighted : IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply hcapS.congr
    intro t _ht
    exact roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq X s t
  have hcapNextWeighted : IntervalIntegrable
      (fun t : ℝ => (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasFullyRealHyperbolaScaledDickmanKernel
          X ((m + 1 : ℕ) : ℝ) t)
      volume (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
    apply hcapNext.congr
    intro t _ht
    exact roughSaiasFullyRealBaseFreeFractionalKernel_hyperbola_eq
      X ((m + 1 : ℕ) : ℝ) t
  have hledgerInt :=
    roughSaiasFullyRealHyperbolaCellFractionalOscillation_intervalIntegrable
      hX ha2 hab hbX hm hu5
  have haCapOne : (1 : ℝ) ≤ (a : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a by omega)) (by norm_num)
  rw [hsEq, hnextEq,
    ← intervalIntegral.integral_sub hcapSWeighted hcapNextWeighted]
  calc
    |∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t -
          (Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel
              X ((m + 1 : ℕ) : ℝ) t| ≤
      ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        |(Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel X s t -
          (Int.fract t / t ^ (2 : ℕ)) *
            roughSaiasFullyRealHyperbolaScaledDickmanKernel
              X ((m + 1 : ℕ) : ℝ) t| :=
        intervalIntegral.abs_integral_le_integral_abs haCapOne
    _ ≤ ∫ t in (1 : ℝ)..(a : ℝ) ^ (5 : ℝ),
        roughSaiasFullyRealHyperbolaCellFractionalOscillation X m t := by
      apply intervalIntegral.integral_mono_on haCapOne
        (hcapSWeighted.sub hcapNextWeighted).abs hledgerInt
      intro t ht
      have htI : t ∈ Set.Icc (1 : ℝ) ((a : ℝ) ^ (5 : ℝ)) := by
        simpa [Set.uIcc_of_le haCapOne] using ht
      have htpos : 0 < t := zero_lt_one.trans_le htI.1
      have htSqPos : 0 < t ^ (2 : ℕ) := pow_pos htpos 2
      have hfactorNonneg : 0 ≤ Int.fract t / t ^ (2 : ℕ) :=
        div_nonneg (Int.fract_nonneg t) htSqPos.le
      have hkernel :=
        roughSaiasFullyRealHyperbolaScaledDickmanKernel_cell_abs_sub_le
          hX ha2 hab hbX hm hu5 hs htI.1
      unfold roughSaiasFullyRealHyperbolaCellFractionalOscillation
      rw [← mul_sub, abs_mul, abs_of_nonneg hfactorNonneg]
      exact mul_le_mul_of_nonneg_left hkernel hfactorNonneg
    _ = roughSaiasFullyRealHyperbolaCellFractionalOscillationLedger X a m := by
      rfl

/-- Exact telescoping of the absolute scaled-kernel variation on a finite
base block on which every base remains active and on the five constructed
faces. -/
theorem roughSaiasScaledDickmanKernel_sum_abs_succ_sub_eq
    {q a b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a) (hab : a ≤ b)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ (q : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) =
      roughSaiasScaledDickmanKernel q a t -
        roughSaiasScaledDickmanKernel q b t := by
  have hmono : ∀ m ∈ Finset.Ico a b,
      roughSaiasScaledDickmanKernel q (m + 1) t ≤
        roughSaiasScaledDickmanKernel q m t := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hmNow : m ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    have hmNext : m + 1 ∈ Finset.Icc a b := by
      rw [Finset.mem_Icc]
      omega
    exact roughSaiasScaledDickmanKernel_succ_le_of_active
      hq1 (by omega) htpos (hactive (m + 1) hmNext) (hface m hmNow)
  calc
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) =
        ∑ m ∈ Finset.Ico a b,
          (roughSaiasScaledDickmanKernel q m t -
            roughSaiasScaledDickmanKernel q (m + 1) t) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [abs_of_nonpos (sub_nonpos.mpr (hmono m hm))]
      ring
    _ = roughSaiasScaledDickmanKernel q a t -
        roughSaiasScaledDickmanKernel q b t := by
      clear hmono hactive hface
      induction b, hab using Nat.le_induction with
      | base => simp
      | succ b hab ih =>
          rw [Finset.sum_Ico_succ_top hab, ih]
          ring

/-- Quantitative all-active block variation.  The exact telescoping sum is
at most the inverse logarithm of the first base. -/
theorem roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_inv_log
    {q a b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a) (hab : a ≤ b)
    {t : ℝ} (htpos : 0 < t)
    (hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ (q : ℝ) / (m : ℝ))
    (hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) ≤
      1 / Real.log (a : ℝ) := by
  have haMem : a ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, hab⟩
  have hbMem : b ∈ Finset.Icc a b := by
    rw [Finset.mem_Icc]
    exact ⟨hab, le_rfl⟩
  have hb2 : 2 ≤ b := ha2.trans hab
  have huA1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate q a t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      ha2 htpos (hactive a haMem)
  have huB1 :
      1 ≤ roughSaiasBaseFreeDickmanCoordinate q b t :=
    one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
      hb2 htpos (hactive b hbMem)
  have hA_nonpos : roughSaiasScaledDickmanKernel q a t ≤ 0 :=
    roughSaiasScaledDickmanKernel_nonpos_of_active
      ha2 huA1 (hface a haMem)
  have hB_nonpos : roughSaiasScaledDickmanKernel q b t ≤ 0 :=
    roughSaiasScaledDickmanKernel_nonpos_of_active
      hb2 huB1 (hface b hbMem)
  have hBabs : |roughSaiasScaledDickmanKernel q b t| ≤
      1 / Real.log (b : ℝ) :=
    roughSaiasScaledDickmanKernel_abs_le_inv_log
      hb2 (hface b hbMem)
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hlogab : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < a by omega))
      (by exact_mod_cast hab)
  rw [roughSaiasScaledDickmanKernel_sum_abs_succ_sub_eq
      hq1 ha2 hab htpos hactive hface]
  calc
    roughSaiasScaledDickmanKernel q a t -
        roughSaiasScaledDickmanKernel q b t ≤
      -roughSaiasScaledDickmanKernel q b t := by linarith
    _ = |roughSaiasScaledDickmanKernel q b t| :=
      (abs_of_nonpos hB_nonpos).symm
    _ ≤ 1 / Real.log (b : ℝ) := hBabs
    _ ≤ 1 / Real.log (a : ℝ) :=
      one_div_le_one_div_of_le hloga hlogab

/-- Endpoint form of the all-active block estimate.  Activity at the last
base and the five-face condition at the first base automatically propagate
through the whole block. -/
theorem roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_inv_log_of_last_active
    {q a b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a) (hab : a ≤ b)
    {t : ℝ} (htpos : 0 < t)
    (htactive : t ≤ (q : ℝ) / (b : ℝ))
    (hua5 : roughSaiasBaseFreeDickmanCoordinate q a t ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t|) ≤
      1 / Real.log (a : ℝ) := by
  have hb1 : 1 ≤ b := by omega
  have htq : t ≤ (q : ℝ) :=
    htactive.trans
      (div_le_self (by positivity) (by exact_mod_cast hb1))
  have hactive : ∀ m ∈ Finset.Icc a b,
      t ≤ (q : ℝ) / (m : ℝ) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hdiv : (q : ℝ) / (b : ℝ) ≤ (q : ℝ) / (m : ℝ) := by
      exact div_le_div_of_nonneg_left (by positivity)
        (by exact_mod_cast (show 0 < m by omega))
        (by exact_mod_cast hm.2)
    exact htactive.trans hdiv
  have hface : ∀ m ∈ Finset.Icc a b,
      roughSaiasBaseFreeDickmanCoordinate q m t ≤ 5 := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    exact (roughSaiasBaseFreeDickmanCoordinate_antitone_base
      ha2 hm.1 htpos htq).trans hua5
  exact roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_inv_log
    hq1 ha2 hab htpos hactive hface

/-- Arbitrary one-cutoff block variation.  The bases in `[a,c]` are active,
the bases in `(c,b]` are beyond support, and the sole reset from the active
negative branch to zero costs one additional inverse logarithm. -/
theorem roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_two_inv_log_of_cutoff
    {q a c b : ℕ} (hq1 : 1 ≤ q) (ha2 : 2 ≤ a)
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
      2 / Real.log (a : ℝ) := by
  have hloga : 0 < Real.log (a : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hactiveBound :
      (∑ m ∈ Finset.Ico a c,
          |roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t|) ≤
        1 / Real.log (a : ℝ) :=
    roughSaiasScaledDickmanKernel_sum_abs_succ_sub_le_inv_log
      hq1 ha2 hac htpos hactive hface
  rcases hcb.eq_or_lt with rfl | hcbLt
  · exact hactiveBound.trans (by
      have hinv : 0 ≤ 1 / Real.log (a : ℝ) := by positivity
      calc
        1 / Real.log (a : ℝ) ≤
            1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
          le_add_of_nonneg_right hinv
        _ = 2 / Real.log (a : ℝ) := by ring)
  · have hc2 : 2 ≤ c := ha2.trans hac
    have hcMem : c ∈ Finset.Icc a c := by
      rw [Finset.mem_Icc]
      exact ⟨hac, le_rfl⟩
    have hcNextMem : c + 1 ∈ Finset.Ioc c b := by
      rw [Finset.mem_Ioc]
      omega
    have hcNextZero :
        roughSaiasScaledDickmanKernel q (c + 1) t = 0 :=
      roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
        hq1 (by omega) (hinactive (c + 1) hcNextMem)
    have htailZero :
        (∑ m ∈ Finset.Ico (c + 1) b,
          |roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t|) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      rw [Finset.mem_Ico] at hm
      have hmMem : m ∈ Finset.Ioc c b := by
        rw [Finset.mem_Ioc]
        omega
      have hmNextMem : m + 1 ∈ Finset.Ioc c b := by
        rw [Finset.mem_Ioc]
        omega
      have hmZero : roughSaiasScaledDickmanKernel q m t = 0 :=
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hq1 (by omega) (hinactive m hmMem)
      have hmNextZero :
          roughSaiasScaledDickmanKernel q (m + 1) t = 0 :=
        roughSaiasScaledDickmanKernel_eq_zero_of_div_lt
          hq1 (by omega) (hinactive (m + 1) hmNextMem)
      rw [hmZero, hmNextZero, sub_self, abs_zero]
    have htail :
        (∑ m ∈ Finset.Ico c b,
          |roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t|) =
          |roughSaiasScaledDickmanKernel q c t| := by
      rw [Finset.sum_eq_sum_Ico_succ_bot hcbLt, hcNextZero,
        zero_sub, abs_neg, htailZero, add_zero]
    have hcAbs : |roughSaiasScaledDickmanKernel q c t| ≤
        1 / Real.log (c : ℝ) :=
      roughSaiasScaledDickmanKernel_abs_le_inv_log
        hc2 (hface c hcMem)
    have hlogac : Real.log (a : ℝ) ≤ Real.log (c : ℝ) :=
      Real.log_le_log
        (by exact_mod_cast (show 0 < a by omega))
        (by exact_mod_cast hac)
    have hcAbs' : |roughSaiasScaledDickmanKernel q c t| ≤
        1 / Real.log (a : ℝ) :=
      hcAbs.trans (one_div_le_one_div_of_le hloga hlogac)
    rw [← Finset.sum_Ico_consecutive _ hac hcb, htail]
    calc
      (∑ m ∈ Finset.Ico a c,
          |roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t|) +
          |roughSaiasScaledDickmanKernel q c t| ≤
        1 / Real.log (a : ℝ) + 1 / Real.log (a : ℝ) :=
          add_le_add hactiveBound hcAbs'
      _ = 2 / Real.log (a : ℝ) := by ring

end

end Erdos390.WholePaper
