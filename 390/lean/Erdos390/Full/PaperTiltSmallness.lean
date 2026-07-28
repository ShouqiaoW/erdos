import Erdos390.Full.ValuationTiltCell
import Erdos390.Full.PrimeSums

/-!
# Non-circular smallness of the actual valuation tilt

The omitted-score denominator is automatically positive at the paper scale.
The fixed box and cutoff enter only through a fixed exponential constant;
the remaining factor is `O(log L / L)`.
-/

open Filter Topology

namespace Erdos390.Full.PaperTiltSmallness

open ArithmeticModel Scale PrimeSums
open DivisibilityMomentBounds FiniteProbability
open ValuationScoreDomination ValuationTiltCell

noncomputable section

/-- With a fixed physical multiplier, fixed coefficient box and fixed prime
cutoff, the explicit majorant used for the actual valuation-tilt denominator
is eventually smaller than one.  This is the paper's `W -> box -> n`
ordering, with no constant depending on `n` or on a marked divisor. -/
theorem eventually_actual_valuationTilt_small
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) * ((2 / c) * bandReciprocalSum n W) < 1 := by
  let Kbound : ℝ := 2 * B / Real.log (W : ℝ)
  let small : ℕ → ℝ := fun n ↦
    (B / L n) * ((2 / c) * bandReciprocalSum n W)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (𝓝 0) := by
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto
      (fun n : ℕ ↦ (24 * B / c) * (Real.log (L n) / L n))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hratio)
  have hsmallNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ small n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    have hL : 0 < L n := L_pos hn
    dsimp only [small]
    exact mul_nonneg (div_nonneg hB hL.le)
      (mul_nonneg (div_nonneg (by norm_num) hc.le)
        (by
          unfold bandReciprocalSum
          exact Finset.sum_nonneg fun p hp ↦ by positivity))
  have hsmallMajor : ∀ᶠ n : ℕ in atTop,
      small n ≤ (24 * B / c) * (Real.log (L n) / L n) := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      Filter.eventually_gt_atTop 1] with n hband hn
    have hL : 0 < L n := L_pos hn
    have hcoef : 0 ≤ (B / L n) * (2 / c) :=
      mul_nonneg (div_nonneg hB hL.le) (div_nonneg (by norm_num) hc.le)
    dsimp only [small]
    calc
      (B / L n) * ((2 / c) * bandReciprocalSum n W) =
          ((B / L n) * (2 / c)) * bandReciprocalSum n W := by ring
      _ ≤ ((B / L n) * (2 / c)) * (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef
      _ = (24 * B / c) * (Real.log (L n) / L n) := by ring
  have hsmallT : Tendsto small atTop (𝓝 0) :=
    squeeze_zero' hsmallNonneg hsmallMajor hmajor
  have hsmallEventually : ∀ᶠ n : ℕ in atTop,
      small n < Real.exp (-Kbound) := by
    exact hsmallT (Iio_mem_nhds (Real.exp_pos (-Kbound)))
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [hsmallEventually, hsmallNonneg, hCevent, hInvCevent,
    Filter.eventually_gt_atTop 1] with n hsmall hsmall0 hCn hInvCn hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hphysLower : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  have hphysPos : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one hphysLower
  have hphysCast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogPhys : Real.log (physicalBound C n : ℝ) ≤ 2 * L n := by
    have hleSq : (physicalBound C n : ℝ) ≤ (n : ℝ) ^ 2 :=
      hphysCast.trans hCnSq
    have hlog := Real.log_le_log (by exact_mod_cast hphysPos) hleSq
    rw [Real.log_pow] at hlog
    simpa [L] using hlog
  have hK :
      (B / L n) *
          (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ)) ≤
        Kbound := by
    calc
      _ ≤ (B / L n) * ((2 * L n) / Real.log (W : ℝ)) := by
        gcongr
      _ = Kbound := by
        dsimp only [Kbound]
        field_simp [hL.ne', hlogW.ne']
  have hexp : Real.exp
      ((B / L n) *
        (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) ≤
      Real.exp Kbound := Real.exp_le_exp.mpr hK
  calc
    Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) * ((2 / c) * bandReciprocalSum n W) =
        Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        small n := by
      dsimp only [small]
      ring
    _ ≤ Real.exp Kbound * small n :=
      mul_le_mul_of_nonneg_right hexp hsmall0
    _ < Real.exp Kbound * Real.exp (-Kbound) :=
      mul_lt_mul_of_pos_left hsmall (Real.exp_pos Kbound)
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The preceding paper-scale estimate dominates the exact prime-power
normalizer for every omitted-score set of primes contained in the actual
band.  In particular, the cutoff set may depend on `n` and may omit one or
two local primes; the threshold is still chosen uniformly before that set. -/
theorem eventually_actual_valuationTilt_small_for_subset
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ P : Finset ℕ, P ⊆ primeBand n W →
      Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) *
          ((1 / c) *
            ∑ a ∈ primePowerModuli P (physicalBound C n),
              1 / (a : ℝ)) < 1 := by
  filter_upwards [eventually_actual_valuationTilt_small B C c W hB hC hc hW,
    Filter.eventually_gt_atTop 1] with n hsmall hn
  intro P hP
  have hL : 0 < L n := L_pos hn
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (hP hp)
  have hPsum : (∑ p ∈ P, 1 / (p : ℝ)) ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    exact Finset.sum_le_sum_of_subset_of_nonneg hP
      (fun p hpBand hpNotP ↦ by positivity)
  have hpowers :
      (∑ a ∈ primePowerModuli P (physicalBound C n), 1 / (a : ℝ)) ≤
        2 * bandReciprocalSum n W := by
    exact (sum_inv_primePowerModuli_le P (physicalBound C n) hprime).trans
      (mul_le_mul_of_nonneg_left hPsum (by norm_num))
  let pref : ℝ :=
    Real.exp
        ((B / L n) *
          (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
      (B / L n) * (1 / c)
  have hpref : 0 ≤ pref := by
    dsimp only [pref]
    positivity
  calc
    Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) *
          ((1 / c) *
            ∑ a ∈ primePowerModuli P (physicalBound C n),
              1 / (a : ℝ)) =
        pref *
          (∑ a ∈ primePowerModuli P (physicalBound C n),
            1 / (a : ℝ)) := by
      dsimp only [pref]
      ring
    _ ≤ pref * (2 * bandReciprocalSum n W) :=
      mul_le_mul_of_nonneg_left hpowers hpref
    _ = Real.exp
          ((B / L n) *
            (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
        (B / L n) * ((2 / c) * bandReciprocalSum n W) := by
      dsimp only [pref]
      ring
    _ < 1 := hsmall

/-- Paper-scale omitted-score comparison with the normalizing-smallness
condition discharged once and for all.  The event in `n` is uniform over the
actual cell, the marked modulus, the box coefficients, and every subset of
the moving prime band.  All remaining hypotheses are literal arithmetic
properties of the chosen cell. -/
theorem eventually_abs_actual_valuationTilt_divInd_sub_average_le
    (B C c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hC : 0 < C)
    (hc : 0 < c) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (S P : Finset ℕ) (eta : ℕ → ℝ) (D : ℕ),
        P ⊆ primeBand n W → ∀ hS : S.Nonempty, 0 < D →
        c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) →
        (∀ m ∈ S, 0 < m) →
        (∀ m ∈ S, m ≤ physicalBound C n) →
        (∀ p ∈ P, Nat.Coprime D p) →
        (∀ p ∈ P, |eta p| ≤ B) →
        |((uniformOnFinset S hS).exponentialTilt
              (fun m : S ↦ valuationScore P eta (L n) m)).expect
              (fun m : S ↦ divInd D m) -
            uniformAverage S (divInd D)| ≤
          (Real.exp ((B / L n) *
              (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
              (B / L n) *
              ((1 / (c * (D : ℝ))) *
                ∑ a ∈ primePowerModuli P (physicalBound C n),
                  1 / (a : ℝ)) +
            Real.exp ((B / L n) *
              (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
              uniformAverage S (divInd D) *
              ((B / L n) *
                ((1 / c) *
                  ∑ a ∈ primePowerModuli P (physicalBound C n),
                    1 / (a : ℝ)))) /
          (1 -
            Real.exp ((B / L n) *
              (Real.log (physicalBound C n : ℝ) / Real.log (W : ℝ))) *
              (B / L n) *
              ((1 / c) *
                ∑ a ∈ primePowerModuli P (physicalBound C n),
                  1 / (a : ℝ))) := by
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  filter_upwards [eventually_actual_valuationTilt_small_for_subset
      B C c W hB hC hc hW, hInvCevent,
    Filter.eventually_gt_atTop 1] with n hsmallAll hInvCn hn
  intro S P eta D hP hS hD hcard hSpos hSle hcop heta
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hphysLower : 1 ≤ physicalBound C n := by
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  have hM : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one hphysLower
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeBand (hP hp)
  have hpW : ∀ p ∈ P, W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand (hP hp)).le
  exact abs_valuationTilt_divInd_sub_average_le
    S P hS eta hD hM hB hL hW hc hcard hSpos hSle hprime hpW hcop heta
      (hsmallAll P hP)

end

end Erdos390.Full.PaperTiltSmallness
