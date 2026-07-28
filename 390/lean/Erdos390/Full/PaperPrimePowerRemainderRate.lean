import Erdos390.Full.PaperPrimePowerTailRow
import Erdos390.Full.OmittedTiltHarmonicRate

/-!
# Common vanishing remainder for Lemma 7.5

The omitted-score error must survive one complete harmonic prime sum.  This
file propagates the strengthened `epsilon * log L -> 0` estimate through the
local restoration and covariance polynomials, and then combines it with the
literal beyond-four row.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerRemainderRate

open ArithmeticModel Scale PrimeSums
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation PaperPrimePowerTailRow

noncomputable section

private theorem tendsto_const_mul_zero
    (a : ℝ) {f : ℕ → ℝ} (hf : Tendsto f atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦ a * f n) atTop (nhds 0) := by
  have ha : Tendsto (fun _n : ℕ ↦ a) atTop (nhds a) :=
    tendsto_const_nhds
  simpa only [mul_zero] using ha.mul hf

theorem tendsto_coefficientScale_zero
    (B : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ coefficientScale B W n) atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun n : ℕ ↦ (L n)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))
      atTop (nhds ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
    tendsto_const_nhds
  have hmul := hconst.mul hInv
  have hmul0 : Tendsto
      (fun n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)) *
        (L n)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using hmul
  apply hmul0.congr'
  filter_upwards with n
  unfold coefficientScale
  ring

theorem tendsto_coefficientScale_mul_logL_zero
    (B : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦
      coefficientScale B W n * Real.log (L n)) atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratioReal : Tendsto (fun x : ℝ ↦ Real.log x / x)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hratio := hratioReal.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))
      atTop (nhds ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
    tendsto_const_nhds
  have hmul := hconst.mul hratio
  have hmul0 : Tendsto
      (fun n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)) *
        (Real.log (L n) / L n)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using hmul
  apply hmul0.congr'
  filter_upwards with n
  unfold coefficientScale
  ring

/-- The explicit coefficient tail also survives two harmonic losses. -/
theorem tendsto_coefficientScale_mul_logL_sq_zero
    (B : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ coefficientScale B W n * Real.log (L n) ^ 2)
      atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ Real.log (L n) ^ 2 / L n)
      atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hconst : Tendsto
      (fun _n : ℕ ↦ (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))
      atTop (nhds ((2 * B) * Real.exp (2 * B / Real.log (W : ℝ)))) :=
    tendsto_const_nhds
  have hmul := hconst.mul hratio
  have hmul0 : Tendsto (fun n : ℕ ↦
      (2 * B) * Real.exp (2 * B / Real.log (W : ℝ)) *
        (Real.log (L n) ^ 2 / L n)) atTop (nhds 0) := by
    simpa only [mul_zero] using hmul
  apply hmul0.congr'
  filter_upwards with n
  unfold coefficientScale
  ring

/-- The common chamber remainder tends to zero and remains vanishing after
one harmonic loss. -/
theorem tendsto_primePowerChamberRemainder_zero_and_rate
    (epsilon : ℕ → ℝ) (G₀ B : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n))
        atTop (nhds 0) ∧
    Tendsto (fun n : ℕ ↦
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
        Real.log (L n)) atTop (nhds 0) := by
  let k : ℕ → ℝ := fun n ↦ coefficientScale B W n
  have hk := tendsto_coefficientScale_zero B W
  have hkRate := tendsto_coefficientScale_mul_logL_zero B W
  have hkSq : Tendsto (fun n : ℕ ↦ k n ^ 2) atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hk.pow 2
  have hkSqRate : Tendsto
      (fun n : ℕ ↦ k n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
    have hprod := hk.mul hkRate
    have hprod0 : Tendsto
        (fun n : ℕ ↦ k n * (k n * Real.log (L n)))
          atTop (nhds 0) := by
      simpa only [k, mul_zero] using hprod
    apply hprod0.congr'
    filter_upwards with n
    ring

  let loc : ℕ → ℝ := fun n ↦ localRestorationScale G₀ (k n)
  have hloc : Tendsto loc atTop (nhds 0) := by
    have hpoly : Tendsto (fun n : ℕ ↦ 2 * k n + k n ^ 2)
        atTop (nhds 0) := by
      simpa only [add_zero] using (tendsto_const_mul_zero 2 hk).add hkSq
    simpa only [loc, localRestorationScale] using
      tendsto_const_mul_zero G₀ hpoly
  have hlocRate : Tendsto
      (fun n : ℕ ↦ loc n * Real.log (L n)) atTop (nhds 0) := by
    have hpolyRate : Tendsto (fun n : ℕ ↦
        (2 * k n + k n ^ 2) * Real.log (L n)) atTop (nhds 0) := by
      have htwo := tendsto_const_mul_zero 2 hkRate
      have hadd := htwo.add hkSqRate
      have hadd0 : Tendsto (fun n : ℕ ↦
          2 * (coefficientScale B W n * Real.log (L n)) +
            k n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
        simpa only [add_zero] using hadd
      apply hadd0.congr'
      filter_upwards with n
      ring
    have hbase := tendsto_const_mul_zero G₀ hpolyRate
    apply hbase.congr'
    filter_upwards with n
    unfold loc localRestorationScale
    ring
  let E : ℕ → ℝ := fun n ↦
    pairProbabilityScale (epsilon n) G₀ (k n)
  have hE : Tendsto E atTop (nhds 0) := by
    have hRloc := tendsto_const_mul_zero
      (1 / DickmanBasic.rho DickmanBasic.U) hloc
    have hsum := (hloc.add hepsilon).add hRloc
    have hsum0 : Tendsto (fun n : ℕ ↦
        loc n + epsilon n +
          (1 / DickmanBasic.rho DickmanBasic.U) * loc n)
        atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have htwo := tendsto_const_mul_zero 2 hsum0
    apply htwo.congr'
    filter_upwards with n
    unfold E pairProbabilityScale
    dsimp only [loc]
  have hERate : Tendsto (fun n : ℕ ↦ E n * Real.log (L n))
      atTop (nhds 0) := by
    have hRloc := tendsto_const_mul_zero
      (1 / DickmanBasic.rho DickmanBasic.U) hlocRate
    have hsum := (hlocRate.add hepsilonRate).add hRloc
    have hsum0 : Tendsto (fun n : ℕ ↦
        loc n * Real.log (L n) + epsilon n * Real.log (L n) +
          (1 / DickmanBasic.rho DickmanBasic.U) *
            (loc n * Real.log (L n))) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have htwo := tendsto_const_mul_zero 2 hsum0
    apply htwo.congr'
    filter_upwards with n
    unfold E pairProbabilityScale
    dsimp only [loc]
    ring
  let ECov : ℕ → ℝ := fun n ↦ pairCovarianceScale (E n)
  have hESq : Tendsto (fun n : ℕ ↦ E n ^ 2) atTop (nhds 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hE.pow 2
  have hESqRate : Tendsto (fun n : ℕ ↦
      E n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
    have hprod := hE.mul hERate
    have hprod0 : Tendsto
        (fun n : ℕ ↦ E n * (E n * Real.log (L n)))
          atTop (nhds 0) := by
      simpa only [mul_zero] using hprod
    apply hprod0.congr'
    filter_upwards with n
    ring
  have hECov : Tendsto ECov atTop (nhds 0) := by
    have hlin := tendsto_const_mul_zero
      (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) hE
    have hadd := hlin.add hESq
    have hadd0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) * E n + E n ^ 2)
        atTop (nhds 0) := by
      simpa only [add_zero] using hadd
    apply hadd0.congr'
    filter_upwards with n
    unfold ECov pairCovarianceScale
    ring
  have hECovRate : Tendsto
      (fun n : ℕ ↦ ECov n * Real.log (L n)) atTop (nhds 0) := by
    have hlin := tendsto_const_mul_zero
      (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) hERate
    have hadd := hlin.add hESqRate
    have hadd0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
            (E n * Real.log (L n)) +
          E n ^ 2 * Real.log (L n)) atTop (nhds 0) := by
      simpa only [add_zero] using hadd
    apply hadd0.congr'
    filter_upwards with n
    unfold ECov pairCovarianceScale
    ring
  constructor
  · have hagg := (tendsto_const_mul_zero 2 hECov).add hE
    have hagg0 : Tendsto (fun n : ℕ ↦ 2 * ECov n + E n)
        atTop (nhds 0) := by simpa only [add_zero] using hagg
    apply hagg0.congr'
    filter_upwards with n
    unfold primePowerChamberRemainder aggregateChamberScale
    dsimp only [ECov, E, k]
  · have hagg := (tendsto_const_mul_zero 2 hECovRate).add hERate
    have hagg0 : Tendsto (fun n : ℕ ↦
        2 * (ECov n * Real.log (L n)) + E n * Real.log (L n))
        atTop (nhds 0) := by simpa only [add_zero] using hagg
    apply hagg0.congr'
    filter_upwards with n
    unfold primePowerChamberRemainder aggregateChamberScale
    dsimp only [ECov, E, k]
    ring

/-- The chamber polynomial preserves the stronger two-harmonic rate. -/
theorem tendsto_primePowerChamberRemainder_mul_logL_sq_zero
    (epsilon : ℕ → ℝ) (G₀ B : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRateSq : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2) atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
        Real.log (L n) ^ 2) atTop (nhds 0) := by
  let k : ℕ → ℝ := fun n ↦ coefficientScale B W n
  have hk : Tendsto k atTop (nhds 0) := tendsto_coefficientScale_zero B W
  have hkRateSq : Tendsto (fun n : ℕ ↦ k n * Real.log (L n) ^ 2)
      atTop (nhds 0) := by
    simpa only [k] using tendsto_coefficientScale_mul_logL_sq_zero B W
  have hkSqRateSq : Tendsto
      (fun n : ℕ ↦ k n ^ 2 * Real.log (L n) ^ 2) atTop (nhds 0) := by
    have hprod := hk.mul hkRateSq
    have hprod0 : Tendsto
        (fun n : ℕ ↦ k n * (k n * Real.log (L n) ^ 2))
        atTop (nhds 0) := by simpa only [mul_zero] using hprod
    apply hprod0.congr'
    filter_upwards with n
    ring
  let loc : ℕ → ℝ := fun n ↦ localRestorationScale G₀ (k n)
  have hlocRateSq : Tendsto
      (fun n : ℕ ↦ loc n * Real.log (L n) ^ 2) atTop (nhds 0) := by
    have hpoly := (tendsto_const_mul_zero 2 hkRateSq).add hkSqRateSq
    have hpoly0 : Tendsto (fun n : ℕ ↦
        2 * (k n * Real.log (L n) ^ 2) +
          k n ^ 2 * Real.log (L n) ^ 2) atTop (nhds 0) := by
      simpa only [add_zero] using hpoly
    have hscaled := tendsto_const_mul_zero G₀ hpoly0
    apply hscaled.congr'
    filter_upwards with n
    unfold loc localRestorationScale
    ring
  let E : ℕ → ℝ := fun n ↦ pairProbabilityScale (epsilon n) G₀ (k n)
  have hERateSq : Tendsto
      (fun n : ℕ ↦ E n * Real.log (L n) ^ 2) atTop (nhds 0) := by
    have hRloc := tendsto_const_mul_zero
      (1 / DickmanBasic.rho DickmanBasic.U) hlocRateSq
    have hsum := (hlocRateSq.add hepsilonRateSq).add hRloc
    have hsum0 : Tendsto (fun n : ℕ ↦
        loc n * Real.log (L n) ^ 2 +
          epsilon n * Real.log (L n) ^ 2 +
          (1 / DickmanBasic.rho DickmanBasic.U) *
            (loc n * Real.log (L n) ^ 2)) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have htwo := tendsto_const_mul_zero 2 hsum0
    apply htwo.congr'
    filter_upwards with n
    unfold E pairProbabilityScale
    dsimp only [loc]
    ring
  have hE : Tendsto E atTop (nhds 0) := by
    have hkSq : Tendsto (fun n : ℕ ↦ k n ^ 2) atTop (nhds 0) := by
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hk.pow 2
    have hloc : Tendsto loc atTop (nhds 0) := by
      have hpoly := (tendsto_const_mul_zero 2 hk).add hkSq
      have hpoly0 : Tendsto (fun n : ℕ ↦ 2 * k n + k n ^ 2)
          atTop (nhds 0) := by simpa only [add_zero] using hpoly
      simpa only [loc, localRestorationScale] using
        tendsto_const_mul_zero G₀ hpoly0
    have hRloc := tendsto_const_mul_zero
      (1 / DickmanBasic.rho DickmanBasic.U) hloc
    have hsum := (hloc.add hepsilon).add hRloc
    have hsum0 : Tendsto (fun n : ℕ ↦
        loc n + epsilon n +
          (1 / DickmanBasic.rho DickmanBasic.U) * loc n)
        atTop (nhds 0) := by simpa only [add_zero] using hsum
    have htwo := tendsto_const_mul_zero 2 hsum0
    apply htwo.congr'
    filter_upwards with n
    unfold E pairProbabilityScale
    dsimp only [loc]
  have hESqRateSq : Tendsto
      (fun n : ℕ ↦ E n ^ 2 * Real.log (L n) ^ 2) atTop (nhds 0) := by
    have hprod := hE.mul hERateSq
    have hprod0 : Tendsto
        (fun n : ℕ ↦ E n * (E n * Real.log (L n) ^ 2))
        atTop (nhds 0) := by simpa only [mul_zero] using hprod
    apply hprod0.congr'
    filter_upwards with n
    ring
  let ECov : ℕ → ℝ := fun n ↦ pairCovarianceScale (E n)
  have hECovRateSq : Tendsto
      (fun n : ℕ ↦ ECov n * Real.log (L n) ^ 2) atTop (nhds 0) := by
    have hlin := tendsto_const_mul_zero
      (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) hERateSq
    have hsum := hlin.add hESqRateSq
    have hsum0 : Tendsto (fun n : ℕ ↦
        (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) *
            (E n * Real.log (L n) ^ 2) +
          E n ^ 2 * Real.log (L n) ^ 2) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold ECov pairCovarianceScale
    ring
  have htotal := (tendsto_const_mul_zero 2 hECovRateSq).add hERateSq
  have htotal0 : Tendsto (fun n : ℕ ↦
      2 * (ECov n * Real.log (L n) ^ 2) +
        E n * Real.log (L n) ^ 2) atTop (nhds 0) := by
    simpa only [add_zero] using htotal
  apply htotal0.congr'
  filter_upwards with n
  unfold primePowerChamberRemainder aggregateChamberScale
  dsimp only [ECov, E, k]
  ring

/-- The exact remainder appearing after finite aggregation. -/
def primePowerRowRemainder
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W n : ℕ) : ℝ :=
  pairAggregationConstant *
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) +
    tailRowMajorant Gf W n

theorem tendsto_primePowerRowRemainder_zero
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (nhds 0))
    (hepsilon0 : ∀ n, 0 ≤ epsilon n) (hG₀ : 0 ≤ G₀)
    (hB : 0 ≤ B) (hGf : 0 ≤ Gf) (hW : 1 < W) :
    Tendsto (primePowerRowRemainder epsilon G₀ B Gf W) atTop (nhds 0) := by
  obtain ⟨hchamber, hchamberRate⟩ :=
    tendsto_primePowerChamberRemainder_zero_and_rate
      epsilon G₀ B W hepsilon hepsilonRate
  let R : ℕ → ℝ := fun n ↦
    primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n)
  let upper : ℕ → ℝ := fun n ↦
    pairAggregationConstant *
      (12 * (R n * Real.log (L n)) + 5 * R n) * (1 / (W : ℝ))
  have hupperT : Tendsto upper atTop (nhds 0) := by
    have hscaledRate := tendsto_const_mul_zero 12 hchamberRate
    have hscaled := tendsto_const_mul_zero 5 hchamber
    have hsum := hscaledRate.add hscaled
    have hsum0 : Tendsto (fun n : ℕ ↦
        12 * (primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) * Real.log (L n)) +
        5 * primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n)) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    have houterLeft := tendsto_const_mul_zero pairAggregationConstant hsum0
    have houter := tendsto_const_mul_zero (1 / (W : ℝ)) houterLeft
    apply houter.congr'
    filter_upwards with n
    unfold upper
    dsimp only [R]
    ring
  have hchamberNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ R n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    unfold R
    exact primePowerChamberRemainder_nonneg
      (hepsilon0 n) hG₀ (by
        unfold coefficientScale
        have hL := L_pos hn
        positivity)
  have hbandUpper : ∀ᶠ n : ℕ in atTop,
      pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ)) ≤ upper n := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      hchamberNonneg] with n hband hR
    unfold upper
    have hAgg : 0 ≤ pairAggregationConstant := pairAggregationConstant_nonneg
    have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
    have hinside : R n * (bandReciprocalSum n W + 5) ≤
        12 * (R n * Real.log (L n)) + 5 * R n := by
      nlinarith [mul_le_mul_of_nonneg_left hband hR]
    calc
      pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ)) =
        (pairAggregationConstant * (R n * (bandReciprocalSum n W + 5))) *
          (1 / (W : ℝ)) := by ring
      _ ≤ (pairAggregationConstant *
          (12 * (R n * Real.log (L n)) + 5 * R n)) *
            (1 / (W : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinside hAgg) hWinv
      _ = upper n := by rfl
  have hbandNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
        (1 / (W : ℝ)) := by
    filter_upwards [hchamberNonneg] with n hR
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg pairAggregationConstant_nonneg hR)
        (by linarith))
      (by positivity)
  have hbandT := squeeze_zero' hbandNonneg hbandUpper hupperT
  have htail := tendsto_tailRowMajorant_zero Gf W hGf hW
  unfold primePowerRowRemainder
  simpa only [R, add_zero] using hbandT.add htail

/-- After the two-harmonic pointwise rate, the fully aggregated row still
has one harmonic rate left.  This is the exact `o(alpha_0)` input required
by the sharp moving-low-cell transfer. -/
theorem tendsto_primePowerRowRemainder_mul_logL_zero
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W : ℕ)
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (nhds 0))
    (hepsilonRateSq : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2) atTop (nhds 0))
    (hepsilon0 : ∀ n, 0 ≤ epsilon n) (hG₀ : 0 ≤ G₀)
    (hB : 0 ≤ B) (hGf : 0 ≤ Gf) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      primePowerRowRemainder epsilon G₀ B Gf W n * Real.log (L n))
      atTop (nhds 0) := by
  obtain ⟨hchamber, hchamberRate⟩ :=
    tendsto_primePowerChamberRemainder_zero_and_rate
      epsilon G₀ B W hepsilon hepsilonRate
  have hchamberRateSq :=
    tendsto_primePowerChamberRemainder_mul_logL_sq_zero
      epsilon G₀ B W hepsilon hepsilonRateSq
  let R : ℕ → ℝ := fun n ↦
    primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n)
  let upper : ℕ → ℝ := fun n ↦
    pairAggregationConstant *
      (12 * (R n * Real.log (L n) ^ 2) +
        5 * (R n * Real.log (L n))) * (1 / (W : ℝ))
  have hupperT : Tendsto upper atTop (nhds 0) := by
    have hscaledSq := tendsto_const_mul_zero 12 hchamberRateSq
    have hscaled := tendsto_const_mul_zero 5 hchamberRate
    have hsum := hscaledSq.add hscaled
    have hsum0 : Tendsto (fun n : ℕ ↦
        12 * (primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) * Real.log (L n) ^ 2) +
        5 * (primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) * Real.log (L n)))
        atTop (nhds 0) := by simpa only [add_zero] using hsum
    have hleft := tendsto_const_mul_zero pairAggregationConstant hsum0
    have hout := tendsto_const_mul_zero (1 / (W : ℝ)) hleft
    apply hout.congr'
    filter_upwards with n
    unfold upper
    dsimp only [R]
    ring
  have hchamberNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ R n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    unfold R
    exact primePowerChamberRemainder_nonneg
      (hepsilon0 n) hG₀ (by
        unfold coefficientScale
        have hL := L_pos hn
        positivity)
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbandUpper : ∀ᶠ n : ℕ in atTop,
      (pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ))) * Real.log (L n) ≤ upper n := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      hchamberNonneg, hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hband hR hL1
    have hlog : 0 ≤ Real.log (L n) := Real.log_nonneg hL1
    have hAgg : 0 ≤ pairAggregationConstant := pairAggregationConstant_nonneg
    have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
    have hinside : R n * (bandReciprocalSum n W + 5) * Real.log (L n) ≤
        12 * (R n * Real.log (L n) ^ 2) +
          5 * (R n * Real.log (L n)) := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hband hR) hlog
      nlinarith
    calc
      (pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ))) * Real.log (L n) =
        (pairAggregationConstant *
          (R n * (bandReciprocalSum n W + 5) * Real.log (L n))) *
            (1 / (W : ℝ)) := by ring
      _ ≤ (pairAggregationConstant *
          (12 * (R n * Real.log (L n) ^ 2) +
            5 * (R n * Real.log (L n)))) * (1 / (W : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinside hAgg) hWinv
      _ = upper n := by rfl
  have hbandNonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ (pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
        (1 / (W : ℝ))) * Real.log (L n) := by
    filter_upwards [hchamberNonneg,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hR hL1
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg pairAggregationConstant_nonneg hR) (by linarith))
        (by positivity)) (Real.log_nonneg hL1)
  have hbandT := squeeze_zero' hbandNonneg hbandUpper hupperT
  have htail := tendsto_tailRowMajorant_mul_logL_zero Gf W hGf hW
  change Tendsto (fun n : ℕ ↦
    (pairAggregationConstant *
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) +
      tailRowMajorant Gf W n) * Real.log (L n)) atTop (nhds 0)
  have hsum := hbandT.add htail
  have hsum0 : Tendsto (fun n : ℕ ↦
      pairAggregationConstant * R n * (bandReciprocalSum n W + 5) *
          (1 / (W : ℝ)) * Real.log (L n) +
        tailRowMajorant Gf W n * Real.log (L n))
      atTop (nhds 0) := by simpa only [add_zero] using hsum
  apply hsum0.congr'
  filter_upwards with n
  dsimp only [R]
  ring

end

end Erdos390.Full.PaperPrimePowerRemainderRate
