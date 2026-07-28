import Erdos390.WholePaper.BankPaperCanonicalRawRowCorrectionRateClosure
import Erdos390.WholePaper.BankPaperCanonicalGuardedRawCorrectionMomentDefectConnector

/-!
# Paper-rate closure for the guarded postcharge correction

The raw nonsmooth correction already has the strict
`secondOrderScale / (p * L)` bound.  The implemented selector uses the same
row discrepancies after removing at most three guarded coordinates and
adding the fixed postcharge numerator shift.

The existing finite postcharge-density theorem is stronger than its usual
endpoint-slack specialization: its reserve parameter is only the requested
upper bound.  Taking that parameter to be a fixed constant divided by `L`
and using `L^2 = o(n^deltaStar)` gives a uniform guarded density
`O(1 / L^2)`.  The guarded pools are subsets of the raw pools, so the
existing global `4n/p` valuation census then gives the strict paper rate.

Finally, the guarded-minus-raw defect is bounded by the sum of the two
aggregate corrections.  This avoids imposing a separate cross-moment
estimate.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- Constant in the uniform guarded postcharge density bound. -/
def roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  16 *
      (3 * roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta +
        roughCanonicalBalancedGuardNumeratorConstant W K0 c beta) /
    roughCanonicalRawBroadPoolDensity W

theorem roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant_pos
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <
      roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        W K0 c beta := by
  unfold roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
  have hC :=
    roughCanonicalSharpUnifiedRowScaleConstant_nonneg
      W K0 (beta := beta) hc
  have hG :=
    roughCanonicalBalancedGuardNumeratorConstant_pos
      W K0 (beta := beta) hc
  exact div_pos (mul_pos (by norm_num) (by positivity))
    (roughCanonicalRawBroadPoolDensity_pos W)

private theorem guardedPostchargeRate_L_sq_div_rpow_tendsto_zero
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => L n ^ 2 / (n : Real) ^ deltaStar)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real =>
        Real.log x ^ (2 : Real) / x ^ deltaStar)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : Real) hdelta).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : Nat =>
      Real.log (n : Real) ^ (2 : Real) / (n : Real) ^ deltaStar)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

private theorem guardedPostchargeRate_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- The balanced guarded postcharge density has a uniform
`constant/(4 L^2)` bound on every active attained row. -/
theorem
    eventually_roughCanonicalUniformGuardedPostchargeCorrectionDensityBound
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n
        (upperTailLength c n) (K0 + 1) deltaStar,
        abs
          (R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n)) <=
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
              W K0 c beta /
            (4 * L n ^ 2) := by
  let d := roughCanonicalRawBroadPoolDensity W
  let C := roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta
  let G := roughCanonicalBalancedGuardNumeratorConstant W K0 c beta
  let D :=
    roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
      W K0 c beta
  have hd : 0 < d := by
    dsimp only [d]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have hdensity_ne : roughCanonicalRawBroadPoolDensity W ≠ 0 :=
    (roughCanonicalRawBroadPoolDensity_pos W).ne'
  have hC : 0 <= C := by
    dsimp only [C]
    exact
      roughCanonicalSharpUnifiedRowScaleConstant_nonneg
        W K0 (beta := beta) hc
  have hG : 0 < G := by
    dsimp only [G]
    exact
      roughCanonicalBalancedGuardNumeratorConstant_pos
        W K0 (beta := beta) hc
  have hA : 0 < 3 * C + G := by positivity
  have hD : 0 < D := by
    dsimp only [D]
    exact
      roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant_pos
        W K0 (beta := beta) hc
  have hraw :=
    Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
      W K0 (beta := beta) hc hdelta
  have hlinear :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W (K0 + 1) hc hdelta
  have hLOne : ∀ᶠ n : Nat in atTop, 1 <= L n := by
    have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact hLTop.eventually (eventually_ge_atTop 1)
  have hratio : ∀ᶠ n : Nat in atTop,
      L n ^ 2 / (n : Real) ^ deltaStar < 1 / 4 :=
    (guardedPostchargeRate_L_sq_div_rpow_tendsto_zero hdelta).eventually
      (eventually_lt_nhds (by norm_num : (0 : Real) < 1 / 4))
  have hpower : ∀ᶠ n : Nat in atTop,
      max 4 (24 / d) <= (n : Real) ^ deltaStar :=
    (guardedPostchargeRate_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop (max 4 (24 / d)))
  filter_upwards [eventually_ge_atTop 2, hraw, hlinear, hLOne,
      hratio, hpower]
      with n hn hrawN hlinearN hLone hratioN hpowerN
  intro depth R certificate hnCutoff hyCutoff label hlabel
  have hlabelParts :=
    mem_roughCanonicalActiveRawCorrectionLabels.mp hlabel
  let row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
    ⟨label, hlabelParts.1⟩
  have hlabelData : IsCompleteRoughLabel (yNat n) label := by
    simpa only [row] using
      (isCompleteRoughLabel_of_canonicalCompleteRoughRow row)
  have hlabelPos : 0 < label := hlabelData.1
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hlabelReal : (0 : Real) < (label : Real) := by
    exact_mod_cast hlabelPos
  have hpowPos : (0 : Real) < (n : Real) ^ deltaStar :=
    Real.rpow_pos_of_pos hnReal deltaStar
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  let X : Real := ((n / label : Nat) : Real)
  have hnatUpper :
      (n : Real) / (label : Real) < X + 1 := by
    apply (div_lt_iff₀ hlabelReal).2
    have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
      (Nat.lt_succ_self (n / label))
    dsimp only [X]
    exact_mod_cast hnat
  have hactiveHalf :
      (n : Real) ^ deltaStar / 2 <=
        (n : Real) / (label : Real) := by
    calc
      (n : Real) ^ deltaStar / 2 <=
          (2 * (n : Real) / (label : Real)) / 2 :=
        div_le_div_of_nonneg_right hlabelParts.2.2 (by norm_num)
      _ = (n : Real) / (label : Real) := by ring
  have hpowerFour : (4 : Real) <= (n : Real) ^ deltaStar :=
    (le_max_left 4 (24 / d)).trans hpowerN
  have hXlower :
      (n : Real) ^ deltaStar / 4 <= X := by
    have hhalfFour :
        (n : Real) ^ deltaStar / 4 <=
          (n : Real) ^ deltaStar / 2 - 1 := by
      linarith
    linarith
  have hLsq :
      L n ^ 2 <= X := by
    have hlogSmall :
        L n ^ 2 < (n : Real) ^ deltaStar / 4 := by
      have hcross := (div_lt_iff₀ hpowPos).mp hratioN
      nlinarith
    exact (hlogSmall.trans_le hXlower).le
  have hpowerDensity :
      24 / d <= (n : Real) ^ deltaStar :=
    (le_max_right 4 (24 / d)).trans hpowerN
  have hsix : 6 <= d * X := by
    have hcross := (div_le_iff₀ hd).mp hpowerDensity
    have hmul := mul_le_mul_of_nonneg_left hXlower hd.le
    nlinarith
  have hrawPool :
      d * X <=
        ((roughCanonicalBroadCorrectionPool W n
          (upperTailLength c n) (K0 + 1) (yNat n) label).card : Real) := by
    dsimp only [d, X]
    exact hlinearN label hlabelData hlabelParts.2
  have hrawQuota := hrawN row (by simpa only [row] using hlabelParts.2)
  let targetReserve : Real := D / (4 * L n)
  have htargetReserve : 0 < targetReserve := by
    dsimp only [targetReserve]
    exact div_pos hD (mul_pos (by norm_num) hL)
  have hfirst :
      12 * C <= d * targetReserve * L n := by
    have hbase : 12 * C <= 4 * (3 * C + G) := by
      nlinarith [hG.le]
    calc
      12 * C <= 4 * (3 * C + G) := hbase
      _ = d * targetReserve * L n := by
        dsimp only [targetReserve, D]
        unfold
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        dsimp only [d, C, G]
        field_simp [hdensity_ne, hL.ne']
        ring
  have hsecond :
      4 * (3 * C + G) * L n <=
        d * targetReserve * X := by
    have hcoef : 0 <= 4 * (3 * C + G) / L n := by positivity
    calc
      4 * (3 * C + G) * L n =
          (4 * (3 * C + G) / L n) * L n ^ 2 := by
        field_simp [hL.ne']
      _ <= (4 * (3 * C + G) / L n) * X :=
        mul_le_mul_of_nonneg_left hLsq hcoef
      _ = d * targetReserve * X := by
        dsimp only [targetReserve, D]
        unfold
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        dsimp only [d, C, G]
        field_simp [hdensity_ne, hL.ne']
        ring
  have hdensity :=
    R.roughCanonicalBalancedGuardedPostchargeCorrectionDensity_abs_le_reserve
      certificate row hc hn hLone hnCutoff hyCutoff hlabelParts.2
      hd htargetReserve hC (by rfl) hrawQuota
      (by simpa only [X] using hrawPool)
      (by simpa only [X] using hsix)
      hfirst hsecond
  have htarget :
      targetReserve / L n = D / (4 * L n ^ 2) := by
    dsimp only [targetReserve]
    field_simp [hL.ne']
  simpa only [row, D, htarget] using hdensity

/-- Guarded active pools are subpools of the raw active pools, so their
total valuation obeys the same `4n/p` census. -/
theorem
    sum_activeGuardedPostchargeCorrectionPool_factorization_le_four_mul_div_prime
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) {p : Nat} (hp : p.Prime) :
    (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
        (upperTailLength c n) K deltaStar,
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K label,
        (a.factorization p : Real)) <=
      4 * (n : Real) / (p : Real) := by
  calc
    (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
        (upperTailLength c n) K deltaStar,
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K label,
        (a.factorization p : Real)) <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        ∑ a ∈ roughCanonicalBroadCorrectionPool W n
            (upperTailLength c n) K (yNat n) label,
          (a.factorization p : Real) := by
      apply Finset.sum_le_sum
      intro label _hlabel
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar W K label)
        (fun (a : Nat) _ha _hnew =>
          Nat.cast_nonneg (a.factorization p))
    _ <= 4 * (n : Real) / (p : Real) :=
      sum_activeRawCorrectionPool_factorization_le_four_mul_div_prime
        W n (upperTailLength c n) K deltaStar hp

/-- A uniform absolute guarded density bound and the preceding valuation
census bound the whole implemented aggregate correction. -/
theorem
    abs_roughCanonicalAggregateGuardedPostchargeRowCorrection_le_uniformDensity
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell densityBound : Real)
    (hp : p.Prime) (hdensityBound : 0 <= densityBound)
    (hdensity :
      ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        abs
          (R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta ell) <= densityBound) :
    abs
      (R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
        deltaStar W K alpha beta ell p) <=
      densityBound * (4 * (n : Real) / (p : Real)) := by
  unfold roughCanonicalAggregateGuardedPostchargeRowCorrection
  calc
    abs
        (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
            (upperTailLength c n) K deltaStar,
          R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar W K label alpha beta ell *
            ∑ a ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar W K label,
              (a.factorization p : Real)) <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        abs
          (R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta ell) *
          (∑ a ∈
              R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar W K label,
            (a.factorization p : Real)) := by
      calc
        abs (∑ label ∈ _, _ * _) <=
            ∑ label ∈ _, abs (_ * _) :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro label _hlabel
          rw [abs_mul, abs_of_nonneg (by positivity :
            0 <=
              ∑ a ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar W K label,
                (a.factorization p : Real))]
    _ <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        densityBound *
          (∑ a ∈
              R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar W K label,
            (a.factorization p : Real)) := by
      apply Finset.sum_le_sum
      intro label hlabel
      exact mul_le_mul_of_nonneg_right (hdensity label hlabel) (by positivity)
    _ = densityBound *
        (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
            (upperTailLength c n) K deltaStar,
          ∑ a ∈
              R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar W K label,
            (a.factorization p : Real)) := by
      rw [Finset.mul_sum]
    _ <= densityBound * (4 * (n : Real) / (p : Real)) :=
      mul_le_mul_of_nonneg_left
        (R.sum_activeGuardedPostchargeCorrectionPool_factorization_le_four_mul_div_prime
          certificate deltaStar hp)
        hdensityBound

/-- The implemented guarded aggregate correction has the strict paper
rate, uniformly in the realization, certificate, and prime. -/
theorem
    eventually_abs_roughCanonicalAggregateGuardedPostchargeRowCorrection_le_strictScale
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      forall p : Nat, p.Prime ->
        abs
          (R.roughCanonicalAggregateGuardedPostchargeRowCorrection
            certificate deltaStar W (K0 + 1)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) p) <=
          roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
              W K0 c beta *
            secondOrderScale n / ((p : Real) * L n) := by
  have hdensity :=
    eventually_roughCanonicalUniformGuardedPostchargeCorrectionDensityBound
      W K0 (beta := beta) hc hdelta
  let D :=
    roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
      W K0 c beta
  have hD : 0 <= D := by
    exact
      (roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant_pos
        W K0 (beta := beta) hc).le
  filter_upwards [eventually_gt_atTop 1, hdensity]
      with n hn hdensityN
  intro depth R certificate hnCutoff hyCutoff p hp
  have hbound :=
    R.abs_roughCanonicalAggregateGuardedPostchargeRowCorrection_le_uniformDensity
      (W := W) (K := K0 + 1) (p := p)
      certificate deltaStar
      (roughHeadBalancedAlpha W n (upperTailLength c n)
        (K0 + 1) beta (L n))
      beta (L n) (D / (4 * L n ^ 2)) hp
      (div_nonneg hD
        (mul_nonneg (by norm_num) (sq_nonneg (L n))))
      (hdensityN depth R certificate hnCutoff hyCutoff)
  have hpReal : (0 : Real) < (p : Real) := by
    exact_mod_cast hp.pos
  have hL : 0 < L n := L_pos hn
  calc
    abs
        (R.roughCanonicalAggregateGuardedPostchargeRowCorrection
          certificate deltaStar W (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n)
            (K0 + 1) beta (L n))
          beta (L n) p) <=
      (D / (4 * L n ^ 2)) *
        (4 * (n : Real) / (p : Real)) := hbound
    _ = D * secondOrderScale n / ((p : Real) * L n) := by
      unfold secondOrderScale Erdos390.Full.Scale.L
      field_simp [hpReal.ne', hL.ne']

/-- Consequently the literal guarded-minus-raw correction defect has the
strict paper rate.  No cross-moment premise remains. -/
theorem
    eventually_abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_strictScale
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
      forall p : Nat, p.Prime ->
        abs
          (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
            certificate deltaStar W (K0 + 1)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) p) <=
          (roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
              W K0 c beta +
            roughCanonicalUniformRawRowCorrectionDensityConstant
              W K0 c beta) *
            secondOrderScale n / ((p : Real) * L n) := by
  have hguarded :=
    eventually_abs_roughCanonicalAggregateGuardedPostchargeRowCorrection_le_strictScale
      W K0 (beta := beta) hc hdelta
  have hraw :=
    eventually_roughCanonicalAggregateRawRowCorrectionBound_strictScale
      W K0 (beta := beta) hc hdelta
  filter_upwards [hguarded, hraw] with n hguardedN hrawN
  intro depth R certificate hnCutoff hyCutoff p hp
  have hguardedBound :=
    hguardedN depth R certificate hnCutoff hyCutoff p hp
  have hrawBound := hrawN p hp
  unfold RoughCanonicalAggregateRawRowCorrectionBound at hrawBound
  unfold roughCanonicalAggregateGuardedRawCorrectionValuationDefect
  calc
    abs
        (R.roughCanonicalAggregateGuardedPostchargeRowCorrection
            certificate deltaStar W (K0 + 1)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) p -
          roughCanonicalAggregateRawRowCorrection W n
            (upperTailLength c n) (K0 + 1) deltaStar
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) p) <=
      abs
          (R.roughCanonicalAggregateGuardedPostchargeRowCorrection
            certificate deltaStar W (K0 + 1)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) p) +
        abs
          (roughCanonicalAggregateRawRowCorrection W n
            (upperTailLength c n) (K0 + 1) deltaStar
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) p) :=
      abs_sub _ _
    _ <=
      roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
            W K0 c beta *
          secondOrderScale n / ((p : Real) * L n) +
        roughCanonicalUniformRawRowCorrectionDensityConstant W K0 c beta *
          secondOrderScale n / ((p : Real) * L n) :=
      add_le_add hguardedBound hrawBound
    _ =
      (roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
            W K0 c beta +
          roughCanonicalUniformRawRowCorrectionDensityConstant W K0 c beta) *
        secondOrderScale n / ((p : Real) * L n) := by ring

end BankPaperRealization

end

end Erdos390.WholePaper
