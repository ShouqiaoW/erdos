import Erdos390.Full.PaperRawPrefixValuationRow
import Erdos390.Full.PaperRawPrefixThirdCumulantRow
import Erdos390.Full.PaperRawTiltTaylorRate

/-!
# The raw tilted full-valuation moving-prefix row

This file closes the finite Taylor argument for the nuisance marked rows.
All inputs to the Taylor lemma are discharged from the structured-cell
census, the un-tilted prefix theorem, and the third-cumulant theorem.  The
only scale separation retained in the terminal statement is the transparent
fixed-box condition `2 B ≤ log W`, which makes the valuation score pointwise
at most one.  The resulting row coefficient remains `o(1 / log L)`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimeSums ValuationScoreDomination ValuationTiltCell
open PaperScaleMarkedCell FullTiltPairChamber
open PaperRawPrefixValuationRow PaperRawPrefixThirdCumulantRow

noncomputable section

namespace PaperRawTiltedPrefixRow

/-- The first absolute score-moment parameter appearing in the finite
Taylor ledger. -/
def rawTiltSmallParameter (B c : ℝ) (W n : ℕ) : ℝ :=
  (B / L n) * ((2 / c) * bandReciprocalSum n W)

/-- For a fixed box and fixed positive cell-density lower bound, the Taylor
smallness parameter tends to zero.  This statement is uniform in all
coefficients in the box because it only contains the box radius `B`. -/
theorem tendsto_rawTiltSmallParameter_zero
    (B c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    Tendsto (rawTiltSmallParameter B c W) atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦ Real.log (L n) / L n)
      atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto
      (fun n : ℕ ↦ (24 * B / c) * (Real.log (L n) / L n))
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hratio
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ rawTiltSmallParameter B c W n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    unfold rawTiltSmallParameter bandReciprocalSum
    have hL : 0 < L n := L_pos hn
    positivity
  have hle : ∀ᶠ n : ℕ in atTop,
      rawTiltSmallParameter B c W n ≤
        (24 * B / c) * (Real.log (L n) / L n) := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      Filter.eventually_gt_atTop 1] with n hband hn
    have hL : 0 < L n := L_pos hn
    have hcoef : 0 ≤ (B / L n) * (2 / c) := by positivity
    unfold rawTiltSmallParameter
    calc
      (B / L n) * ((2 / c) * bandReciprocalSum n W) =
          ((B / L n) * (2 / c)) * bandReciprocalSum n W := by ring
      _ ≤ ((B / L n) * (2 / c)) * (12 * Real.log (L n)) :=
        mul_le_mul_of_nonneg_left hband hcoef
      _ = (24 * B / c) * (Real.log (L n) / L n) := by ring
  exact squeeze_zero' hnonneg hle hmajor

/-- In particular, the exact hypothesis used by the finite Taylor theorem
holds eventually. -/
theorem eventually_two_rawTiltSmallParameter_le_half
    (B c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * rawTiltSmallParameter B c W n ≤ (1 : ℝ) / 2 := by
  have hzero := tendsto_rawTiltSmallParameter_zero B c W hB hc
  filter_upwards [hzero.eventually (Iio_mem_nhds
      (show (0 : ℝ) < 1 / 4 by norm_num))] with n hn
  linarith

/-- The complete raw tilted moving-prefix row.  The coefficient `epsilon`
is chosen before `n`, the moving band prime, the prefix endpoint, and the
coefficient vector.  Its sharp weighted rate is part of the conclusion. -/
theorem exists_uniform_rawCell_tilted_valuation_prefix_rate
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hboxW : 2 * B ≤ Real.log (W : ℝ)) :
    ∃ epsilon : ℕ → ℝ,
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → physicalBound A n < k →
        k ≤ physicalBound C n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) := by
  let c : ℝ := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  obtain ⟨K₀, hK₀, G₀, hG₀, Nbase, hbase⟩ :=
    exists_uniform_rawCell_valuation_prefix_bound
      H hA hAC hC W hW hHeadLe
  obtain ⟨G₃, hG₃, Nthird, hthird⟩ :=
    exists_uniform_rawCell_valuationScore_thirdCumulant_bound
      H hA hAC hC
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let epsilonZero : ℕ → ℝ :=
    rawValuationPrefixRateMajorant K₀ G₀ W
  let epsilonThird : ℕ → ℝ :=
    rawThirdCumulantRateMajorant B G₃
  let nonlinear : ℕ → ℝ :=
    rawTiltNonlinearRateMajorant B c
  let epsilon : ℕ → ℝ := fun n ↦
    epsilonZero n + epsilonThird n + nonlinear n
  have hepsilon : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    exact tendsto_sum_three_mul_logL_zero
      epsilonZero epsilonThird nonlinear
      (tendsto_rawValuationPrefixRateMajorant_mul_logL_zero
        K₀ G₀ W hG₀.le hW)
      (tendsto_rawThirdCumulantRateMajorant_mul_logL_zero B G₃)
      (tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero B c)
  have hbaseRate :=
    eventually_rawValuationPrefix_rowCoefficient_le
      K₀ G₀ W hG₀.le hW
  have hthirdRate :=
    eventually_rawThirdCumulantCoefficient_le B G₃ W hB hG₃.le
  have hnonlinearRate :=
    eventually_rawTiltNonlinear_row_le B c W hB hc
  have hsmall :=
    eventually_two_rawTiltSmallParameter_le_half B c W hB hc
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hCevent : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop C)
  have hInvCevent : ∀ᶠ n : ℕ in atTop, 1 / C ≤ (n : ℝ) :=
    hcastTop.eventually (eventually_ge_atTop (1 / C))
  have hAll : ∀ᶠ n : ℕ in atTop,
      (∀ p ∈ primeBand n W,
        (p : ℝ) *
            ((2 * K₀ / L n) * (1 / (p : ℝ)) +
              (4 * G₀ *
                  (PaperPrimePowerTailLedger.cutoffScale W * L n) ^ 2) /
                ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) ≤
          epsilonZero n) ∧
      ((B / L n) *
          ((8 * G₃ + 16 * G₃ ^ 2) * bandReciprocalSum n W +
            2 * G₃ *
              PrimePowerTaylorLedger.positivePrimePowerLcmConstant) ≤
        epsilonThird n) ∧
      (∀ p : ℕ, 0 < p →
        let Hsum := bandReciprocalSum n W
        let a := (B / L n) * ((2 / c) * Hsum)
        let MF := 2 / (c * (p : ℝ))
        let RFone := (B / L n) * (1 / c) *
          ((4 * Hsum +
              PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
            (p : ℝ))
        (p : ℝ) * (128 * (RFone + MF * a)) ≤ nonlinear n) ∧
      2 * rawTiltSmallParameter B c W n ≤ (1 : ℝ) / 2 ∧
      C ≤ (n : ℝ) ∧ 1 / C ≤ (n : ℝ) ∧ 2 < n := by
    filter_upwards [hbaseRate, hthirdRate, hnonlinearRate, hsmall,
      hCevent, hInvCevent, Filter.eventually_gt_atTop 2] with
      n hbaseRateN hthirdRateN hnonlinearRateN hsmallN hCn hInvCn hn
    exact ⟨hbaseRateN, hthirdRateN, hnonlinearRateN, hsmallN,
      hCn, hInvCn, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨epsilon, hepsilon, max Nbase (max Nthird (max Ndensity Nevent)), ?_⟩
  intro n k p eta hN hlow hhigh hpBand heta
  have hNbase : Nbase ≤ n := by omega
  have hNthird : Nthird ≤ n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNevent' : Nevent ≤ n := by omega
  obtain ⟨hbaseRateN, hthirdRateN, hnonlinearRateN, hsmallN,
    hCn, hInvCn, hn⟩ := hNevent n hNevent'
  have hnpos : 0 < n := by omega
  have hL : 0 < L n := L_pos (by omega)
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let M := physicalBound C n
  let S := structuredCell H (physicalBound A n) M (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  have hMcast : (M : ℝ) ≤ C * (n : ℝ) := by
    dsimp only [M]
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hC.le (by positivity))
  have hMlower : 1 ≤ M := by
    dsimp only [M]
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have hraw := (div_le_iff₀ hC).mp hInvCn
      simpa only [one_mul, mul_comm] using hraw
    exact_mod_cast hOne
  have hMpos : 0 < M := Nat.zero_lt_of_lt hMlower
  have hcard : c * (M : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (M : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hC.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S, M] using hdensity hNdensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ M := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  have hprime : ∀ q ∈ primeBand n W, q.Prime := by
    intro q hq
    exact prime_of_mem_primeBand hq
  have hpW : ∀ q ∈ primeBand n W, W ≤ q := by
    intro q hq
    exact (cutoff_lt_of_mem_primeBand hq).le
  have hCnSq : C * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hlogM : Real.log (M : ℝ) ≤ 2 * L n := by
    have hMleSq : (M : ℝ) ≤ (n : ℝ) ^ 2 :=
      hMcast.trans hCnSq
    have hraw := Real.log_le_log (by exact_mod_cast hMpos) hMleSq
    rw [Real.log_pow] at hraw
    simpa [L] using hraw
  have hscore : ∀ m : S,
      |valuationScore (primeBand n W) eta (L n) (m : ℕ)| ≤ 1 := by
    intro m
    have hmpos : 0 < (m : ℕ) := hSpos m m.property
    have hmM : (m : ℕ) ≤ M := hSle m m.property
    have hraw := abs_valuationScore_le_log_ratio
      (primeBand n W) eta hmpos hmM hW hpW hB hL heta
    calc
      |valuationScore (primeBand n W) eta (L n) (m : ℕ)| ≤
          (B / L n) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := hraw
      _ ≤ (B / L n) * ((2 * L n) / Real.log (W : ℝ)) := by
        gcongr
      _ = (2 * B) / Real.log (W : ℝ) := by
        field_simp [hL.ne', hlogW.ne']
      _ ≤ 1 := by
        exact (div_le_iff₀ hlogW).2 (by simpa using hboxW)
  let Czero : ℝ :=
    (2 * K₀ / L n) * (1 / (p : ℝ)) +
      (4 * G₀ * (PaperPrimePowerTailLedger.cutoffScale W * L n) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)
  let Cthird : ℝ :=
    (B / L n) *
      (((8 * G₃ + 16 * G₃ ^ 2) * bandReciprocalSum n W +
        2 * G₃ * PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
          (p : ℝ))
  let a : ℝ := rawTiltSmallParameter B c W n
  let MF : ℝ := 2 / (c * (p : ℝ))
  let RFone : ℝ := (B / L n) * (1 / c) *
    ((4 * bandReciprocalSum n W +
      PrimePowerTaylorLedger.positivePrimePowerLcmConstant) / (p : ℝ))
  have ha : 0 ≤ a := by
    dsimp only [a, rawTiltSmallParameter, bandReciprocalSum]
    positivity
  have ha1 : a ≤ 1 := by
    dsimp only [a] at hsmallN ⊢
    linarith
  have hMF : 0 ≤ MF := by dsimp only [MF]; positivity
  have hRFone : 0 ≤ RFone := by
    dsimp only [RFone, bandReciprocalSum]
    have hconst :=
      PrimePowerTaylorLedger.positivePrimePowerLcmConstant_pos
    positivity
  have hCzero : 0 ≤ Czero := by
    dsimp only [Czero]
    positivity
  have hCthird : 0 ≤ Cthird := by
    dsimp only [Cthird, bandReciprocalSum]
    have hconst :=
      PrimePowerTaylorLedger.positivePrimePowerLcmConstant_pos
    positivity
  have hbaseN :
      |(uniformOnFinset S hS).covariance
          (fun m : S ↦ (valuation p (m : ℕ) : ℝ))
          (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤ Czero := by
    simpa only [S, M, Czero] using
      hbase hNbase hlow hhigh hpBand hS
  have hthirdN :
      |(uniformOnFinset S hS).covarianceThirdCentered
          (fun m : S ↦ (valuation p (m : ℕ) : ℝ))
          (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))| ≤ Cthird := by
    simpa only [S, M, Cthird, bandReciprocalSum] using
      hthird eta hNthird hpBand hB heta hS
  have hTaylor :=
    uniformOnFinset_exponentialTilt_covariance_valuation_prefix_le
      S (primeBand n W) hS eta hpBand hMpos hB hL hc
      hCzero hCthird hcard hSpos hSle hprime heta hscore
      (by simpa only [a, rawTiltSmallParameter] using hsmallN)
      hbaseN hthirdN
  have hzeroRow : Czero ≤ epsilonZero n / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [Czero, epsilonZero, mul_comm] using
      hbaseRateN p hpBand
  have hthirdRow : Cthird ≤ epsilonThird n / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    calc
      Cthird * (p : ℝ) =
          (B / L n) *
            ((8 * G₃ + 16 * G₃ ^ 2) * bandReciprocalSum n W +
              2 * G₃ *
                PrimePowerTaylorLedger.positivePrimePowerLcmConstant) := by
        dsimp only [Cthird]
        field_simp [hpR.ne']
      _ ≤ epsilonThird n := by
        simpa only [epsilonThird] using hthirdRateN
  have hnonlinearRow :
      (p : ℝ) * (128 * (RFone + MF * a)) ≤ nonlinear n := by
    simpa only [a, MF, RFone, nonlinear, rawTiltSmallParameter] using
      hnonlinearRateN p hp.pos
  have hpoly :
      rawTiltPrefixTaylorBound a MF RFone Czero Cthird ≤
        epsilon n / (p : ℝ) := by
    simpa only [epsilon] using rawTiltPrefixTaylorBound_le_row
      hp.pos ha ha1 hMF hRFone hzeroRow hthirdRow hnonlinearRow
  exact hTaylor.trans (by
    simpa only [a, MF, RFone, bandReciprocalSum] using hpoly)

/-- All-prefix form of the preceding theorem.  Prefixes outside the physical
cell are constant zero or constant one, so their covariance vanishes
identically.  Taking the absolute value of the rate makes its nonnegativity
literal for every `n` without changing the sharp asymptotic rate. -/
theorem exists_uniform_rawCell_tilted_valuation_all_prefix_rate
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W)
    (hboxW : 2 * B ≤ Real.log (W : ℝ)) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n k p : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        (∀ q ∈ primeBand n W, |eta q| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦
                  valuationScore (primeBand n W) eta (L n) (m : ℕ))).covariance
              (fun m : S ↦ valuation p (m : ℕ))
              (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
            epsilon n / (p : ℝ) := by
  obtain ⟨epsilon₀, hepsilon₀, N₀, hprefix⟩ :=
    exists_uniform_rawCell_tilted_valuation_prefix_rate
      H hA hAC hC B W hB hW hHeadLe hboxW
  let epsilon : ℕ → ℝ := fun n ↦ |epsilon₀ n|
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) :=
    (hLTop.eventually (eventually_ge_atTop 1)).mono fun n hn ↦
      Real.log_nonneg hn
  have hepsilon : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have habs := hepsilon₀.abs
    have habs' : Tendsto (fun n : ℕ ↦
        |epsilon₀ n * Real.log (L n)|) atTop (nhds 0) := by
      simpa only [abs_zero] using habs
    apply habs'.congr'
    filter_upwards [hlog0] with n hn
    dsimp only [epsilon]
    rw [abs_mul, abs_of_nonneg hn]
  refine ⟨epsilon, fun n ↦ abs_nonneg _, hepsilon, N₀, ?_⟩
  intro n k p eta hN hpBand heta
  let S := structuredCell H (physicalBound A n) (physicalBound C n)
    (yNat n)
  change ∀ hS : S.Nonempty, _
  intro hS
  let mu := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore (primeBand n W) eta (L n) (m : ℕ))
  let V : S → ℝ := fun m ↦ valuation p (m : ℕ)
  have hp := prime_of_mem_primeBand hpBand
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hepsilonLe : epsilon₀ n / (p : ℝ) ≤
      epsilon n / (p : ℝ) := by
    exact div_le_div_of_nonneg_right (le_abs_self (epsilon₀ n)) hpR.le
  by_cases hlow : physicalBound A n < k
  · by_cases hhigh : k ≤ physicalBound C n
    · simpa only [S, mu, V] using
        (hprefix eta hN hlow hhigh hpBand heta hS).trans hepsilonLe
    · have hconst :
          (fun m : S ↦ if (m : ℕ) ≤ k then (1 : ℝ) else 0) =
            fun _ ↦ 1 := by
        funext m
        have hmC : (m : ℕ) ≤ physicalBound C n :=
          (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
        have hCk : physicalBound C n ≤ k :=
          (Nat.lt_of_not_ge hhigh).le
        rw [if_pos (hmC.trans hCk)]
      rw [hconst]
      have hcov : mu.covariance V (fun _ ↦ 1) = 0 := by
        calc
          mu.covariance V (fun _ ↦ 1) =
              mu.covariance V (fun _ ↦ 0) := by
            simpa using
              (mu.covariance_sub_const_right V (fun _ ↦ 0) (-1))
          _ = 0 := mu.covariance_zero_right V
      rw [hcov, abs_zero]
      exact div_nonneg (abs_nonneg _) hpR.le
  · have hconst :
        (fun m : S ↦ if (m : ℕ) ≤ k then (1 : ℝ) else 0) =
          fun _ ↦ 0 := by
      funext m
      have hAm : physicalBound A n < (m : ℕ) :=
        (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).1
      have hkm : k < (m : ℕ) := (Nat.le_of_not_gt hlow).trans_lt hAm
      rw [if_neg (not_le_of_gt hkm)]
    rw [hconst, mu.covariance_zero_right, abs_zero]
    exact div_nonneg (abs_nonneg _) hpR.le

end PaperRawTiltedPrefixRow

end

end Erdos390.Full
