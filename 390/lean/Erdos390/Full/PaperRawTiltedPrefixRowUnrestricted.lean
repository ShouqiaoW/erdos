import Erdos390.Full.PaperRawTiltedPrefixRow
import Erdos390.Full.PaperBoundedScorePrefixCovariance

/-!
# Raw tilted moving-prefix row with an unrestricted fixed coefficient box

This is the parameter-order-safe form of the raw row.  `W` and the box
radius are arbitrary fixed parameters.  The score envelope
`2 B / log W` enters only through a fixed exponential constant; no relation
between the box radius and `W` is assumed.
-/

open Filter Topology

namespace Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimeSums ValuationScoreDomination ValuationTiltCell
open PaperScaleMarkedCell FullTiltPairChamber
open PaperRawPrefixValuationRow
open PaperRawTiltedPrefixRow

noncomputable section

set_option maxHeartbeats 1600000

/-- The raw moving-prefix terminal for arbitrary fixed `B,W`. -/
theorem exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
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
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let Kscore : ℝ := (2 * B) / Real.log (W : ℝ)
  let epsilonZero : ℕ → ℝ := rawValuationPrefixRateMajorant K₀ G₀ W
  let epsilonPerturb : ℕ → ℝ := fun n ↦
    Real.exp Kscore * rawTiltNonlinearRateMajorant B c n
  let epsilon : ℕ → ℝ := fun n ↦ epsilonZero n + epsilonPerturb n
  have hepsilonZero : Tendsto (fun n : ℕ ↦
      epsilonZero n * Real.log (L n)) atTop (nhds 0) :=
    tendsto_rawValuationPrefixRateMajorant_mul_logL_zero
      K₀ G₀ W hG₀.le hW
  have hepsilonPerturb : Tendsto (fun n : ℕ ↦
      epsilonPerturb n * Real.log (L n)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ Real.exp Kscore)
        atTop (nhds (Real.exp Kscore)) := tendsto_const_nhds
    have hrate := tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero B c
    have hmul := hconst.mul hrate
    simpa only [epsilonPerturb, mul_zero, mul_assoc] using hmul
  have hepsilon : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := hepsilonZero.add hepsilonPerturb
    simpa only [epsilon, add_mul, zero_add] using hsum
  have hbaseRate := eventually_rawValuationPrefix_rowCoefficient_le
    K₀ G₀ W hG₀.le hW
  have hnonlinearRate :=
    eventually_rawTiltNonlinear_row_le B c W hB hc
  have haT := tendsto_rawTiltSmallParameter_zero B c W hB hc
  have hEaT : Tendsto (fun n : ℕ ↦
      Real.exp Kscore * rawTiltSmallParameter B c W n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul haT
  have hsmallHalf : ∀ᶠ n : ℕ in atTop,
      Real.exp Kscore * rawTiltSmallParameter B c W n ≤
        (1 : ℝ) / 2 :=
    hEaT.eventually (eventually_le_nhds (by norm_num))
  have hsmallQuarter : ∀ᶠ n : ℕ in atTop,
      4 * Real.exp Kscore * rawTiltSmallParameter B c W n ≤ 1 := by
    filter_upwards [hEaT.eventually (eventually_le_nhds
      (by norm_num : (0 : ℝ) < 1 / 4))] with n hn
    linarith
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
      (∀ p : ℕ, 0 < p →
        let Hsum := bandReciprocalSum n W
        let a := (B / L n) * ((2 / c) * Hsum)
        let MF := 2 / (c * (p : ℝ))
        let RFone := (B / L n) * (1 / c) *
          ((4 * Hsum +
              PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
            (p : ℝ))
        (p : ℝ) * (128 * (RFone + MF * a)) ≤
          rawTiltNonlinearRateMajorant B c n) ∧
      Real.exp Kscore * rawTiltSmallParameter B c W n ≤ (1 : ℝ) / 2 ∧
      4 * Real.exp Kscore * rawTiltSmallParameter B c W n ≤ 1 ∧
      C ≤ (n : ℝ) ∧ 1 / C ≤ (n : ℝ) ∧ 2 < n := by
    filter_upwards [hbaseRate, hnonlinearRate, hsmallHalf, hsmallQuarter,
      hCevent, hInvCevent, Filter.eventually_gt_atTop 2] with
      n hbaseN hnonlinearN hhalfN hquarterN hCn hInvCn hn
    exact ⟨hbaseN, hnonlinearN, hhalfN, hquarterN, hCn, hInvCn, hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨epsilon, hepsilon, max Nbase (max Ndensity Nevent), ?_⟩
  intro n k p eta hN hlow hhigh hpBand heta
  have hNbase : Nbase ≤ n := by omega
  have hNdensity : Ndensity ≤ n := by omega
  have hNevent' : Nevent ≤ n := by omega
  obtain ⟨hbaseRateN, hnonlinearRateN, hhalfN, hquarterN,
    hCn, hInvCn, hn⟩ := hNevent n hNevent'
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
    have hMleSq : (M : ℝ) ≤ (n : ℝ) ^ 2 := hMcast.trans hCnSq
    have hraw := Real.log_le_log (by exact_mod_cast hMpos) hMleSq
    rw [Real.log_pow] at hraw
    simpa [L] using hraw
  have hscore : ∀ m : S,
      |valuationScore (primeBand n W) eta (L n) (m : ℕ)| ≤ Kscore := by
    intro m
    have hraw := abs_valuationScore_le_log_ratio
      (primeBand n W) eta (hSpos m m.property) (hSle m m.property)
      hW hpW hB hL heta
    calc
      |valuationScore (primeBand n W) eta (L n) (m : ℕ)| ≤
          (B / L n) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := hraw
      _ ≤ (B / L n) * ((2 * L n) / Real.log (W : ℝ)) := by
        gcongr
      _ = Kscore := by
        dsimp only [Kscore]
        field_simp [hL.ne', hlogW.ne']
  let mu := uniformOnFinset S hS
  let score : S → ℝ := fun m ↦
    valuationScore (primeBand n W) eta (L n) (m : ℕ)
  let F : S → ℝ := fun m ↦ (valuation p (m : ℕ) : ℝ)
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  let Czero : ℝ :=
    (2 * K₀ / L n) * (1 / (p : ℝ)) +
      (4 * G₀ * (PaperPrimePowerTailLedger.cutoffScale W * L n) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)
  let a : ℝ := rawTiltSmallParameter B c W n
  let MF : ℝ := 2 / (c * (p : ℝ))
  let RFone : ℝ := (B / L n) * (1 / c) *
    ((4 * bandReciprocalSum n W +
      PrimePowerTaylorLedger.positivePrimePowerLcmConstant) / (p : ℝ))
  let X : ℝ := RFone + MF * a
  let DF : ℝ := 2 * Real.exp Kscore * X
  let DG : ℝ := 4 * Real.exp Kscore * a
  have ha0 : 0 ≤ a := by
    dsimp only [a, rawTiltSmallParameter, bandReciprocalSum]
    positivity
  have hMF0 : 0 ≤ MF := by dsimp only [MF]; positivity
  have hRF0 : 0 ≤ RFone := by
    dsimp only [RFone, bandReciprocalSum]
    have hconst := PrimePowerTaylorLedger.positivePrimePowerLcmConstant_pos
    positivity
  have hX0 : 0 ≤ X := by dsimp only [X]; positivity
  have hDF0 : 0 ≤ DF := by dsimp only [DF]; positivity
  have hDG0 : 0 ≤ DG := by dsimp only [DG]; positivity
  have hDG1 : DG ≤ 1 := by
    simpa only [DG, a] using hquarterN
  have hF0 : ∀ m, 0 ≤ F m := by
    intro m
    exact valuation_nonneg p (m : ℕ)
  have hpref0 : ∀ m, 0 ≤ pref m := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hpref1 : ∀ m, pref m ≤ 1 := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have habsScore : mu.expect (fun m ↦ |score m|) ≤ a := by
    dsimp only [mu, score, a, rawTiltSmallParameter]
    exact uniformOnFinset_expect_abs_valuationScore_reciprocal_le
      S (primeBand n W) hS eta hMpos hB hL hc hcard hSpos hSle
        hprime heta
  have hmeanF : mu.expect F ≤ MF := by
    dsimp only [mu, F, MF]
    exact uniformOnFinset_expect_valuation_reciprocal_le
      S hS hp hMpos hc hcard hSpos hSle
  have hmarkedF : mu.expect (fun m ↦ F m * |score m|) ≤ RFone := by
    have hraw :=
      uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_reciprocal_le
        S (primeBand n W) hS eta hpBand hMpos hB hL hc hcard
          hSpos hSle hprime heta
    simpa only [mu, F, score, abs_of_nonneg (hF0 _), RFone] using hraw
  have hbaseN : |mu.covariance F pref| ≤ Czero := by
    simpa only [mu, F, pref, S, M, Czero] using
      hbase hNbase hlow hhigh hpBand hS
  have hdiff : |(mu.exponentialTilt score).covariance F pref -
      mu.covariance F pref| ≤ DF + (MF + DF) * DG + DF := by
    have hraw :=
      mu.abs_exponentialTilt_covariance_prefix_sub_covariance_le_of_bounded_score
        F pref score hF0 hpref0 hpref1
          (by simpa only [score] using hscore) ha0 hMF0 hRF0
          (by simpa only [a] using hhalfN) habsScore hmeanF hmarkedF
    simpa only [DF, DG, X] using hraw
  have htilt : |(mu.exponentialTilt score).covariance F pref| ≤
      Czero + (DF + (MF + DF) * DG + DF) := by
    calc
      |(mu.exponentialTilt score).covariance F pref| =
          |mu.covariance F pref +
            ((mu.exponentialTilt score).covariance F pref -
              mu.covariance F pref)| := by
                congr 1
                ring
      _ ≤ |mu.covariance F pref| +
          |(mu.exponentialTilt score).covariance F pref -
            mu.covariance F pref| := abs_add_le _ _
      _ ≤ Czero + (DF + (MF + DF) * DG + DF) :=
        add_le_add hbaseN hdiff
  have hzeroRow : Czero ≤ epsilonZero n / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [Czero, epsilonZero, mul_comm] using
      hbaseRateN p hpBand
  have hnonlinear :
      (p : ℝ) * (128 * X) ≤ rawTiltNonlinearRateMajorant B c n := by
    simpa only [X, a, MF, RFone] using hnonlinearRateN p hp.pos
  have hMFpart : (p : ℝ) * MF * a ≤ (p : ℝ) * X := by
    dsimp only [X]
    nlinarith [mul_nonneg hpR.le hRF0]
  have hDFrow : (p : ℝ) * DF =
      2 * Real.exp Kscore * ((p : ℝ) * X) := by
    dsimp only [DF]
    ring
  have hMFDGrow : (p : ℝ) * MF * DG ≤
      4 * Real.exp Kscore * ((p : ℝ) * X) := by
    dsimp only [DG]
    have hE0 : 0 ≤ 4 * Real.exp Kscore := by positivity
    calc
      (p : ℝ) * MF * (4 * Real.exp Kscore * a) =
          (4 * Real.exp Kscore) * ((p : ℝ) * MF * a) := by ring
      _ ≤ (4 * Real.exp Kscore) * ((p : ℝ) * X) :=
        mul_le_mul_of_nonneg_left hMFpart hE0
  have hDFDGrow : (p : ℝ) * DF * DG ≤
      2 * Real.exp Kscore * ((p : ℝ) * X) := by
    calc
      (p : ℝ) * DF * DG ≤ (p : ℝ) * DF * 1 :=
        mul_le_mul_of_nonneg_left hDG1 (mul_nonneg hpR.le hDF0)
      _ = 2 * Real.exp Kscore * ((p : ℝ) * X) := by rw [mul_one, hDFrow]
  have hperturbRow : (p : ℝ) *
      (DF + (MF + DF) * DG + DF) ≤ epsilonPerturb n := by
    have hten : (p : ℝ) * (DF + (MF + DF) * DG + DF) ≤
        10 * Real.exp Kscore * ((p : ℝ) * X) := by
      calc
        (p : ℝ) * (DF + (MF + DF) * DG + DF) =
            (p : ℝ) * DF + (p : ℝ) * MF * DG +
              (p : ℝ) * DF * DG + (p : ℝ) * DF := by ring
        _ ≤ (2 * Real.exp Kscore * ((p : ℝ) * X)) +
            (4 * Real.exp Kscore * ((p : ℝ) * X)) +
            (2 * Real.exp Kscore * ((p : ℝ) * X)) +
            (2 * Real.exp Kscore * ((p : ℝ) * X)) := by
          exact add_le_add
            (add_le_add (add_le_add hDFrow.le hMFDGrow) hDFDGrow)
            hDFrow.le
        _ = 10 * Real.exp Kscore * ((p : ℝ) * X) := by ring
    calc
      (p : ℝ) * (DF + (MF + DF) * DG + DF) ≤
          10 * Real.exp Kscore * ((p : ℝ) * X) := hten
      _ ≤ Real.exp Kscore * ((p : ℝ) * (128 * X)) := by
        have hrow0 : 0 ≤ (p : ℝ) * X := mul_nonneg hpR.le hX0
        nlinarith [Real.exp_pos Kscore]
      _ ≤ Real.exp Kscore * rawTiltNonlinearRateMajorant B c n :=
        mul_le_mul_of_nonneg_left hnonlinear (Real.exp_pos Kscore).le
      _ = epsilonPerturb n := rfl
  have hperturb : DF + (MF + DF) * DG + DF ≤
      epsilonPerturb n / (p : ℝ) := by
    apply (le_div_iff₀ hpR).2
    simpa only [mul_comm] using hperturbRow
  calc
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))).covariance
        (fun m : S ↦ valuation p (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
      Czero + (DF + (MF + DF) * DG + DF) := by
        simpa only [mu, score, F, pref] using htilt
    _ ≤ epsilonZero n / (p : ℝ) + epsilonPerturb n / (p : ℝ) :=
      add_le_add hzeroRow hperturb
    _ = epsilon n / (p : ℝ) := by
      dsimp only [epsilon]
      ring

/-- All-prefix unrestricted terminal. -/
theorem exists_uniform_rawCell_tilted_valuation_all_prefix_rate_unrestricted
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ)
    (hB : 0 ≤ B) (hW : 1 < W)
    (hHeadLe : ∀ q ∈ H.primes, q ≤ W) :
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
    exists_uniform_rawCell_tilted_valuation_prefix_rate_unrestricted
      H hA hAC hC B W hB hW hHeadLe
  let epsilon : ℕ → ℝ := fun n ↦ |epsilon₀ n|
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlog0 : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) :=
    (hLTop.eventually (eventually_ge_atTop 1)).mono fun n hn ↦
      Real.log_nonneg hn
  have hepsilon : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have habs' : Tendsto (fun n : ℕ ↦
        |epsilon₀ n * Real.log (L n)|) atTop (nhds 0) := by
      simpa only [abs_zero] using hepsilon₀.abs
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
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hpBand).pos
  have hepsilonLe : epsilon₀ n / (p : ℝ) ≤ epsilon n / (p : ℝ) :=
    div_le_div_of_nonneg_right (le_abs_self (epsilon₀ n)) hpR.le
  by_cases hlow : physicalBound A n < k
  · by_cases hhigh : k ≤ physicalBound C n
    · exact (hprefix eta hN hlow hhigh hpBand heta hS).trans hepsilonLe
    · have hconst :
          (fun m : S ↦ if (m : ℕ) ≤ k then (1 : ℝ) else 0) =
            fun _ ↦ 1 := by
        funext m
        have hmC : (m : ℕ) ≤ physicalBound C n :=
          (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
        rw [if_pos (hmC.trans (Nat.le_of_not_ge hhigh))]
      rw [hconst]
      have hcov : ((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))).covariance
          (fun m : S ↦ valuation p (m : ℕ)) (fun _ ↦ 1) = 0 := by
        let nu := (uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
            (m : ℕ))
        calc
          nu.covariance (fun m : S ↦ valuation p (m : ℕ))
              (fun _ ↦ 1) =
            nu.covariance (fun m : S ↦ valuation p (m : ℕ))
              (fun _ ↦ 0) := by
                simpa using (nu.covariance_sub_const_right
                  (fun m : S ↦ valuation p (m : ℕ)) (fun _ ↦ 0) (-1))
          _ = 0 := nu.covariance_zero_right _
      rw [hcov, abs_zero]
      exact div_nonneg (abs_nonneg _) hpR.le
  · have hconst :
        (fun m : S ↦ if (m : ℕ) ≤ k then (1 : ℝ) else 0) =
          fun _ ↦ 0 := by
      funext m
      have hAm : physicalBound A n < (m : ℕ) :=
        (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).1
      rw [if_neg (not_le_of_gt ((Nat.le_of_not_gt hlow).trans_lt hAm))]
    rw [hconst,
      ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
          (m : ℕ))).covariance_zero_right,
      abs_zero]
    exact div_nonneg (abs_nonneg _) hpR.le

end

end Erdos390.Full.PaperRawTiltedPrefixRowUnrestricted
