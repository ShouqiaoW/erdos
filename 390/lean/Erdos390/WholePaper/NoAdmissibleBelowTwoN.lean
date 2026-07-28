import Erdos390.WholePaper.StationaryLayers
import Erdos390.WholePaper.CentralExtension
import Erdos390.WholePaper.FactorizationIncidence
import Erdos390.WholePaper.LargePrimeCollision
import Erdos390.WholePaper.Constants
import Erdos390.WholePaper.IncidenceBound

/-!
# No admissible endpoint at or below twice the base

This module formalizes the preliminary lemma in the thirteen-layer lower
bound.  The first thirteen stationary prime layers force more distinct
large-prime carriers in any central extension than can be supported by the
valuation of the nine small primes.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The union of the first thirteen stationary layers. -/
def stationaryPrimeUnion13 (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 13).biUnion (stationaryPrimeLayer n)

/-- The total valuation of the central binomial coefficient at the nine
small primes used in the paper. -/
def centralSmallPrimeValuationSum (n : ℕ) : ℕ :=
  ∑ ℓ ∈ smallPrimes, (Nat.choose (2 * n) n).factorization ℓ

/-- The lower stationary endpoint determines `floor (n / p)`. -/
theorem div_eq_row_of_mem_stationaryPrimeLayer {n r p : ℕ}
    (hp : p ∈ stationaryPrimeLayer n r) :
    n / p = r := by
  have hpPrime := (mem_stationaryPrimeLayer.mp hp).1
  have hpPos : 0 < p := hpPrime.pos
  have hlower := (mem_stationaryPrimeLayer.mp hp).2.1
  have hupper := (mem_stationaryPrimeLayer.mp hp).2.2
  have hrp : r * p ≤ n := by nlinarith
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa [Nat.mul_comm] using hlower))
  · exact (Nat.le_div_iff_mul_le hpPos).2 hrp

/-- The upper stationary endpoint determines `floor (2n / p)`. -/
theorem two_mul_div_eq_two_mul_row_add_one_of_mem_stationaryPrimeLayer
    {n r p : ℕ} (hp : p ∈ stationaryPrimeLayer n r) :
    (2 * n) / p = 2 * r + 1 := by
  have hpPrime := (mem_stationaryPrimeLayer.mp hp).1
  have hpPos : 0 < p := hpPrime.pos
  have hlower := (mem_stationaryPrimeLayer.mp hp).2.1
  have hupper := (mem_stationaryPrimeLayer.mp hp).2.2
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).2 (by
      nlinarith))
  · exact (Nat.le_div_iff_mul_le hpPos).2 (by
      simpa [Nat.mul_comm] using hupper)

/-- Uniform square-root cutoff for all of the first thirteen rows. -/
theorem two_mul_lt_sq_of_mem_stationaryPrimeLayer
    {n r p : ℕ} (hn : 392 ≤ n) (hr : r ≤ 13)
    (hp : p ∈ stationaryPrimeLayer n r) :
    2 * n < p ^ 2 := by
  have hlower := (mem_stationaryPrimeLayer.mp hp).2.1
  have hrOne : r + 1 ≤ 14 := by omega
  have hFourteen : n < p * 14 :=
    hlower.trans_le (Nat.mul_le_mul_left p hrOne)
  have hpLower : 29 ≤ p := by nlinarith
  rw [pow_two]
  nlinarith

/-- Legendre's carry in a stationary layer is exactly one. -/
theorem centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer
    {n r p : ℕ} (hn : 392 ≤ n) (hr : r ≤ 13)
    (hp : p ∈ stationaryPrimeLayer n r) :
    (Nat.choose (2 * n) n).factorization p = 1 := by
  have hpPrime := (mem_stationaryPrimeLayer.mp hp).1
  have hnPos : 0 < n := by omega
  have htwoNPos : 0 < 2 * n := by omega
  have htwoNSq := two_mul_lt_sq_of_mem_stationaryPrimeLayer hn hr hp
  have hnSq : n < p ^ 2 := (show n ≤ 2 * n by omega).trans_lt htwoNSq
  have hnFac : n.factorial.factorization p = r := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime hnPos hnSq,
      div_eq_row_of_mem_stationaryPrimeLayer hp]
  have htwoNFac : (2 * n).factorial.factorization p = 2 * r + 1 := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime htwoNPos htwoNSq,
      two_mul_div_eq_two_mul_row_add_one_of_mem_stationaryPrimeLayer hp]
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hfactorization :=
    congrArg Nat.factorization (centralChoose_mul_factorial_sq n)
  rw [Nat.factorization_mul hchoosePos.ne'
      (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hcoordinate
  rw [hnFac, htwoNFac] at hcoordinate
  omega

/-- A carrier in `(n,2n]` for a stationary layer prime has the paper's
cofactor range `[r+1,2r+1]`. -/
theorem cofactor_range_of_mem_stationaryPrimeLayer
    {n r p q : ℕ} (hp : p ∈ stationaryPrimeLayer n r)
    (hnpq : n < p * q) (hpqTwoN : p * q ≤ 2 * n) :
    r + 1 ≤ q ∧ q ≤ 2 * r + 1 := by
  have hpPos : 0 < p := (mem_stationaryPrimeLayer.mp hp).1.pos
  constructor
  · rw [← Nat.lt_iff_add_one_le,
      ← div_eq_row_of_mem_stationaryPrimeLayer hp]
    exact (Nat.div_lt_iff_lt_mul hpPos).2 (by
      simpa [Nat.mul_comm] using hnpq)
  · rw [← two_mul_div_eq_two_mul_row_add_one_of_mem_stationaryPrimeLayer hp]
    exact (Nat.le_div_iff_mul_le hpPos).2 (by
      simpa [Nat.mul_comm] using hpqTwoN)

/-- Membership in two stationary layers determines the same row. -/
theorem stationaryPrimeLayer_row_eq_of_mem {n r s p : ℕ}
    (hpr : p ∈ stationaryPrimeLayer n r)
    (hps : p ∈ stationaryPrimeLayer n s) :
    r = s := by
  rw [← div_eq_row_of_mem_stationaryPrimeLayer hpr,
    div_eq_row_of_mem_stationaryPrimeLayer hps]

/-- The stationary layers are pairwise disjoint. -/
theorem stationaryPrimeLayer_pairwiseDisjoint (n : ℕ) :
    ((Finset.Icc 1 13 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (stationaryPrimeLayer n) := by
  intro r _ s _ hrs
  change Disjoint (stationaryPrimeLayer n r) (stationaryPrimeLayer n s)
  rw [Finset.disjoint_left]
  intro p hpr hps
  exact hrs (stationaryPrimeLayer_row_eq_of_mem hpr hps)

/-- Because the rows are disjoint, the union cardinality is the sum of the
thirteen row cardinalities. -/
theorem stationaryPrimeUnion13_card (n : ℕ) :
    (stationaryPrimeUnion13 n).card =
      ∑ r ∈ Finset.Icc 1 13, (stationaryPrimeLayer n r).card := by
  exact Finset.card_biUnion (stationaryPrimeLayer_pairwiseDisjoint n)

/-- The union of the first thirteen layers has normalized mass `A13`. -/
theorem stationaryPrimeUnion13_card_normalized_tendsto :
    Tendsto
      (fun n : ℕ ↦
        ((stationaryPrimeUnion13 n).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (A13 : ℝ)) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          ∑ r ∈ Finset.Icc 1 13,
            ((stationaryPrimeLayer n r).card : ℝ) /
              ((n : ℝ) / Real.log (n : ℝ)))
        atTop
        (nhds (∑ r ∈ Finset.Icc 1 13, (alpha r : ℝ))) := by
    apply tendsto_finset_sum
    intro r hr
    exact stationaryPrimeLayer_card_normalized_tendsto r
      (Finset.mem_Icc.mp hr).1
  have hmass :
      (∑ r ∈ Finset.Icc 1 13, (alpha r : ℝ)) = (A13 : ℝ) := by
    simp only [A13, Rat.cast_sum]
  rw [hmass] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [stationaryPrimeUnion13_card, Nat.cast_sum]
    exact (Finset.sum_div _ _ _).symm

/-- Each of the nine fixed small-prime valuations is logarithmically
bounded, uniformly here by the base-two logarithm. -/
theorem centralSmallPrimeValuationSum_le_log2 (n : ℕ) :
    centralSmallPrimeValuationSum n ≤ 9 * Nat.log2 (2 * n) := by
  rw [centralSmallPrimeValuationSum]
  calc
    ∑ ℓ ∈ smallPrimes, (Nat.choose (2 * n) n).factorization ℓ ≤
        ∑ _ℓ ∈ smallPrimes, Nat.log2 (2 * n) := by
      apply Finset.sum_le_sum
      intro ℓ hℓ
      have htwo : 2 ≤ ℓ := by
        simp [smallPrimes] at hℓ
        omega
      calc
        (Nat.choose (2 * n) n).factorization ℓ ≤ Nat.log ℓ (2 * n) :=
          Nat.factorization_choose_le_log
        _ ≤ Nat.log 2 (2 * n) :=
          Nat.log_anti_left Nat.one_lt_two htwo
        _ = Nat.log2 (2 * n) := Nat.log2_eq_log_two.symm
    _ = 9 * Nat.log2 (2 * n) := by norm_num [smallPrimes]

private theorem tendsto_log_natCast_div_natCast :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem tendsto_log_sq_natCast_div_natCast :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem tendsto_log_two_mul_natCast_mul_log_div_natCast :
    Tendsto
      (fun n : ℕ ↦
        Real.log (2 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hconstant :
      Tendsto (fun _n : ℕ ↦ Real.log 2) atTop (nhds (Real.log 2)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 2 * (Real.log (n : ℝ) / (n : ℝ)) +
            Real.log (n : ℝ) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hconstant.mul tendsto_log_natCast_div_natCast).add
        tendsto_log_sq_natCast_div_natCast
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnReal]
  ring

private theorem tendsto_nine_mul_logb_two_two_mul_normalized :
    Tendsto
      (fun n : ℕ ↦
        (9 * Real.logb 2 (2 * (n : ℝ))) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  have hscaled :
      Tendsto
        (fun n : ℕ ↦
          (9 / Real.log 2) *
            (Real.log (2 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      tendsto_log_two_mul_natCast_mul_log_div_natCast.const_mul
        (9 / Real.log 2)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos one_lt_two).ne'
  rw [Real.logb]
  field_simp

/-- The nine small-prime valuations together are negligible compared with
`n / log n`. -/
theorem centralSmallPrimeValuationSum_normalized_tendsto :
    Tendsto
      (fun n : ℕ ↦
        (centralSmallPrimeValuationSum n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    tendsto_nine_mul_logb_two_two_mul_normalized
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := by
      exact div_pos (by exact_mod_cast (Nat.zero_lt_of_lt hn))
        (Real.log_pos (by exact_mod_cast hn))
    exact div_nonneg (Nat.cast_nonneg _) hden.le
  · filter_upwards [eventually_gt_atTop 1] with n hn
    have hden : 0 < (n : ℝ) / Real.log (n : ℝ) := by
      exact div_pos (by exact_mod_cast (Nat.zero_lt_of_lt hn))
        (Real.log_pos (by exact_mod_cast hn))
    have hbound :
        (centralSmallPrimeValuationSum n : ℝ) ≤
          9 * (Nat.log2 (2 * n) : ℝ) := by
      exact_mod_cast centralSmallPrimeValuationSum_le_log2 n
    have hlogBound :
        (Nat.log2 (2 * n) : ℝ) ≤
          Real.logb 2 (2 * (n : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        Real.log2_le_logb (2 * n)
    exact div_le_div_of_nonneg_right
      (hbound.trans (mul_le_mul_of_nonneg_left hlogBound (by norm_num))) hden.le

private theorem stationaryPrimeUnion13_prime {n p : ℕ}
    (hp : p ∈ stationaryPrimeUnion13 n) :
    p.Prime := by
  rw [stationaryPrimeUnion13, Finset.mem_biUnion] at hp
  obtain ⟨r, _hr, hpr⟩ := hp
  exact (mem_stationaryPrimeLayer.mp hpr).1

private theorem fourteenCutoff_le_of_mem_stationaryPrimeUnion13
    {n p : ℕ} (hp : p ∈ stationaryPrimeUnion13 n) :
    n / 14 + 1 ≤ p := by
  rw [stationaryPrimeUnion13, Finset.mem_biUnion] at hp
  obtain ⟨r, hr, hpr⟩ := hp
  have hrUpper : r + 1 ≤ 14 := by
    have := (Finset.mem_Icc.mp hr).2
    omega
  have hlower := (mem_stationaryPrimeLayer.mp hpr).2.1
  have hFourteen : n < p * 14 :=
    hlower.trans_le (Nat.mul_le_mul_left p hrUpper)
  have hdiv : n / 14 < p :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).2 hFourteen
  omega

private theorem two_mul_lt_fourteenCutoff_sq (n : ℕ) (hn : 392 ≤ n) :
    2 * n < (n / 14 + 1) * (n / 14 + 1) := by
  have hnUpper : n < (n / 14 + 1) * 14 :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).1 (Nat.lt_succ_self (n / 14))
  have hdivLower : 28 ≤ n / 14 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  nlinarith

/-- The exact finite incidence inequality for any representation of the
central binomial coefficient by distinct factors in `(n,2n]`. -/
theorem stationaryPrimeUnion13_card_le_centralSmallPrimeValuationSum
    {n : ℕ} (hn : 392 ≤ n) {selected : Finset ℕ}
    (hselected : selected ⊆ factorInterval n (2 * n))
    (hprod : selected.prod id = Nat.choose (2 * n) n) :
    (stationaryPrimeUnion13 n).card ≤ centralSmallPrimeValuationSum n := by
  have hselectedPos : ∀ a ∈ selected, 0 < a := by
    intro a ha
    have hinterval : n < a ∧ a ≤ 2 * n := by
      simpa only [factorInterval, Finset.mem_Ioc] using hselected ha
    omega
  have hcarrierExists :
      ∀ p : ℕ, ∃ a : ℕ,
        p ∈ stationaryPrimeUnion13 n → a ∈ selected ∧ p ∣ a := by
    intro p
    by_cases hp : p ∈ stationaryPrimeUnion13 n
    · have hpRows := hp
      rw [stationaryPrimeUnion13, Finset.mem_biUnion] at hpRows
      obtain ⟨r, hr, hpr⟩ := hpRows
      have hvaluation : (selected.prod id).factorization p = 1 := by
        rw [hprod]
        exact centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer
          hn (Finset.mem_Icc.mp hr).2 hpr
      obtain ⟨a, ha, _haUnique⟩ :=
        existsUnique_dvd_of_prod_factorization_eq_one
          (stationaryPrimeUnion13_prime hp) hselectedPos hvaluation
      exact ⟨a, fun _hp ↦ ha⟩
    · exact ⟨0, fun hp' ↦ (hp hp').elim⟩
  choose carrier hcarrierSpec using hcarrierExists
  have hcarrierMem :
      ∀ p ∈ stationaryPrimeUnion13 n, carrier p ∈ selected := by
    intro p hp
    exact (hcarrierSpec p hp).1
  have hcarrierDvd :
      ∀ p ∈ stationaryPrimeUnion13 n, p ∣ carrier p := by
    intro p hp
    exact (hcarrierSpec p hp).2
  have hcarrierInj :
      Set.InjOn carrier (stationaryPrimeUnion13 n : Set ℕ) := by
    intro p hp q hq hcarrierEq
    by_contra hpq
    have hpMem : p ∈ stationaryPrimeUnion13 n := hp
    have hqMem : q ∈ stationaryPrimeUnion13 n := hq
    have hpCarrierInterval : n < carrier p ∧ carrier p ≤ 2 * n := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        hselected (hcarrierMem p hpMem)
    have hqCarrierInterval : n < carrier q ∧ carrier q ≤ 2 * n := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        hselected (hcarrierMem q hqMem)
    have hcarrierNe := carrier_ne_of_distinct_large_primes
      (stationaryPrimeUnion13_prime hpMem)
      (stationaryPrimeUnion13_prime hqMem) hpq
      (fourteenCutoff_le_of_mem_stationaryPrimeUnion13 hpMem)
      (fourteenCutoff_le_of_mem_stationaryPrimeUnion13 hqMem)
      (by omega : 0 < carrier p) hpCarrierInterval.2
      (two_mul_lt_fourteenCutoff_sq n hn)
      (hcarrierDvd p hpMem) (hcarrierDvd q hqMem)
    exact hcarrierNe hcarrierEq
  have hsmallDiv :
      ∀ p ∈ stationaryPrimeUnion13 n,
        ∃ ℓ ∈ smallPrimes, ℓ.Prime ∧ ℓ ∣ carrier p := by
    intro p hp
    have hpRows := hp
    rw [stationaryPrimeUnion13, Finset.mem_biUnion] at hpRows
    obtain ⟨r, hr, hpr⟩ := hpRows
    obtain ⟨q, hcarrierEq⟩ := hcarrierDvd p hp
    have hcarrierInterval : n < carrier p ∧ carrier p ≤ 2 * n := by
      simpa only [factorInterval, Finset.mem_Ioc] using
        hselected (hcarrierMem p hp)
    have hqRange := cofactor_range_of_mem_stationaryPrimeLayer hpr
      (by simpa only [hcarrierEq] using hcarrierInterval.1)
      (by simpa only [hcarrierEq] using hcarrierInterval.2)
    have hqIcc : q ∈ Finset.Icc 2 27 := by
      rw [Finset.mem_Icc]
      have hrRange := Finset.mem_Icc.mp hr
      omega
    obtain ⟨ℓ, hℓSmall, hℓPrime, hℓDvd⟩ :=
      exists_smallPrime_dvd_of_mem_Icc hqIcc
    refine ⟨ℓ, hℓSmall, hℓPrime, ?_⟩
    rw [hcarrierEq]
    exact dvd_mul_of_dvd_right hℓDvd p
  have hincidence :=
    card_le_sum_prod_factorization_of_injective_carriers
      hcarrierMem hcarrierInj hselectedPos hsmallDiv
  rw [hprod] at hincidence
  simpa only [centralSmallPrimeValuationSum] using hincidence

/-- Paper Lemma `no-admissible-endpoint-below-two-n`: uniformly in the
endpoint, no admissible endpoint at or below `2n` exists for all sufficiently
large `n`. -/
theorem eventually_no_admissibleEndpoint_le_two_mul :
    ∀ᶠ n : ℕ in atTop,
      ∀ M ≤ 2 * n, ¬ IsAdmissibleEndpoint n M := by
  have hdiff :
      Tendsto
        (fun n : ℕ ↦
          ((stationaryPrimeUnion13 n).card : ℝ) /
              ((n : ℝ) / Real.log (n : ℝ)) -
            (centralSmallPrimeValuationSum n : ℝ) /
              ((n : ℝ) / Real.log (n : ℝ)))
        atTop (nhds (A13 : ℝ)) := by
    simpa only [sub_zero] using
      stationaryPrimeUnion13_card_normalized_tendsto.sub
        centralSmallPrimeValuationSum_normalized_tendsto
  have hA13Pos : 0 < (A13 : ℝ) := by
    rw [A13_eq]
    positivity
  have hgap :
      ∀ᶠ n : ℕ in atTop,
        0 <
          ((stationaryPrimeUnion13 n).card : ℝ) /
              ((n : ℝ) / Real.log (n : ℝ)) -
            (centralSmallPrimeValuationSum n : ℝ) /
              ((n : ℝ) / Real.log (n : ℝ)) :=
    hdiff.eventually (Ioi_mem_nhds hA13Pos)
  filter_upwards [eventually_ge_atTop 392, hgap] with n hn hgapN
  intro M hM hAdmissible
  have hnThree : 3 ≤ n := by omega
  obtain ⟨selected, hselected, hprod⟩ :=
    exists_centralExtension_of_admissible hnThree hM hAdmissible
  have hincidence :=
    stationaryPrimeUnion13_card_le_centralSmallPrimeValuationSum
      hn hselected hprod
  have hdenPos : 0 < (n : ℝ) / Real.log (n : ℝ) := by
    exact div_pos (by exact_mod_cast (show 0 < n by omega))
      (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
  have hnormalized :
      ((stationaryPrimeUnion13 n).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) ≤
        (centralSmallPrimeValuationSum n : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hincidence) hdenPos.le
  linarith

end

end Erdos390.WholePaper
