import Erdos390.WholePaper.VariablePrimeCounting
import Erdos390.WholePaper.PrimeLayers
import Erdos390.WholePaper.Complement
import Erdos390.WholePaper.IncidenceBound
import Erdos390.WholePaper.LargePrimeCollision
import Erdos390.WholePaper.Constants

/-!
# Moving-layer counts and the lower-bound incidence inequality

This module packages the moving thirteen-layer argument used after the
endpoint exclusion below `2n`.  An arbitrary natural shift `h n = o(n)` is
allowed in the analytic statement; this includes the paper's uniform range
`0 < h < n / log n` along every sequence.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Union of the first thirteen moving prime layers. -/
def movingPrimeUnion13 (n M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 13).biUnion (movingPrimeLayer n M)

private theorem card_filter_prime_Ioc {a b : ℕ} (hab : a ≤ b) :
    ((Finset.Ioc a b).filter Nat.Prime).card =
      Nat.primeCounting b - Nat.primeCounting a := by
  classical
  have hdiff :
      (Finset.Ioc a b).filter Nat.Prime =
        (Finset.range (b + 1)).filter Nat.Prime \
          (Finset.range (a + 1)).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime
    · simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff,
        Finset.mem_range, hp, and_true]
      omega
    · simp [hp]
  have hsubset :
      (Finset.range (a + 1)).filter Nat.Prime ⊆
        (Finset.range (b + 1)).filter Nat.Prime := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.add_le_add_right hab 1), hp.2⟩
  rw [hdiff, Finset.card_sdiff_of_subset hsubset]
  simp only [Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]

/-- When `r*h<n`, the two `n`-endpoint conditions in a moving layer are
redundant, exactly as in the paper. -/
theorem movingPrimeLayer_eq_primeInterval {n h r : ℕ}
    (hr : 1 ≤ r) (hrh : r * h < n) :
    movingPrimeLayer n (2 * n + h) r =
      (Finset.Ioc ((2 * n + h) / (2 * r + 2))
        ((2 * n + h) / (2 * r + 1))).filter Nat.Prime := by
  ext p
  simp only [mem_movingPrimeLayer, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · intro hp
    have hpPos : 0 < p := hp.2.1.pos
    exact ⟨⟨(Nat.div_lt_iff_lt_mul (by omega)).2 (by
        simpa [Nat.mul_comm] using hp.2.2.1),
      (Nat.le_div_iff_mul_le (by omega)).2 (by
        simpa [Nat.mul_comm] using hp.2.2.2.1)⟩, hp.2.1⟩
  · rintro ⟨⟨hpLower, hpUpper⟩, hpPrime⟩
    have hpPos : 0 < p := hpPrime.pos
    have hpLower' : 2 * n + h < (2 * r + 2) * p := by
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul (by omega)).1 hpLower
    have hpUpper' : (2 * r + 1) * p ≤ 2 * n + h := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega)).1 hpUpper
    have hpLe : p ≤ 2 * n + h := by
      have : p ≤ (2 * r + 1) * p :=
        Nat.le_mul_of_pos_left p (by omega)
      exact this.trans hpUpper'
    have hnLower : n < (r + 1) * p := by nlinarith
    have hrUpper : r * p ≤ n := by
      by_contra hnr
      have hnlt : n < r * p := Nat.lt_of_not_ge hnr
      nlinarith
    exact ⟨hpLe, hpPrime, hpLower', hpUpper', hnLower, hrUpper⟩

/-- Exact prime-counting difference for a moving layer once the redundant
conditions have been removed. -/
theorem movingPrimeLayer_card_eq_primeCounting_sub {n h r : ℕ}
    (hr : 1 ≤ r) (hrh : r * h < n) :
    (movingPrimeLayer n (2 * n + h) r).card =
      Nat.primeCounting ((2 * n + h) / (2 * r + 1)) -
        Nat.primeCounting ((2 * n + h) / (2 * r + 2)) := by
  rw [movingPrimeLayer_eq_primeInterval hr hrh]
  apply card_filter_prime_Ioc
  exact Nat.div_le_div_left (by omega) (by omega)

private theorem natDiv_endpoint_ratio_tendsto
    {m : ℕ → ℕ} {a : ℝ}
    (hm : Tendsto (fun n : ℕ ↦ (m n : ℝ) / (n : ℝ)) atTop (nhds a))
    (d : ℕ) (hd : 0 < d) :
    Tendsto
      (fun n : ℕ ↦ ((m n / d : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a / (d : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦ ((m n : ℝ) / (n : ℝ)) / (d : ℝ))
        atTop (nhds (a / (d : ℝ))) :=
    hm.div_const (d : ℝ)
  have hinv :
      Tendsto (fun n : ℕ ↦ 1 / (n : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hlower :
      Tendsto
        (fun n : ℕ ↦
          ((m n : ℝ) / (n : ℝ)) / (d : ℝ) - 1 / (n : ℝ))
        atTop (nhds (a / (d : ℝ))) := by
    simpa only [sub_zero] using hmain.sub hinv
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hmain
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hfloor :
        (m n : ℝ) / (d : ℝ) < ((m n / d : ℕ) : ℝ) + 1 := by
      simpa only [Nat.floor_div_eq_div] using
        (Nat.lt_floor_add_one ((m n : ℝ) / (d : ℝ)))
    have hbase :
        (m n : ℝ) / (d : ℝ) - 1 ≤ ((m n / d : ℕ) : ℝ) := by
      linarith
    calc
      ((m n : ℝ) / (n : ℝ)) / (d : ℝ) - 1 / (n : ℝ) =
          ((m n : ℝ) / (d : ℝ) - 1) / (n : ℝ) := by
            field_simp
      _ ≤ ((m n / d : ℕ) : ℝ) / (n : ℝ) :=
        div_le_div_of_nonneg_right hbase hnR.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcast :
        ((m n / d : ℕ) : ℝ) ≤ (m n : ℝ) / (d : ℝ) :=
      Nat.cast_div_le
    calc
      ((m n / d : ℕ) : ℝ) / (n : ℝ) ≤
          ((m n : ℝ) / (d : ℝ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hcast hnR.le
      _ = ((m n : ℝ) / (n : ℝ)) / (d : ℝ) := by
        field_simp

private theorem two_mul_add_ratio_tendsto_two
    {h : ℕ → ℕ}
    (hh : Tendsto (fun n : ℕ ↦ (h n : ℝ) / (n : ℝ)) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦ ((2 * n + h n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 2) := by
  have hsum :
      Tendsto (fun n : ℕ ↦ (2 : ℝ) + (h n : ℝ) / (n : ℝ))
        atTop (nhds 2) := by
    simpa only [add_zero] using
      (tendsto_const_nhds :
        Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2)).add hh
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

private theorem eventually_row_mul_shift_lt
    {h : ℕ → ℕ}
    (hh : Tendsto (fun n : ℕ ↦ (h n : ℝ) / (n : ℝ)) atTop (nhds 0))
    {r : ℕ} (hr : 1 ≤ r) :
    ∀ᶠ n : ℕ in atTop, r * h n < n := by
  have hrPos : 0 < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hsmall :
      ∀ᶠ n : ℕ in atTop, (h n : ℝ) / (n : ℝ) < 1 / (r : ℝ) :=
    hh.eventually (gt_mem_nhds (one_div_pos.mpr hrPos))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hnSmall hn
  have hnPos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmul : (r : ℝ) * (h n : ℝ) < (n : ℝ) := by
    calc
      (r : ℝ) * (h n : ℝ) <
          (r : ℝ) * ((1 / (r : ℝ)) * (n : ℝ)) := by
        apply mul_lt_mul_of_pos_left _ hrPos
        exact (div_lt_iff₀ hnPos).mp hnSmall
      _ = (n : ℝ) := by field_simp
  exact_mod_cast hmul

/-- A fixed moving row has the same normalized mass `alpha r` as its
stationary counterpart for every sublinear natural shift. -/
theorem movingPrimeLayer_card_normalized_tendsto
    {h : ℕ → ℕ}
    (hh : Tendsto (fun n : ℕ ↦ (h n : ℝ) / (n : ℝ)) atTop (nhds 0))
    (r : ℕ) (hr : 1 ≤ r) :
    Tendsto
      (fun n : ℕ ↦
        ((movingPrimeLayer n (2 * n + h n) r).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (alpha r : ℝ)) := by
  let lower : ℕ → ℕ := fun n ↦ (2 * n + h n) / (2 * r + 2)
  let upper : ℕ → ℕ := fun n ↦ (2 * n + h n) / (2 * r + 1)
  have hMratio := two_mul_add_ratio_tendsto_two hh
  have hlowerRatio :
      Tendsto (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ))
        atTop (nhds ((1 : ℝ) / ((r : ℝ) + 1))) := by
    have h := natDiv_endpoint_ratio_tendsto hMratio (2 * r + 2) (by omega)
    have heq :
        (2 : ℝ) / ((2 * r + 2 : ℕ) : ℝ) =
          1 / ((r : ℝ) + 1) := by
      push_cast
      field_simp
    simpa only [lower, heq] using h
  have hupperRatio :
      Tendsto (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ))
        atTop (nhds ((2 : ℝ) / (2 * (r : ℝ) + 1))) := by
    have h := natDiv_endpoint_ratio_tendsto hMratio (2 * r + 1) (by omega)
    have heq :
        (2 : ℝ) / ((2 * r + 1 : ℕ) : ℝ) =
          2 / (2 * (r : ℝ) + 1) := by
      norm_num
    simpa only [upper, heq] using h
  have hlowerPNT :=
    SafePrimeCounting.primeCounting_movingEndpoint_normalized_tendsto
      (a := (1 : ℝ) / ((r : ℝ) + 1)) (by positivity) hlowerRatio
  have hupperPNT :=
    SafePrimeCounting.primeCounting_movingEndpoint_normalized_tendsto
      (a := (2 : ℝ) / (2 * (r : ℝ) + 1)) (by positivity) hupperRatio
  have hsub := hupperPNT.sub hlowerPNT
  have hsubNat :
      Tendsto
        (fun n : ℕ ↦
          ((Nat.primeCounting (upper n) - Nat.primeCounting (lower n) : ℕ) : ℝ) /
            ((n : ℝ) / Real.log (n : ℝ)))
        atTop
        (nhds ((2 : ℝ) / (2 * (r : ℝ) + 1) -
          1 / ((r : ℝ) + 1))) := by
    apply hsub.congr'
    exact Eventually.of_forall fun n ↦ by
      have hargs : lower n ≤ upper n :=
        Nat.div_le_div_left (by omega) (by omega)
      have hpi := Nat.monotone_primeCounting hargs
      dsimp only
      rw [Nat.cast_sub hpi]
      ring
  have halpha :
      (2 : ℝ) / (2 * (r : ℝ) + 1) - 1 / ((r : ℝ) + 1) =
        (alpha r : ℝ) := by
    simpa using
      congrArg (fun q : ℚ ↦ (q : ℝ)) (two_div_sub_one_div_eq_alpha r)
  rw [halpha] at hsubNat
  apply hsubNat.congr'
  filter_upwards [eventually_row_mul_shift_lt hh hr] with n hrh
  rw [movingPrimeLayer_card_eq_primeCounting_sub hr hrh]

/-- Moving layers are pairwise disjoint because membership determines
`floor (n/p)`. -/
theorem movingPrimeLayer_pairwiseDisjoint (n M : ℕ) :
    ((Finset.Icc 1 13 : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (movingPrimeLayer n M) := by
  intro r _ s _ hrs
  change Disjoint (movingPrimeLayer n M r) (movingPrimeLayer n M s)
  rw [Finset.disjoint_left]
  intro p hpr hps
  apply hrs
  rw [← div_eq_row_of_mem_movingPrimeLayer hpr,
    div_eq_row_of_mem_movingPrimeLayer hps]

theorem movingPrimeUnion13_card (n M : ℕ) :
    (movingPrimeUnion13 n M).card =
      ∑ r ∈ Finset.Icc 1 13, (movingPrimeLayer n M r).card := by
  exact Finset.card_biUnion (movingPrimeLayer_pairwiseDisjoint n M)

/-- The complete moving thirteen-layer union has normalized mass `A13` for
every sublinear natural shift. -/
theorem movingPrimeUnion13_card_normalized_tendsto
    {h : ℕ → ℕ}
    (hh : Tendsto (fun n : ℕ ↦ (h n : ℝ) / (n : ℝ)) atTop (nhds 0)) :
    Tendsto
      (fun n : ℕ ↦
        ((movingPrimeUnion13 n (2 * n + h n)).card : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (A13 : ℝ)) := by
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          ∑ r ∈ Finset.Icc 1 13,
            ((movingPrimeLayer n (2 * n + h n) r).card : ℝ) /
              ((n : ℝ) / Real.log (n : ℝ)))
        atTop (nhds (∑ r ∈ Finset.Icc 1 13, (alpha r : ℝ))) := by
    apply tendsto_finset_sum
    intro r hr
    exact movingPrimeLayer_card_normalized_tendsto hh r (Finset.mem_Icc.mp hr).1
  have hmass :
      (∑ r ∈ Finset.Icc 1 13, (alpha r : ℝ)) = (A13 : ℝ) := by
    simp only [A13, Rat.cast_sum]
  rw [hmass] at hsum
  apply hsum.congr'
  exact Eventually.of_forall fun n ↦ by
    dsimp only
    rw [movingPrimeUnion13_card, Nat.cast_sum]
    exact (Finset.sum_div _ _ _).symm

private theorem movingPrimeUnion13_prime {n M p : ℕ}
    (hp : p ∈ movingPrimeUnion13 n M) :
    p.Prime := by
  rw [movingPrimeUnion13, Finset.mem_biUnion] at hp
  obtain ⟨r, _hr, hpr⟩ := hp
  exact movingPrimeLayer_prime hpr

private theorem twentyEightCutoff_le_of_mem_movingPrimeUnion13
    {n M p : ℕ} (hp : p ∈ movingPrimeUnion13 n M) :
    M / 28 + 1 ≤ p := by
  rw [movingPrimeUnion13, Finset.mem_biUnion] at hp
  obtain ⟨r, hr, hpr⟩ := hp
  have hrUpper : 2 * r + 2 ≤ 28 := by
    have := (Finset.mem_Icc.mp hr).2
    omega
  have hlower := (mem_movingPrimeLayer.mp hpr).2.2.1
  have hTwentyEight : M < 28 * p :=
    hlower.trans_le (Nat.mul_le_mul_right p hrUpper)
  have hdiv : M / 28 < p :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).2 (by
      simpa [Nat.mul_comm] using hTwentyEight)
  omega

private theorem movingEndpoint_lt_twentyEightCutoff_sq
    (n h : ℕ) (hn : 392 ≤ n) :
    2 * n + h <
      ((2 * n + h) / 28 + 1) * ((2 * n + h) / 28 + 1) := by
  let M := 2 * n + h
  have hMUpper : M < (M / 28 + 1) * 28 :=
    (Nat.div_lt_iff_lt_mul (by norm_num)).1 (Nat.lt_succ_self (M / 28))
  have hMLower : 28 ≤ M / 28 :=
    (Nat.le_div_iff_mul_le (by norm_num)).2 (by
      dsimp only [M]
      omega)
  dsimp only [M] at hMUpper hMLower ⊢
  nlinarith

/-- Exact moving-layer incidence inequality, proved from unique prime
carriers rather than assumed as a conditional estimate. -/
theorem movingPrimeUnion13_card_le_smallPrimeFactorizationSum
    {n h : ℕ} (hn : 392 ≤ n) {selected : Finset ℕ}
    (hselected : selected ⊆ factorInterval n (2 * n + h))
    (hprod : selected.prod id * n.factorial ^ 2 = (2 * n + h).factorial) :
    (movingPrimeUnion13 n (2 * n + h)).card ≤
      ∑ ℓ ∈ smallPrimes, (selected.prod id).factorization ℓ := by
  let M := 2 * n + h
  have hnPos : 0 < n := by omega
  have hMPos : 0 < M := by
    dsimp only [M]
    omega
  have hselectedPos : ∀ a ∈ selected, 0 < a := by
    intro a ha
    have hinterval : n < a ∧ a ≤ M := by
      simpa only [M, factorInterval, Finset.mem_Ioc] using hselected ha
    omega
  have hcutoffSq : M < (M / 28 + 1) * (M / 28 + 1) := by
    simpa only [M] using movingEndpoint_lt_twentyEightCutoff_sq n h hn
  have hcarrierExists :
      ∀ p : ℕ, ∃ a : ℕ,
        p ∈ movingPrimeUnion13 n M → a ∈ selected ∧ p ∣ a := by
    intro p
    by_cases hp : p ∈ movingPrimeUnion13 n M
    · have hpRows := hp
      rw [movingPrimeUnion13, Finset.mem_biUnion] at hpRows
      obtain ⟨r, _hr, hpr⟩ := hpRows
      have hcutoffLe : M / 28 + 1 ≤ p :=
        twentyEightCutoff_le_of_mem_movingPrimeUnion13 hp
      have hcutoffPow :
          (M / 28 + 1) * (M / 28 + 1) ≤ p ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul hcutoffLe hcutoffLe
      have hMSq : M < p ^ 2 := hcutoffSq.trans_le hcutoffPow
      have hnSq : n < p ^ 2 := by
        have hnM : n ≤ M := by
          dsimp only [M]
          omega
        exact hnM.trans_lt hMSq
      have hvaluation : (selected.prod id).factorization p = 1 :=
        complementProduct_factorization_eq_one_of_mem_movingPrimeLayer
          hnPos hMPos hpr hnSq hMSq hselectedPos (by simpa only [M] using hprod)
      obtain ⟨a, ha, _haUnique⟩ :=
        existsUnique_dvd_of_prod_factorization_eq_one
          (movingPrimeUnion13_prime hp) hselectedPos hvaluation
      exact ⟨a, fun _hp ↦ ha⟩
    · exact ⟨0, fun hp' ↦ (hp hp').elim⟩
  choose carrier hcarrierSpec using hcarrierExists
  have hcarrierMem :
      ∀ p ∈ movingPrimeUnion13 n M, carrier p ∈ selected := by
    intro p hp
    exact (hcarrierSpec p hp).1
  have hcarrierDvd :
      ∀ p ∈ movingPrimeUnion13 n M, p ∣ carrier p := by
    intro p hp
    exact (hcarrierSpec p hp).2
  have hcarrierInj :
      Set.InjOn carrier (movingPrimeUnion13 n M : Set ℕ) := by
    intro p hp q hq hcarrierEq
    by_contra hpq
    have hpMem : p ∈ movingPrimeUnion13 n M := hp
    have hqMem : q ∈ movingPrimeUnion13 n M := hq
    have hpCarrierInterval : n < carrier p ∧ carrier p ≤ M := by
      simpa only [M, factorInterval, Finset.mem_Ioc] using
        hselected (hcarrierMem p hpMem)
    have hqCarrierInterval : n < carrier q ∧ carrier q ≤ M := by
      simpa only [M, factorInterval, Finset.mem_Ioc] using
        hselected (hcarrierMem q hqMem)
    have hcarrierNe := carrier_ne_of_distinct_large_primes
      (movingPrimeUnion13_prime hpMem) (movingPrimeUnion13_prime hqMem) hpq
      (twentyEightCutoff_le_of_mem_movingPrimeUnion13 hpMem)
      (twentyEightCutoff_le_of_mem_movingPrimeUnion13 hqMem)
      (by omega : 0 < carrier p) hpCarrierInterval.2 hcutoffSq
      (hcarrierDvd p hpMem) (hcarrierDvd q hqMem)
    exact hcarrierNe hcarrierEq
  have hsmallDiv :
      ∀ p ∈ movingPrimeUnion13 n M,
        ∃ ℓ ∈ smallPrimes, ℓ.Prime ∧ ℓ ∣ carrier p := by
    intro p hp
    have hpRows := hp
    rw [movingPrimeUnion13, Finset.mem_biUnion] at hpRows
    obtain ⟨r, hr, hpr⟩ := hpRows
    obtain ⟨q, hcarrierEq⟩ := hcarrierDvd p hp
    have hcarrierInterval : n < carrier p ∧ carrier p ≤ M := by
      simpa only [M, factorInterval, Finset.mem_Ioc] using
        hselected (hcarrierMem p hp)
    have hqRange := cofactor_range_of_mem_movingPrimeLayer hpr
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
  simpa only [M] using
    card_le_sum_prod_factorization_of_injective_carriers
      hcarrierMem hcarrierInj hselectedPos hsmallDiv

/-- Public factorial valuation-difference form of the moving incidence
inequality. -/
theorem movingPrimeUnion13_card_le_factorialValuationSub
    {n h : ℕ} (hn : 392 ≤ n) {selected : Finset ℕ}
    (hselected : selected ⊆ factorInterval n (2 * n + h))
    (hprod : selected.prod id * n.factorial ^ 2 = (2 * n + h).factorial) :
    (movingPrimeUnion13 n (2 * n + h)).card ≤
      ∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) := by
  have hincidence :=
    movingPrimeUnion13_card_le_smallPrimeFactorizationSum hn hselected hprod
  have hselectedPos : ∀ a ∈ selected, 0 < a := by
    intro a ha
    have hinterval : n < a ∧ a ≤ 2 * n + h := by
      simpa only [factorInterval, Finset.mem_Ioc] using hselected ha
    omega
  have hselectedProdNe : selected.prod id ≠ 0 :=
    (Finset.prod_pos hselectedPos).ne'
  have hfactorization := congrArg Nat.factorization hprod
  rw [Nat.factorization_mul hselectedProdNe
      (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfactorization
  have hcoordinate : ∀ ℓ : ℕ,
      (selected.prod id).factorization ℓ =
        (2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ := by
    intro ℓ
    have hcoord := congrArg (fun v : ℕ →₀ ℕ ↦ v ℓ) hfactorization
    simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hcoord
    omega
  calc
    (movingPrimeUnion13 n (2 * n + h)).card ≤
        ∑ ℓ ∈ smallPrimes, (selected.prod id).factorization ℓ := hincidence
    _ = ∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) := by
      apply Finset.sum_congr rfl
      intro ℓ _hℓ
      exact hcoordinate ℓ

/-- Admissibility itself forces the public factorial valuation-difference
inequality. -/
theorem movingPrimeUnion13_card_le_factorialValuationSub_of_admissible
    {n h : ℕ} (hn : 392 ≤ n)
    (hAdmissible : IsAdmissibleEndpoint n (2 * n + h)) :
    (movingPrimeUnion13 n (2 * n + h)).card ≤
      ∑ ℓ ∈ smallPrimes,
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) := by
  have hnM : n < 2 * n + h := by omega
  obtain ⟨selected, hselected, hselectedQ⟩ :=
    (complement_formulation hnM).mp hAdmissible
  have hcross :
      selected.prod id * n.factorial ^ 2 = (2 * n + h).factorial :=
    prod_eq_complementQuotient_iff.mp hselectedQ
  exact movingPrimeUnion13_card_le_factorialValuationSub
    hn hselected hcross

end

end Erdos390.WholePaper
