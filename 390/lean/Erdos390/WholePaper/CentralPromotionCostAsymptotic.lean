import Erdos390.WholePaper.ResidualCentralFactors
import Erdos390.WholePaper.SafePrimeCounting
import Erdos390.WholePaper.UpperScale

/-!
# The residual central-promotion cost

This file proves the quantitative form of (4.10)--(4.11).  The elementary
promotion estimate is summed over the actual residual prime support.  A
Chebyshev estimate then shows that, after choosing one fixed cutoff
parameter, its total cost is an arbitrarily small multiple of `n / log n`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- A real majorant for the total promotion cost at cutoff `X`. -/
def centralPromotionMajorant (n X : ℕ) : ℝ :=
  (Nat.primeCounting X : ℝ) +
    ((Nat.primeCounting X : ℝ) * Real.log (n : ℝ) -
        Chebyshev.theta (X : ℝ)) / Real.log 2

private theorem card_primes_Ioc_zero (X : ℕ) :
    ((Finset.Ioc 0 X).filter Nat.Prime).card = Nat.primeCounting X := by
  have heq :
      (Finset.Ioc 0 X).filter Nat.Prime =
        (Finset.range (X + 1)).filter Nat.Prime := by
    ext p
    by_cases hp : p.Prime
    · simp [hp, hp.pos]
    · simp [hp]
  rw [heq]
  simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

private theorem sum_log_primes_Ioc_zero (X : ℕ) :
    ∑ p ∈ (Finset.Ioc 0 X).filter Nat.Prime, Real.log (p : ℝ) =
      Chebyshev.theta (X : ℝ) := by
  simp [Chebyshev.theta]

private theorem sum_prime_logb_eq_majorant (n X : ℕ) (hX : X ≤ n) :
    ∑ p ∈ (Finset.Ioc 0 X).filter Nat.Prime,
        (1 + Real.logb 2 ((n : ℝ) / (p : ℝ))) =
      centralPromotionMajorant n X := by
  classical
  by_cases hn : n = 0
  · subst n
    have : X = 0 := Nat.eq_zero_of_le_zero hX
    subst X
    simp [centralPromotionMajorant, Chebyshev.theta]
  have hsumLog :
      ∑ p ∈ (Finset.Ioc 0 X).filter Nat.Prime,
          Real.log ((n : ℝ) / (p : ℝ)) =
        ∑ p ∈ (Finset.Ioc 0 X).filter Nat.Prime,
          (Real.log (n : ℝ) - Real.log (p : ℝ)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Real.log_div]
    · exact_mod_cast hn
    · exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  simp only [Real.logb]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_primes_Ioc_zero, ← Finset.sum_div]
  rw [hsumLog]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [card_primes_Ioc_zero, sum_log_primes_Ioc_zero]
  simp only [centralPromotionMajorant]
  ring

/-- The actual finite promotion cost is bounded by the Chebyshev majorant.
This is the summed form of the paper's pointwise estimate (4.10). -/
theorem residualPromotionCost_cast_le_centralPromotionMajorant
    {n X : ℕ} (hX : X ≤ n) :
    (residualPromotionCost n X : ℝ) ≤ centralPromotionMajorant n X := by
  classical
  let primes : Finset ℕ := (Finset.Ioc 0 X).filter Nat.Prime
  have hsubset : residualCentralPrimes n X ⊆ primes := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ioc.mpr
        ⟨(residualCentralPrimes_prime hp).pos,
          residualCentralPrimes_le hp⟩,
        residualCentralPrimes_prime hp⟩
  have hpoint : ∀ p ∈ residualCentralPrimes n X,
      (promotionExponent n (centralPrimeBlock n p) : ℝ) ≤
        1 + Real.logb 2 ((n : ℝ) / (p : ℝ)) := by
    intro p hp
    have hpPrime := residualCentralPrimes_prime hp
    have hpLeN : p ≤ n := (residualCentralPrimes_le hp).trans hX
    have hdivPos : 0 < n / p := Nat.div_pos hpLeN hpPrime.pos
    have hnat := centralPromotionExponent_le_one_add_log2 hpPrime
      (residualCentralPrimes_exponent_pos hp)
    have hlogNat :
        (Nat.log2 (n / p) : ℝ) ≤
          Real.logb 2 ((n / p : ℕ) : ℝ) :=
      Real.log2_le_logb (n / p)
    have hcastDiv : ((n / p : ℕ) : ℝ) ≤
        (n : ℝ) / (p : ℝ) := Nat.cast_div_le
    have hlogCast :
        Real.logb 2 ((n / p : ℕ) : ℝ) ≤
          Real.logb 2 ((n : ℝ) / (p : ℝ)) :=
      Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast hdivPos) hcastDiv
    have hnatCast :
        (promotionExponent n (centralPrimeBlock n p) : ℝ) ≤
          1 + (Nat.log2 (n / p) : ℝ) := by
      exact_mod_cast hnat
    linarith
  have hnonneg : ∀ p ∈ primes, p ∉ residualCentralPrimes n X →
      0 ≤ 1 + Real.logb 2 ((n : ℝ) / (p : ℝ)) := by
    intro p hp _
    have hpMem := Finset.mem_filter.mp hp
    have hpLeN : p ≤ n := (Finset.mem_Ioc.mp hpMem.1).2.trans hX
    have hpPos : 0 < p := hpMem.2.pos
    have hratio : (1 : ℝ) ≤ (n : ℝ) / (p : ℝ) := by
      apply (le_div_iff₀ (by exact_mod_cast hpPos)).2
      simpa only [one_mul] using (show (p : ℝ) ≤ n by exact_mod_cast hpLeN)
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hratio
    linarith
  calc
    (residualPromotionCost n X : ℝ) =
        ∑ p ∈ residualCentralPrimes n X,
          (promotionExponent n (centralPrimeBlock n p) : ℝ) := by
            simp [residualPromotionCost]
    _ ≤ ∑ p ∈ residualCentralPrimes n X,
          (1 + Real.logb 2 ((n : ℝ) / (p : ℝ))) := by
            exact Finset.sum_le_sum fun p hp ↦ hpoint p hp
    _ ≤ ∑ p ∈ primes,
          (1 + Real.logb 2 ((n : ℝ) / (p : ℝ))) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg
    _ = centralPromotionMajorant n X := by
      simpa only [primes] using sum_prime_logb_eq_majorant n X hX

private theorem fixed_cutoff_geometry {n q : ℕ}
    (hq : 2 ≤ q) (hn : (2 * q) ^ 2 ≤ n) :
    let X := n / q
    X ≤ n ∧
      n ≤ 2 * q * X ∧
      2 * q ≤ X ∧
      0 < Real.log (X : ℝ) ∧
      Real.log (n : ℝ) ≤ 2 * Real.log (X : ℝ) ∧
      0 ≤ Real.log (n : ℝ) - Real.log (X : ℝ) ∧
      Real.log (n : ℝ) - Real.log (X : ℝ) ≤
        Real.log ((2 * q : ℕ) : ℝ) := by
  dsimp only
  have hqPos : 0 < q := by omega
  have hqTwoPos : 0 < 2 * q := by omega
  have hXge : 2 * q ≤ n / q := by
    apply (Nat.le_div_iff_mul_le hqPos).2
    nlinarith
  have hXPos : 0 < n / q := by omega
  have hnPos : 0 < n := by
    have : 0 < (2 * q) ^ 2 := by positivity
    omega
  have hXle : n / q ≤ n := Nat.div_le_self n q
  have hdivUpper : n < q * (n / q + 1) :=
    Nat.lt_mul_div_succ n hqPos
  have hnLe : n ≤ 2 * q * (n / q) := by
    nlinarith
  have hnSq : n ≤ (n / q) ^ 2 := by
    nlinarith
  have hXRealPos : (0 : ℝ) < (n / q : ℕ) := by exact_mod_cast hXPos
  have hnRealPos : (0 : ℝ) < n := by exact_mod_cast hnPos
  have hTwoQRealPos : (0 : ℝ) < (2 * q : ℕ) := by
    exact_mod_cast hqTwoPos
  have hlogXPos : 0 < Real.log ((n / q : ℕ) : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < n / q by omega)
  have hlogSq :
      Real.log (n : ℝ) ≤
        Real.log (((n / q : ℕ) : ℝ) ^ 2) := by
    apply Real.log_le_log hnRealPos
    exact_mod_cast hnSq
  rw [Real.log_pow] at hlogSq
  norm_num at hlogSq
  have hlogMono :
      Real.log ((n / q : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hXRealPos (by exact_mod_cast hXle)
  have hlogProd :
      Real.log (n : ℝ) ≤
        Real.log (((2 * q : ℕ) : ℝ) * ((n / q : ℕ) : ℝ)) := by
    apply Real.log_le_log hnRealPos
    exact_mod_cast hnLe
  rw [Real.log_mul hTwoQRealPos.ne' hXRealPos.ne'] at hlogProd
  exact ⟨hXle, hnLe, hXge, hlogXPos, hlogSq,
    sub_nonneg.mpr hlogMono, by linarith⟩

private theorem fixed_cutoff_div_log_bound {n q : ℕ}
    (hq : 2 ≤ q) (hn : (2 * q) ^ 2 ≤ n)
    {c : ℝ} (hc : 0 ≤ c) :
    c * (n / q : ℕ) / Real.log ((n / q : ℕ) : ℝ) ≤
      (2 * c / (q : ℝ)) * secondOrderScale n := by
  obtain ⟨hXle, _, hXge, hlogX, hlogSq, _, _⟩ :=
    fixed_cutoff_geometry hq hn
  have hnOne : 1 < n := by
    have hXOne : 1 < n / q := by omega
    omega
  have hlogN : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hnOne)
  have hcastDiv : ((n / q : ℕ) : ℝ) ≤
      (n : ℝ) / (q : ℝ) := Nat.cast_div_le
  have hinvLog :
      1 / Real.log ((n / q : ℕ) : ℝ) ≤
        2 / Real.log (n : ℝ) := by
    apply (div_le_iff₀ hlogX).2
    calc
      (1 : ℝ) ≤
          (2 * Real.log ((n / q : ℕ) : ℝ)) /
            Real.log (n : ℝ) := (le_div_iff₀ hlogN).2 (by
              simpa only [one_mul] using hlogSq)
      _ = (2 / Real.log (n : ℝ)) *
          Real.log ((n / q : ℕ) : ℝ) := by ring
  rw [secondOrderScale]
  calc
    c * (n / q : ℕ) / Real.log ((n / q : ℕ) : ℝ) =
        c * ((n / q : ℕ) : ℝ) *
          (1 / Real.log ((n / q : ℕ) : ℝ)) := by ring
    _ ≤ c * ((n : ℝ) / (q : ℝ)) *
          (1 / Real.log ((n / q : ℕ) : ℝ)) := by
      gcongr
    _ ≤ c * ((n : ℝ) / (q : ℝ)) *
          (2 / Real.log (n : ℝ)) := by
      gcongr
    _ = (2 * c / (q : ℝ)) *
          ((n : ℝ) / Real.log (n : ℝ)) := by ring

/-- Uniform quantitative form of (4.11): one absolute constant controls
every fixed cutoff, and its coefficient tends to zero with the cutoff
parameter. -/
theorem residualPromotionCost_fixedCutoff_uniform_bound :
    ∃ K : ℝ, 0 < K ∧
      ∀ q : ℕ, 2 ≤ q →
        ∀ᶠ n : ℕ in atTop,
          (residualPromotionCost n (n / q) : ℝ) ≤
            (K * (1 + Real.log (q : ℝ)) / (q : ℝ)) *
              secondOrderScale n := by
  obtain ⟨C, hC, herror⟩ :=
    (isBigO_iff'.mp
      Chebyshev.primeCounting_sub_theta_div_log_isBigO)
  let A : ℝ := Real.log 4 + 1
  let K : ℝ :=
    4 * A + 2 * A / Real.log 2 + 2 * C / Real.log 2
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < A := by
    dsimp only [A]
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro q hq
  have hqPos : 0 < q := by omega
  have hcutoffTop :
      Tendsto (fun n : ℕ ↦ ((n / q : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.tendsto_div_const_atTop (n := q) hqPos.ne')
  have hprimeRaw := hcutoffTop.eventually
    (Chebyshev.eventually_primeCounting_le
      (by norm_num : (0 : ℝ) < 1))
  have herrorRaw := hcutoffTop.eventually herror
  have hprime :
      ∀ᶠ n : ℕ in atTop,
        (Nat.primeCounting (n / q) : ℝ) ≤
          A * ((n / q : ℕ) : ℝ) /
            Real.log ((n / q : ℕ) : ℝ) := by
    filter_upwards [hprimeRaw] with n hn
    simpa [A] using hn
  have hchebyshevError :
      ∀ᶠ n : ℕ in atTop,
        ‖(Nat.primeCounting (n / q) : ℝ) -
            Chebyshev.theta ((n / q : ℕ) : ℝ) /
              Real.log ((n / q : ℕ) : ℝ)‖ ≤
          C * ‖((n / q : ℕ) : ℝ) /
            Real.log ((n / q : ℕ) : ℝ) ^ 2‖ := by
    filter_upwards [herrorRaw] with n hn
    simpa using hn
  filter_upwards [hprime, hchebyshevError,
      eventually_ge_atTop ((2 * q) ^ 2)] with n hprimeN herrorN hn
  obtain ⟨hXle, _, _, hlogX, _, hdeltaNonneg, hdeltaUpper⟩ :=
    fixed_cutoff_geometry hq hn
  have hnOne : 1 < n := by
    have hXOne : 1 < n / q := by
      have htwoq : 2 * q ≤ n / q :=
        (fixed_cutoff_geometry hq hn).2.2.1
      omega
    omega
  have hscale : 0 < secondOrderScale n := by
    rw [secondOrderScale]
    exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hnOne))
  have hpiBound :
      (Nat.primeCounting (n / q) : ℝ) ≤
        (2 * A / (q : ℝ)) * secondOrderScale n :=
    hprimeN.trans (fixed_cutoff_div_log_bound hq hn hA.le)
  have herrorNorm :
      |(Nat.primeCounting (n / q) : ℝ) -
          Chebyshev.theta ((n / q : ℕ) : ℝ) /
            Real.log ((n / q : ℕ) : ℝ)| ≤
        C * (((n / q : ℕ) : ℝ) /
          Real.log ((n / q : ℕ) : ℝ) ^ 2) := by
    have hquotientNonneg :
        0 ≤ ((n / q : ℕ) : ℝ) /
          Real.log ((n / q : ℕ) : ℝ) ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hquotientNonneg] using herrorN
  have hthetaError :
      (Nat.primeCounting (n / q) : ℝ) *
            Real.log ((n / q : ℕ) : ℝ) -
          Chebyshev.theta ((n / q : ℕ) : ℝ) ≤
        (2 * C / (q : ℝ)) * secondOrderScale n := by
    calc
      (Nat.primeCounting (n / q) : ℝ) *
              Real.log ((n / q : ℕ) : ℝ) -
            Chebyshev.theta ((n / q : ℕ) : ℝ) =
          ((Nat.primeCounting (n / q) : ℝ) -
              Chebyshev.theta ((n / q : ℕ) : ℝ) /
                Real.log ((n / q : ℕ) : ℝ)) *
            Real.log ((n / q : ℕ) : ℝ) := by
              field_simp [hlogX.ne']
      _ ≤ |(Nat.primeCounting (n / q) : ℝ) -
              Chebyshev.theta ((n / q : ℕ) : ℝ) /
                Real.log ((n / q : ℕ) : ℝ)| *
            Real.log ((n / q : ℕ) : ℝ) := by
              gcongr
              exact le_abs_self _
      _ ≤ (C * (((n / q : ℕ) : ℝ) /
              Real.log ((n / q : ℕ) : ℝ) ^ 2)) *
            Real.log ((n / q : ℕ) : ℝ) := by
              gcongr
      _ = C * ((n / q : ℕ) : ℝ) /
            Real.log ((n / q : ℕ) : ℝ) := by
              field_simp [hlogX.ne']
      _ ≤ (2 * C / (q : ℝ)) * secondOrderScale n :=
        fixed_cutoff_div_log_bound hq hn hC.le
  have hlogTwoQ :
      Real.log ((2 * q : ℕ) : ℝ) =
        Real.log 2 + Real.log (q : ℝ) := by
    rw [show ((2 * q : ℕ) : ℝ) = 2 * (q : ℝ) by norm_num,
      Real.log_mul (by norm_num) (by exact_mod_cast hqPos.ne')]
  have hlogQNonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hlogTwoQNonneg : 0 ≤ Real.log ((2 * q : ℕ) : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * q by omega))
  have hpiDelta :
      (Nat.primeCounting (n / q) : ℝ) *
          (Real.log (n : ℝ) -
            Real.log ((n / q : ℕ) : ℝ)) ≤
        ((2 * A / (q : ℝ)) * secondOrderScale n) *
          Real.log ((2 * q : ℕ) : ℝ) := by
    calc
      (Nat.primeCounting (n / q) : ℝ) *
            (Real.log (n : ℝ) -
              Real.log ((n / q : ℕ) : ℝ)) ≤
          (Nat.primeCounting (n / q) : ℝ) *
            Real.log ((2 * q : ℕ) : ℝ) := by gcongr
      _ ≤ ((2 * A / (q : ℝ)) * secondOrderScale n) *
            Real.log ((2 * q : ℕ) : ℝ) := by gcongr
  have hmajorant :
      centralPromotionMajorant n (n / q) ≤
        (2 * A / (q : ℝ)) * secondOrderScale n +
          ((((2 * A / (q : ℝ)) * secondOrderScale n) *
              Real.log ((2 * q : ℕ) : ℝ) +
            (2 * C / (q : ℝ)) * secondOrderScale n) /
              Real.log 2) := by
    rw [centralPromotionMajorant]
    have hsplit :
        (Nat.primeCounting (n / q) : ℝ) * Real.log (n : ℝ) -
            Chebyshev.theta ((n / q : ℕ) : ℝ) =
          (Nat.primeCounting (n / q) : ℝ) *
              (Real.log (n : ℝ) -
                Real.log ((n / q : ℕ) : ℝ)) +
            ((Nat.primeCounting (n / q) : ℝ) *
                Real.log ((n / q : ℕ) : ℝ) -
              Chebyshev.theta ((n / q : ℕ) : ℝ)) := by ring
    rw [hsplit]
    exact add_le_add hpiBound
      (div_le_div_of_nonneg_right
        (add_le_add hpiDelta hthetaError) hlogTwo.le)
  have hcoefficient :
      2 * A +
          (2 * A * Real.log ((2 * q : ℕ) : ℝ) + 2 * C) /
            Real.log 2 ≤
        K * (1 + Real.log (q : ℝ)) := by
    have hdiff :
        K * (1 + Real.log (q : ℝ)) -
            (2 * A +
              (2 * A * Real.log ((2 * q : ℕ) : ℝ) + 2 * C) /
                Real.log 2) =
          (2 * A + (4 * A * Real.log 2 + 2 * C) *
              Real.log (q : ℝ)) / Real.log 2 := by
      dsimp only [K]
      rw [hlogTwoQ]
      field_simp [hlogTwo.ne']
      ring
    have hdiffNonneg :
        0 ≤ K * (1 + Real.log (q : ℝ)) -
            (2 * A +
              (2 * A * Real.log ((2 * q : ℕ) : ℝ) + 2 * C) /
                Real.log 2) := by
      rw [hdiff]
      positivity
    linarith
  have hcombined :
      (2 * A / (q : ℝ)) * secondOrderScale n +
          ((((2 * A / (q : ℝ)) * secondOrderScale n) *
              Real.log ((2 * q : ℕ) : ℝ) +
            (2 * C / (q : ℝ)) * secondOrderScale n) /
              Real.log 2) ≤
        (K * (1 + Real.log (q : ℝ)) / (q : ℝ)) *
          secondOrderScale n := by
    have hrearrange :
        (2 * A / (q : ℝ)) * secondOrderScale n +
            ((((2 * A / (q : ℝ)) * secondOrderScale n) *
                Real.log ((2 * q : ℕ) : ℝ) +
              (2 * C / (q : ℝ)) * secondOrderScale n) /
                Real.log 2) =
          ((2 * A +
              (2 * A * Real.log ((2 * q : ℕ) : ℝ) + 2 * C) /
                Real.log 2) / (q : ℝ)) * secondOrderScale n := by
      field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hqPos.ne', hlogTwo.ne']
    rw [hrearrange]
    gcongr
  exact (residualPromotionCost_cast_le_centralPromotionMajorant hXle).trans
    (hmajorant.trans hcombined)

private theorem one_add_log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun q : ℕ ↦ (1 + Real.log (q : ℝ)) / (q : ℝ))
      atTop (nhds 0) := by
  have hone :
      Tendsto (fun q : ℕ ↦ (1 : ℝ) / (q : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa only [add_div, add_zero] using
    hone.add log_natCast_div_natCast_tendsto_zero

/-- Real-budget terminal from (4.10)--(4.11).  For every positive tolerance,
one fixed `R ≥ 201` makes the actual residual promotion cost fit inside
that exact multiple of `n / log n`. -/
theorem residualPromotionCost_eventually_cast_le_mul
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        (residualPromotionCost n (n / (R + 1)) : ℝ) ≤
          epsilon * secondOrderScale n := by
  obtain ⟨K, hK, hbound⟩ :=
    residualPromotionCost_fixedCutoff_uniform_bound
  have hcoefficient :
      Tendsto
        (fun q : ℕ ↦
          K * (1 + Real.log (q : ℝ)) / (q : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero] using
      (tendsto_const_nhds.mul
        one_add_log_natCast_div_natCast_tendsto_zero :
          Tendsto
            (fun q : ℕ ↦
              K * ((1 + Real.log (q : ℝ)) / (q : ℝ)))
            atTop (nhds (K * 0)))
  have hsmall :
      ∀ᶠ q : ℕ in atTop,
        K * (1 + Real.log (q : ℝ)) / (q : ℝ) < epsilon :=
    hcoefficient.eventually (Iio_mem_nhds hepsilon)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  let q : ℕ := max N 202
  have hqLarge : 202 ≤ q := le_max_right N 202
  have hqSmall :
      K * (1 + Real.log (q : ℝ)) / (q : ℝ) < epsilon :=
    hN q (le_max_left N 202)
  have hfixed := hbound q (by omega)
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (residualPromotionCost n (n / q) : ℝ) ≤
          epsilon * secondOrderScale n := by
    filter_upwards [hfixed, eventually_gt_atTop 1] with n hcost hn
    have hscale : 0 < secondOrderScale n := by
      rw [secondOrderScale]
      exact div_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
    exact hcost.trans
      (mul_le_mul_of_nonneg_right hqSmall.le hscale.le)
  refine ⟨q - 1, by omega, ?_⟩
  have hqEq : q - 1 + 1 = q := by omega
  simpa only [hqEq] using hevent

/-- Integral ceiling form of the terminal promotion budget, with the same
fixed cutoff choice as the real-budget theorem. -/
theorem residualPromotionCost_eventually_le_ceil
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        residualPromotionCost n (n / (R + 1)) ≤
          Nat.ceil (epsilon * secondOrderScale n) := by
  obtain ⟨R, hR, hreal⟩ :=
    residualPromotionCost_eventually_cast_le_mul hepsilon
  refine ⟨R, hR, ?_⟩
  filter_upwards [hreal] with n hn
  have hceil :
      epsilon * secondOrderScale n ≤
        (Nat.ceil (epsilon * secondOrderScale n) : ℝ) :=
    Nat.le_ceil _
  exact_mod_cast hn.trans hceil

end

end Erdos390.WholePaper
