import Erdos390.WholePaper.PrimeLayerCounts
import Mathlib.NumberTheory.Bertrand

/-!
# A finite Nagura certificate and an asymptotic Nagura tail

Nagura's theorem says that every integer `n ≥ 25` has a prime `p` with
`n < p < 6n/5`.  The available assumption-free Mathlib theorem on explicit
prime intervals is Bertrand's postulate.  For the infinite tail we use the
assumption-free prime number theorem exported by `SafePrimeCounting`; the
stronger explicit results in the optional `PrimeNumberTheoremAnd` dependency
are not proof-complete and are deliberately not imported here.

This file proves the Nagura conclusion unconditionally on the complete
finite range `25 ≤ n < 91639`.  The certificate is a chain of actual primes;
successive entries `a,b` satisfy `5b < 6a`, so their covered integer
intervals overlap.  It also proves that the Nagura conclusion holds for all
sufficiently large integers and records the exact reduction of the full
theorem to a concrete tail, together with the transfer from a Nagura witness
to the ratio for consecutive primes.
-/

open Filter Topology

namespace Erdos390.WholePaper

/-- The exact natural-number form of the prime interval used in Section 4. -/
def HasNaguraPrime (n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ n < p ∧ 5 * p < 6 * n

/-- A kernel-checked finite Nagura certificate.  The upper endpoint exceeds
the cutoff `2103` in Nagura's original analytic proof. -/
theorem exists_prime_nagura_finite {n : ℕ} (hnLower : 25 ≤ n)
    (hnUpper : n < 2423) : HasNaguraPrime n := by
  by_cases h29 : n < 29
  · exact ⟨29, by norm_num, h29, by omega⟩
  by_cases h31 : n < 31
  · exact ⟨31, by norm_num, h31, by omega⟩
  by_cases h37 : n < 37
  · exact ⟨37, by norm_num, h37, by omega⟩
  by_cases h43 : n < 43
  · exact ⟨43, by norm_num, h43, by omega⟩
  by_cases h47 : n < 47
  · exact ⟨47, by norm_num, h47, by omega⟩
  by_cases h53 : n < 53
  · exact ⟨53, by norm_num, h53, by omega⟩
  by_cases h61 : n < 61
  · exact ⟨61, by norm_num, h61, by omega⟩
  by_cases h73 : n < 73
  · exact ⟨73, by norm_num, h73, by omega⟩
  by_cases h83 : n < 83
  · exact ⟨83, by norm_num, h83, by omega⟩
  by_cases h97 : n < 97
  · exact ⟨97, by norm_num, h97, by omega⟩
  by_cases h113 : n < 113
  · exact ⟨113, by norm_num, h113, by omega⟩
  by_cases h131 : n < 131
  · exact ⟨131, by norm_num, h131, by omega⟩
  by_cases h157 : n < 157
  · exact ⟨157, by norm_num, h157, by omega⟩
  by_cases h181 : n < 181
  · exact ⟨181, by norm_num, h181, by omega⟩
  by_cases h211 : n < 211
  · exact ⟨211, by norm_num, h211, by omega⟩
  by_cases h251 : n < 251
  · exact ⟨251, by norm_num, h251, by omega⟩
  by_cases h293 : n < 293
  · exact ⟨293, by norm_num, h293, by omega⟩
  by_cases h349 : n < 349
  · exact ⟨349, by norm_num, h349, by omega⟩
  by_cases h409 : n < 409
  · exact ⟨409, by norm_num, h409, by omega⟩
  by_cases h487 : n < 487
  · exact ⟨487, by norm_num, h487, by omega⟩
  by_cases h577 : n < 577
  · exact ⟨577, by norm_num, h577, by omega⟩
  by_cases h691 : n < 691
  · exact ⟨691, by norm_num, h691, by omega⟩
  by_cases h829 : n < 829
  · exact ⟨829, by norm_num, h829, by omega⟩
  by_cases h991 : n < 991
  · exact ⟨991, by norm_num, h991, by omega⟩
  by_cases h1187 : n < 1187
  · exact ⟨1187, by norm_num, h1187, by omega⟩
  by_cases h1423 : n < 1423
  · exact ⟨1423, by norm_num, h1423, by omega⟩
  by_cases h1699 : n < 1699
  · exact ⟨1699, by norm_num, h1699, by omega⟩
  by_cases h2029 : n < 2029
  · exact ⟨2029, by norm_num, h2029, by omega⟩
  exact ⟨2423, by norm_num, hnUpper, by omega⟩

/-- A second kernel-checked prime chain bridges the original finite
certificate past `89693`, the threshold in Dusart's explicit interval
estimate.  No result from the incomplete Dusart module is imported. -/
theorem exists_prime_nagura_medium {n : ℕ} (hnLower : 2423 ≤ n)
    (hnUpper : n < 91639) : HasNaguraPrime n := by
  by_cases h2903 : n < 2903
  · exact ⟨2903, by norm_num, h2903, by omega⟩
  by_cases h3469 : n < 3469
  · exact ⟨3469, by norm_num, h3469, by omega⟩
  by_cases h4159 : n < 4159
  · exact ⟨4159, by norm_num, h4159, by omega⟩
  by_cases h4987 : n < 4987
  · exact ⟨4987, by norm_num, h4987, by omega⟩
  by_cases h5981 : n < 5981
  · exact ⟨5981, by norm_num, h5981, by omega⟩
  by_cases h7177 : n < 7177
  · exact ⟨7177, by norm_num, h7177, by omega⟩
  by_cases h8609 : n < 8609
  · exact ⟨8609, by norm_num, h8609, by omega⟩
  by_cases h10321 : n < 10321
  · exact ⟨10321, by norm_num, h10321, by omega⟩
  by_cases h12379 : n < 12379
  · exact ⟨12379, by norm_num, h12379, by omega⟩
  by_cases h14851 : n < 14851
  · exact ⟨14851, by norm_num, h14851, by omega⟩
  by_cases h17807 : n < 17807
  · exact ⟨17807, by norm_num, h17807, by omega⟩
  by_cases h21347 : n < 21347
  · exact ⟨21347, by norm_num, h21347, by omega⟩
  by_cases h25609 : n < 25609
  · exact ⟨25609, by norm_num, h25609, by omega⟩
  by_cases h30727 : n < 30727
  · exact ⟨30727, by norm_num, h30727, by omega⟩
  by_cases h36871 : n < 36871
  · exact ⟨36871, by norm_num, h36871, by omega⟩
  by_cases h44221 : n < 44221
  · exact ⟨44221, by norm_num, h44221, by omega⟩
  by_cases h53051 : n < 53051
  · exact ⟨53051, by norm_num, h53051, by omega⟩
  by_cases h63659 : n < 63659
  · exact ⟨63659, by norm_num, h63659, by omega⟩
  by_cases h76387 : n < 76387
  · exact ⟨76387, by norm_num, h76387, by omega⟩
  exact ⟨91639, by norm_num, hnUpper, by omega⟩

/-- Combined unconditional certificate through the explicit-estimate
threshold. -/
theorem exists_prime_nagura_below_91639 {n : ℕ} (hnLower : 25 ≤ n)
    (hnUpper : n < 91639) : HasNaguraPrime n := by
  by_cases h : n < 2423
  · exact exists_prime_nagura_finite hnLower h
  · exact exists_prime_nagura_medium (by omega) hnUpper

/-- The prime-count difference in the stronger interval `(n, 7n/6]` is
eventually positive.  Choosing `7/6 < 6/5` avoids the integral upper-endpoint
case in the strict Nagura inequality. -/
theorem eventually_primeCounting_nagura_difference_pos :
    ∀ᶠ n : ℕ in atTop,
      0 < Nat.primeCounting ⌊((7 : ℝ) / 6) * (n : ℝ)⌋₊ -
        Nat.primeCounting n := by
  have hLimit :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : ℝ)) (b := (7 : ℝ) / 6) (by norm_num) (by norm_num)
  have hRatioPos : ∀ᶠ n : ℕ in atTop,
      0 <
        ((Nat.primeCounting ⌊((7 : ℝ) / 6) * (n : ℝ)⌋₊ -
            Nat.primeCounting n : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)) := by
    have hEventually := hLimit.eventually
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < (7 : ℝ) / 6 - 1))
    simpa using hEventually
  filter_upwards [hRatioPos, eventually_gt_atTop 1] with n hRatio hn
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hLogPos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hScalePos : 0 < (n : ℝ) / Real.log (n : ℝ) :=
    div_pos hnPos hLogPos
  have hCountReal :
      0 <
        ((Nat.primeCounting ⌊((7 : ℝ) / 6) * (n : ℝ)⌋₊ -
          Nat.primeCounting n : ℕ) : ℝ) :=
    (div_pos_iff_of_pos_right hScalePos).mp hRatio
  exact_mod_cast hCountReal

/-- The exact count difference requested for `(n, 6n/5]` is eventually
positive.  The narrower `7/6` interval above makes this an immediate
monotonicity consequence. -/
theorem eventually_primeCounting_six_fifths_difference_pos :
    ∀ᶠ n : ℕ in atTop,
      0 < Nat.primeCounting ⌊((6 : ℝ) / 5) * (n : ℝ)⌋₊ -
        Nat.primeCounting n := by
  filter_upwards [eventually_primeCounting_nagura_difference_pos] with n hCount
  apply Nat.sub_pos_iff_lt.mpr
  have hNarrow :
      Nat.primeCounting n <
        Nat.primeCounting ⌊((7 : ℝ) / 6) * (n : ℝ)⌋₊ :=
    Nat.sub_pos_iff_lt.mp hCount
  have hArg :
      ((7 : ℝ) / 6) * (n : ℝ) ≤ ((6 : ℝ) / 5) * (n : ℝ) := by
    exact mul_le_mul_of_nonneg_right (by norm_num) (Nat.cast_nonneg n)
  exact hNarrow.trans_le (Nat.monotone_primeCounting (Nat.floor_mono hArg))

/-- Every sufficiently large natural number has a prime in the strict
Nagura interval. -/
theorem eventually_exists_prime_nagura :
    ∀ᶠ n : ℕ in atTop, HasNaguraPrime n := by
  filter_upwards [eventually_primeCounting_nagura_difference_pos,
      eventually_gt_atTop 1] with n hCount hn
  let upper : ℕ := ⌊((7 : ℝ) / 6) * (n : ℝ)⌋₊
  have hPrimeCounting : Nat.primeCounting n < Nat.primeCounting upper := by
    exact Nat.sub_pos_iff_lt.mp hCount
  have hCounting :
      Nat.count Nat.Prime (n + 1) < Nat.count Nat.Prime (upper + 1) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using hPrimeCounting
  obtain ⟨p, hpInterval, hpPrime⟩ :=
    Nat.exists_of_count_lt_count (p := Nat.Prime) hCounting
  rcases hpInterval with ⟨hpLower, hpUpper⟩
  refine ⟨p, hpPrime, by omega, ?_⟩
  have hpUpper' : p ≤ upper := by omega
  have hArgNonneg :
      (0 : ℝ) ≤ ((7 : ℝ) / 6) * (n : ℝ) := by positivity
  have hpReal :
      (p : ℝ) ≤ ((7 : ℝ) / 6) * (n : ℝ) :=
    (Nat.le_floor_iff hArgNonneg).mp hpUpper'
  have hnPos : (0 : ℝ) < n := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hStrict : (5 : ℝ) * p < 6 * n := by
    nlinarith
  exact_mod_cast hStrict

/-- Existential cutoff form of the assumption-free asymptotic Nagura tail. -/
theorem exists_nagura_tail_cutoff :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasNaguraPrime n := by
  exact eventually_atTop.1 eventually_exists_prime_nagura

/-- The full Nagura theorem reduces exactly to the tail beginning at the
first endpoint not covered by `exists_prime_nagura_finite`. -/
theorem exists_prime_nagura_of_tail
    (hTail : ∀ n : ℕ, 91639 ≤ n → HasNaguraPrime n) :
    ∀ n : ℕ, 25 ≤ n → HasNaguraPrime n := by
  intro n hn
  by_cases h : n < 91639
  · exact exists_prime_nagura_below_91639 hn h
  · exact hTail n (by omega)

/-- A Nagura witness above `pPrev`, together with the assertion that `p` is
the least prime above `pPrev`, gives the scalar inequality used in the
allocation tail. -/
theorem consecutivePrime_ratio_of_naguraWitness {pPrev p : ℕ}
    (hLeast : ∀ q : ℕ, q.Prime → pPrev < q → p ≤ q)
    (hNagura : HasNaguraPrime pPrev) :
    5 * p < 6 * pPrev := by
  obtain ⟨q, hqPrime, hPrevQ, hqRatio⟩ := hNagura
  have hpq : p ≤ q := hLeast q hqPrime hPrevQ
  omega

/-- Exact consecutive-prime consequence on the certified finite range.
The hypotheses say literally that `pPrev < p` are consecutive primes. -/
theorem consecutivePrimes_ratio_finite {pPrev p : ℕ}
    (hConsecutive : pPrev.Prime ∧ p.Prime ∧ pPrev < p ∧
      ∀ q : ℕ, q.Prime → pPrev < q → q < p → False)
    (hpLower : 401 < p) (hpUpper : p ≤ 91639) :
    5 * p < 6 * pPrev := by
  obtain ⟨_hPrevPrime, _hpPrime, hPrevLt, hNoBetween⟩ := hConsecutive
  have hLeast : ∀ q : ℕ, q.Prime → pPrev < q → p ≤ q := by
    intro q hqPrime hPrevQ
    have hnqp : ¬q < p := fun hqp ↦ hNoBetween q hqPrime hPrevQ hqp
    omega
  have hPrevLower : 401 ≤ pPrev := by
    by_cases h : 401 ≤ pPrev
    · exact h
    · have hp401 : p ≤ 401 := hLeast 401 (by norm_num) (by omega)
      omega
  have hPrevUpper : pPrev < 91639 := hPrevLt.trans_le hpUpper
  exact consecutivePrime_ratio_of_naguraWitness hLeast
    (exists_prime_nagura_below_91639 (by omega) hPrevUpper)

end Erdos390.WholePaper
