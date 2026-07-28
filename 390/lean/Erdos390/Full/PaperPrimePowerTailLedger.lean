import Erdos390.Full.PaperValuationCutoff
import Erdos390.Full.PowerLedger

/-!
# Actual prime-power tail and endpoint ledgers

This module closes the finite arithmetic part of the beyond-four-mark
argument in paper Lemma 7.5.  The exponent sets are the actual logarithmic
valuation cutoffs, the primes belong to the actual finite band cut off by
`yNat`, and the four-mark boundary is the literal integer inequality
`yNat n ^ 4 < D`.  No asymptotic `O` notation is used in the statements.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailLedger

open ArithmeticModel Scale ValuationCutoff PaperValuationCutoff

noncomputable section

/-- Exponents in the `J_p I_q` orientation whose forced modulus is beyond
the actual four-mark range. -/
def jiBeyondFour (n p q A : ℕ) : Finset ℕ :=
  (highExponents A).filter (fun r ↦ yNat n ^ 4 < p ^ r * q)

/-- The transposed `I_p J_q` tail. -/
def ijBeyondFour (n p q A : ℕ) : Finset ℕ :=
  (highExponents A).filter (fun s ↦ yNat n ^ 4 < p * q ^ s)

/-- Exponent pairs in the `J_p J_q` orientation beyond the actual
four-mark range. -/
def jjBeyondFour (n p q A B : ℕ) : Finset (ℕ × ℕ) :=
  ((highExponents A).product (highExponents B)).filter
    (fun rs ↦ yNat n ^ 4 < p ^ rs.1 * q ^ rs.2)

/-- The diagonal high-power tail beyond four marks. -/
def diagonalBeyondFour (n p A : ℕ) : Finset ℕ :=
  (highExponents A).filter (fun r ↦ yNat n ^ 4 < p ^ r)

lemma card_highExponents_le (A : ℕ) : (highExponents A).card ≤ A := by
  simp [highExponents]

lemma card_jiBeyondFour_le (n p q A : ℕ) :
    (jiBeyondFour n p q A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

lemma card_ijBeyondFour_le (n p q A : ℕ) :
    (ijBeyondFour n p q A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

lemma card_jjBeyondFour_le (n p q A B : ℕ) :
    (jjBeyondFour n p q A B).card ≤ A * B := by
  calc
    (jjBeyondFour n p q A B).card ≤
        ((highExponents A).product (highExponents B)).card :=
      Finset.card_filter_le _ _
    _ = (highExponents A).card * (highExponents B).card :=
      Finset.card_product _ _
    _ ≤ A * B := Nat.mul_le_mul (card_highExponents_le A)
      (card_highExponents_le B)

lemma card_diagonalBeyondFour_le (n p A : ℕ) :
    (diagonalBeyondFour n p A).card ≤ A := by
  exact (Finset.card_filter_le _ _).trans (card_highExponents_le A)

/-- A `JI` modulus beyond `yNat^4` has at least one full extra factor
`yNat` after its first two `p` marks. -/
lemma yNat_lt_pow_sub_two_of_jiBeyondFour
    {n p q A r : ℕ} (hr : r ∈ jiBeyondFour n p q A)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n < p ^ (r - 2) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hfour : yNat n ^ 4 < p ^ r * q := (Finset.mem_filter.mp hr).2
  by_contra hnot
  have hexcess : p ^ (r - 2) ≤ yNat n := Nat.le_of_not_gt hnot
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hfactor : p ^ r = p ^ (r - 2) * p ^ 2 := by
    calc
      p ^ r = p ^ ((r - 2) + 2) := by
        congr 1
        omega
      _ = p ^ (r - 2) * p ^ 2 := pow_add _ _ _
  have hupper : p ^ r * q ≤ yNat n ^ 4 := by
    calc
      p ^ r * q = (p ^ (r - 2) * p ^ 2) * q := by rw [hfactor]
      _ ≤ (yNat n * yNat n ^ 2) * yNat n :=
        Nat.mul_le_mul (Nat.mul_le_mul hexcess hp2) hqY
      _ = yNat n ^ 4 := by ring
  omega

/-- Transposed one-high-power excess. -/
lemma yNat_lt_pow_sub_two_of_ijBeyondFour
    {n p q A s : ℕ} (hs : s ∈ ijBeyondFour n p q A)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n < q ^ (s - 2) := by
  have hs2 : 2 ≤ s := (mem_highExponents.mp (Finset.mem_filter.mp hs).1).1
  have hfour : yNat n ^ 4 < p * q ^ s := (Finset.mem_filter.mp hs).2
  by_contra hnot
  have hexcess : q ^ (s - 2) ≤ yNat n := Nat.le_of_not_gt hnot
  have hq2 : q ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hqY 2
  have hfactor : q ^ s = q ^ 2 * q ^ (s - 2) := by
    calc
      q ^ s = q ^ (2 + (s - 2)) := by
        congr 1
        omega
      _ = q ^ 2 * q ^ (s - 2) := pow_add _ _ _
  have hupper : p * q ^ s ≤ yNat n ^ 4 := by
    calc
      p * q ^ s = p * (q ^ 2 * q ^ (s - 2)) := by rw [hfactor]
      _ ≤ yNat n * (yNat n ^ 2 * yNat n) :=
        Nat.mul_le_mul hpY (Nat.mul_le_mul hq2 hexcess)
      _ = yNat n ^ 4 := by ring
  omega

/-- Pointwise reciprocal bound for a literal `JI` tail exponent. -/
lemma jiBeyondFour_reciprocal_le
    {n p q A r : ℕ} (hr : r ∈ jiBeyondFour n p q A)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) ^ r * (q : ℝ)) ≤
      1 / ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hexcess := yNat_lt_pow_sub_two_of_jiBeyondFour hr hpY hqY
  have hfactor : (p : ℝ) ^ r * (q : ℝ) =
      ((p : ℝ) ^ 2 * (q : ℝ)) * (p : ℝ) ^ (r - 2) := by
    calc
      (p : ℝ) ^ r * (q : ℝ) =
          (p : ℝ) ^ (2 + (r - 2)) * (q : ℝ) := by
            congr 2
            omega
      _ = ((p : ℝ) ^ 2 * (q : ℝ)) * (p : ℝ) ^ (r - 2) := by
        rw [pow_add]
        ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  gcongr
  exact_mod_cast hexcess.le

/-- Pointwise reciprocal bound in the transposed orientation. -/
lemma ijBeyondFour_reciprocal_le
    {n p q A s : ℕ} (hs : s ∈ ijBeyondFour n p q A)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) * (q : ℝ) ^ s) ≤
      1 / ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  have hs2 : 2 ≤ s := (mem_highExponents.mp (Finset.mem_filter.mp hs).1).1
  have hexcess := yNat_lt_pow_sub_two_of_ijBeyondFour hs hpY hqY
  have hfactor : (p : ℝ) * (q : ℝ) ^ s =
      ((p : ℝ) * (q : ℝ) ^ 2) * (q : ℝ) ^ (s - 2) := by
    calc
      (p : ℝ) * (q : ℝ) ^ s =
          (p : ℝ) * (q : ℝ) ^ (2 + (s - 2)) := by
            congr 2
            omega
      _ = ((p : ℝ) * (q : ℝ) ^ 2) * (q : ℝ) ^ (s - 2) := by
        rw [pow_add]
        ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  gcongr
  exact_mod_cast hexcess.le

/-- The complete finite `JI` reciprocal tail: the only multiplicity loss is
the actual exponent cutoff. -/
theorem sum_jiBeyondFour_reciprocal_le
    {n p q A : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ r ∈ jiBeyondFour n p q A,
        1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
      (A : ℝ) /
        ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))
  calc
    (∑ r ∈ jiBeyondFour n p q A,
        1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
        ∑ _r ∈ jiBeyondFour n p q A, K := by
      apply Finset.sum_le_sum
      intro r hr
      exact jiBeyondFour_reciprocal_le hr hp0 hq0 hY0 hpY hqY
    _ = ((jiBeyondFour n p q A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_jiBeyondFour_le n p q A) (by positivity)
    _ = (A : ℝ) /
        ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- The complete finite `IJ` reciprocal tail. -/
theorem sum_ijBeyondFour_reciprocal_le
    {n p q A : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ s ∈ ijBeyondFour n p q A,
        1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
      (A : ℝ) /
        ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))
  calc
    (∑ s ∈ ijBeyondFour n p q A,
        1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
        ∑ _s ∈ ijBeyondFour n p q A, K := by
      apply Finset.sum_le_sum
      intro s hs
      exact ijBeyondFour_reciprocal_le hs hp0 hq0 hY0 hpY hqY
    _ = ((ijBeyondFour n p q A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_ijBeyondFour_le n p q A) (by positivity)
    _ = (A : ℝ) /
        ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- Taking a positive cube root converts the integer inequality
`Y^2 < D^3` into the exact `Y^(2/3) < D` scale used in the paper's `JJ`
tail. -/
lemma rpow_two_thirds_lt_of_sq_lt_cube {Y D : ℕ}
    (hY0 : 0 < Y) (hD0 : 0 < D) (h : Y ^ 2 < D ^ 3) :
    (Y : ℝ) ^ (2 / 3 : ℝ) < (D : ℝ) := by
  have hcast : (Y : ℝ) ^ 2 < (D : ℝ) ^ 3 := by exact_mod_cast h
  have hr := Real.rpow_lt_rpow (show 0 ≤ (Y : ℝ) ^ 2 by positivity)
    hcast (show 0 < (1 / 3 : ℝ) by norm_num)
  have hleft : ((Y : ℝ) ^ 2) ^ (1 / 3 : ℝ) =
      (Y : ℝ) ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (show 0 ≤ (Y : ℝ) by positivity)]
    congr 1
    norm_num
  have hright : ((D : ℝ) ^ 3) ^ (1 / 3 : ℝ) = (D : ℝ) := by
    simpa [one_div] using Real.pow_rpow_inv_natCast
      (show 0 ≤ (D : ℝ) by positivity) (show (3 : ℕ) ≠ 0 by norm_num)
  rw [hleft, hright] at hr
  exact hr

private lemma pow_le_excess_cube {p r : ℕ} (hp0 : 0 < p) (hr3 : 3 ≤ r) :
    p ^ r ≤ (p ^ (r - 2)) ^ 3 := by
  calc
    p ^ r ≤ p ^ ((r - 2) * 3) :=
      Nat.pow_le_pow_right hp0 (by omega)
    _ = (p ^ (r - 2)) ^ 3 := pow_mul _ _ _

/-- Every literal `JJ` tail pair has excess prime-power product larger
than `yNat^(2/3)`.  The proof treats the one-high and two-high exponent
orientations separately, exactly as in the paper. -/
lemma yNat_sq_lt_excess_cube_of_jjBeyondFour
    {n p q A B r s : ℕ} (hrs : (r, s) ∈ jjBeyondFour n p q A B)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    yNat n ^ 2 < (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by
  have hrs' := Finset.mem_filter.mp hrs
  have hrmem : r ∈ highExponents A := (Finset.mem_product.mp hrs'.1).1
  have hsmem : s ∈ highExponents B := (Finset.mem_product.mp hrs'.1).2
  have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
  have hs2 : 2 ≤ s := (mem_highExponents.mp hsmem).1
  have hfour : yNat n ^ 4 < p ^ r * q ^ s := hrs'.2
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hq2 : q ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hqY 2
  by_cases hrEq : r = 2
  · subst r
    have hsNe : s ≠ 2 := by
      intro hsEq
      subst s
      have hupper : p ^ 2 * q ^ 2 ≤ yNat n ^ 4 := by
        calc
          p ^ 2 * q ^ 2 ≤ yNat n ^ 2 * yNat n ^ 2 :=
            Nat.mul_le_mul hp2 hq2
          _ = yNat n ^ 4 := by ring
      omega
    have hs3 : 3 ≤ s := by omega
    have hqPow : yNat n ^ 2 < q ^ s := by
      by_contra hnot
      have hqPowLe : q ^ s ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
      have hupper : p ^ 2 * q ^ s ≤ yNat n ^ 4 := by
        calc
          p ^ 2 * q ^ s ≤ yNat n ^ 2 * yNat n ^ 2 :=
            Nat.mul_le_mul hp2 hqPowLe
          _ = yNat n ^ 4 := by ring
      omega
    have hqCube := pow_le_excess_cube hq0 hs3
    simpa using hqPow.trans_le hqCube
  · have hr3 : 3 ≤ r := by omega
    by_cases hsEq : s = 2
    · subst s
      have hpPow : yNat n ^ 2 < p ^ r := by
        by_contra hnot
        have hpPowLe : p ^ r ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
        have hupper : p ^ r * q ^ 2 ≤ yNat n ^ 4 := by
          calc
            p ^ r * q ^ 2 ≤ yNat n ^ 2 * yNat n ^ 2 :=
              Nat.mul_le_mul hpPowLe hq2
            _ = yNat n ^ 4 := by ring
        omega
      have hpCube := pow_le_excess_cube hp0 hr3
      simpa using hpPow.trans_le hpCube
    · have hs3 : 3 ≤ s := by omega
      have hpCube := pow_le_excess_cube hp0 hr3
      have hqCube := pow_le_excess_cube hq0 hs3
      have htotalCube : p ^ r * q ^ s ≤
          (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by
        calc
          p ^ r * q ^ s ≤
              (p ^ (r - 2)) ^ 3 * (q ^ (s - 2)) ^ 3 :=
            Nat.mul_le_mul hpCube hqCube
          _ = (p ^ (r - 2) * q ^ (s - 2)) ^ 3 := by ring
      have hY24 : yNat n ^ 2 ≤ yNat n ^ 4 :=
        Nat.pow_le_pow_right hY0 (by norm_num)
      exact hY24.trans_lt (hfour.trans_le htotalCube)

/-- Pointwise `JJ` reciprocal tail with the exact two-thirds power. -/
lemma jjBeyondFour_reciprocal_le
    {n p q A B r s : ℕ} (hrs : (r, s) ∈ jjBeyondFour n p q A B)
    (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    1 / ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤
      1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
        (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  have hrs' := Finset.mem_filter.mp hrs
  have hrmem : r ∈ highExponents A := (Finset.mem_product.mp hrs'.1).1
  have hsmem : s ∈ highExponents B := (Finset.mem_product.mp hrs'.1).2
  have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
  have hs2 : 2 ≤ s := (mem_highExponents.mp hsmem).1
  have hexcessCube := yNat_sq_lt_excess_cube_of_jjBeyondFour
    hrs hp0 hq0 hY0 hpY hqY
  have hexcessPos : 0 < p ^ (r - 2) * q ^ (s - 2) := by positivity
  have hexcess := rpow_two_thirds_lt_of_sq_lt_cube hY0 hexcessPos hexcessCube
  have hfactor : (p : ℝ) ^ r * (q : ℝ) ^ s =
      ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) *
        ((p : ℝ) ^ (r - 2) * (q : ℝ) ^ (s - 2)) := by
    calc
      (p : ℝ) ^ r * (q : ℝ) ^ s =
          ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) *
            ((q : ℝ) ^ 2 * (q : ℝ) ^ (s - 2)) := by
              congr 2
              · rw [← pow_add]
                congr 1
                omega
              · rw [← pow_add]
                congr 1
                omega
      _ = ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) *
          ((p : ℝ) ^ (r - 2) * (q : ℝ) ^ (s - 2)) := by ring
  apply one_div_le_one_div_of_le (by positivity)
  rw [hfactor]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hexcess.le

/-- The complete finite `JJ` reciprocal tail, with precisely the product of
the two actual exponent cutoffs as multiplicity. -/
theorem sum_jjBeyondFour_reciprocal_le
    {n p q A B : ℕ} (hp0 : 0 < p) (hq0 : 0 < q) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) (hqY : q ≤ yNat n) :
    (∑ rs ∈ jjBeyondFour n p q A B,
        1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
      ((A : ℝ) * (B : ℝ)) /
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  let K : ℝ := 1 / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
    (yNat n : ℝ) ^ (2 / 3 : ℝ))
  calc
    (∑ rs ∈ jjBeyondFour n p q A B,
        1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
        ∑ _rs ∈ jjBeyondFour n p q A B, K := by
      apply Finset.sum_le_sum
      intro rs hrs
      exact jjBeyondFour_reciprocal_le hrs hp0 hq0 hY0 hpY hqY
    _ = ((jjBeyondFour n p q A B).card : ℝ) * K := by simp
    _ ≤ ((A : ℝ) * (B : ℝ)) * K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_jjBeyondFour_le n p q A B
    _ = ((A : ℝ) * (B : ℝ)) /
        ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
          (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
      simp [K, div_eq_mul_inv]

/-- A diagonal exponent beyond four marks has two complete extra factors
of `yNat` after the first two powers of `p`. -/
lemma yNat_sq_lt_pow_sub_two_of_diagonalBeyondFour
    {n p A r : ℕ} (hr : r ∈ diagonalBeyondFour n p A)
    (hpY : p ≤ yNat n) : yNat n ^ 2 < p ^ (r - 2) := by
  have hr2 : 2 ≤ r := (mem_highExponents.mp (Finset.mem_filter.mp hr).1).1
  have hfour : yNat n ^ 4 < p ^ r := (Finset.mem_filter.mp hr).2
  by_contra hnot
  have hexcess : p ^ (r - 2) ≤ yNat n ^ 2 := Nat.le_of_not_gt hnot
  have hp2 : p ^ 2 ≤ yNat n ^ 2 := Nat.pow_le_pow_left hpY 2
  have hfactor : p ^ r = p ^ 2 * p ^ (r - 2) := by
    calc
      p ^ r = p ^ (2 + (r - 2)) := by
        congr 1
        omega
      _ = p ^ 2 * p ^ (r - 2) := pow_add _ _ _
  have hupper : p ^ r ≤ yNat n ^ 4 := by
    calc
      p ^ r = p ^ 2 * p ^ (r - 2) := hfactor
      _ ≤ yNat n ^ 2 * yNat n ^ 2 := Nat.mul_le_mul hp2 hexcess
      _ = yNat n ^ 4 := by ring
  omega

/-- Complete diagonal reciprocal tail with the exact `(2r-3)` weight. -/
theorem sum_diagonalBeyondFour_weighted_reciprocal_le
    {n p A : ℕ} (hp0 : 0 < p) (hY0 : 0 < yNat n)
    (hpY : p ≤ yNat n) :
    (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      (2 * (A : ℝ) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  let K : ℝ := (2 * (A : ℝ)) /
    ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)
  have hpoint (r : ℕ) (hr : r ∈ diagonalBeyondFour n p A) :
      ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r ≤ K := by
    have hrmem : r ∈ highExponents A := (Finset.mem_filter.mp hr).1
    have hr2 : 2 ≤ r := (mem_highExponents.mp hrmem).1
    have hrA : r ≤ A := (mem_highExponents.mp hrmem).2
    have hexcess := yNat_sq_lt_pow_sub_two_of_diagonalBeyondFour hr hpY
    have hfactor : (p : ℝ) ^ r =
        (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
      calc
        (p : ℝ) ^ r = (p : ℝ) ^ (2 + (r - 2)) := by
          congr 1
          omega
        _ = (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := pow_add _ _ _
    have hrecip : 1 / (p : ℝ) ^ r ≤
        1 / ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [hfactor]
      gcongr
      exact_mod_cast hexcess.le
    have hweight : ((2 * r - 3 : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
      exact_mod_cast (show 2 * r - 3 ≤ 2 * A by omega)
    have hrecip' : ((p : ℝ) ^ r)⁻¹ ≤
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)⁻¹ := by
      simpa [one_div] using hrecip
    dsimp [K]
    rw [div_eq_mul_inv]
    exact mul_le_mul hweight hrecip' (by positivity) (by positivity)
  calc
    (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
        ∑ _r ∈ diagonalBeyondFour n p A, K := by
      apply Finset.sum_le_sum
      intro r hr
      exact hpoint r hr
    _ = ((diagonalBeyondFour n p A).card : ℝ) * K := by simp
    _ ≤ (A : ℝ) * K := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_diagonalBeyondFour_le n p A
    _ = (2 * (A : ℝ) ^ 2) /
        ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
      simp [K, div_eq_mul_inv]
      ring

/-! ## Literal endpoint multiplicities -/

/-- One endpoint error for every actual high exponent costs at most the
cutoff itself. -/
lemma sum_highExponents_const_le (A : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    (∑ _r ∈ highExponents A, E) ≤ (A : ℝ) * E := by
  calc
    (∑ _r ∈ highExponents A, E) =
        ((highExponents A).card : ℝ) * E := by simp
    _ ≤ (A : ℝ) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast card_highExponents_le A

/-- Literal endpoint multiplicity in the double-high `JJ` orientation. -/
lemma sum_highExponents_pair_const_le (A B : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    (∑ _r ∈ highExponents A, ∑ _s ∈ highExponents B, E) ≤
      ((A : ℝ) * (B : ℝ)) * E := by
  calc
    (∑ _r ∈ highExponents A, ∑ _s ∈ highExponents B, E) =
        (((highExponents A).card : ℝ) *
          ((highExponents B).card : ℝ)) * E := by simp; ring
    _ ≤ ((A : ℝ) * (B : ℝ)) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      exact_mod_cast Nat.mul_le_mul (card_highExponents_le A)
        (card_highExponents_le B)

/-- Literal diagonal endpoint multiplicity with the exact `(2r-3)`
weight.  The factor `2 A^2` is deliberately explicit. -/
lemma sum_highExponents_diagonalWeight_const_le
    (A : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    (∑ r ∈ highExponents A, ((2 * r - 3 : ℕ) : ℝ) * E) ≤
      2 * (A : ℝ) ^ 2 * E := by
  have hpoint (r : ℕ) (hr : r ∈ highExponents A) :
      ((2 * r - 3 : ℕ) : ℝ) * E ≤ (2 * (A : ℝ)) * E := by
    have hrA := (mem_highExponents.mp hr).2
    apply mul_le_mul_of_nonneg_right _ hE
    exact_mod_cast (show 2 * r - 3 ≤ 2 * A by omega)
  calc
    (∑ r ∈ highExponents A, ((2 * r - 3 : ℕ) : ℝ) * E) ≤
        ∑ _r ∈ highExponents A, (2 * (A : ℝ)) * E := by
      apply Finset.sum_le_sum
      intro r hr
      exact hpoint r hr
    _ = ((highExponents A).card : ℝ) * ((2 * (A : ℝ)) * E) := by simp
    _ ≤ (A : ℝ) * ((2 * (A : ℝ)) * E) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_highExponents_le A
    _ = 2 * (A : ℝ) ^ 2 * E := by ring

/-! ## Actual logarithmic cutoffs and paper-scale ledgers -/

/-- The exact exponent cutoff for one prime in the physical interval. -/
def actualExponentCutoff (C : ℝ) (n p : ℕ) : ℕ :=
  valuationCutoff p (physicalBound C n)

/-- The fixed cutoff coefficient `2 / log W`. -/
def cutoffScale (W : ℕ) : ℝ := 2 / Real.log (W : ℝ)

lemma cutoffScale_pos {W : ℕ} (hW : 1 < W) : 0 < cutoffScale W := by
  unfold cutoffScale
  exact div_pos (by norm_num) (Real.log_pos (by exact_mod_cast hW))

/-- The already-proved valuation-cutoff estimate in the multiplication form
used by every finite tail and endpoint ledger below. -/
theorem eventually_actualExponentCutoff_cast_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (actualExponentCutoff C n p : ℝ) ≤ cutoffScale W * L n := by
  filter_upwards [eventually_valuationCutoff_div_L_le_of_pos C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp
  have hL : 0 < L n := L_pos hn
  have hpCut := hcut p hp
  unfold actualExponentCutoff cutoffScale
  exact (div_le_iff₀ hL).mp hpCut

private lemma band_prime_data {n W p : ℕ} (hp : p ∈ primeBand n W) :
    0 < p ∧ 0 < yNat n ∧ p ≤ yNat n := by
  have hp0 : 0 < p := (prime_of_mem_primeBand hp).pos
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hp
  exact ⟨hp0, hp0.trans_le hpY, hpY⟩

/-- Paper-scale `JI` reciprocal tail with the actual valuation cutoff.  Its
coefficient depends on `W` but not on the tilt box. -/
theorem eventually_actual_ji_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ jiBeyondFour n p q (actualExponentCutoff C n p),
          1 / ((p : ℝ) ^ r * (q : ℝ))) ≤
        (cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  exact (sum_jiBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right (hcut p hp) (by positivity))

/-- Paper-scale transposed reciprocal tail. -/
theorem eventually_actual_ij_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ ijBeyondFour n p q (actualExponentCutoff C n q),
          1 / ((p : ℝ) * (q : ℝ) ^ s)) ≤
        (cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  exact (sum_ijBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right (hcut q hq) (by positivity))

/-- Paper-scale `JJ` reciprocal tail with the exact `yNat^(-2/3)` decay. -/
theorem eventually_actual_jj_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ rs ∈ jjBeyondFour n p q
          (actualExponentCutoff C n p) (actualExponentCutoff C n q),
          1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) ≤
        ((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ)) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp q hq
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  rcases band_prime_data hq with ⟨hq0, _, hqY⟩
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hnum :
      (actualExponentCutoff C n p : ℝ) *
          (actualExponentCutoff C n q : ℝ) ≤
        (cutoffScale W * L n) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hcut p hp) (hcut q hq) (by positivity) hscale0
  exact (sum_jjBeyondFour_reciprocal_le hp0 hq0 hY0 hpY hqY).trans
    (div_le_div_of_nonneg_right hnum (by positivity))

/-- Paper-scale weighted diagonal reciprocal tail. -/
theorem eventually_actual_diagonal_weighted_reciprocal_tail_le
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ diagonalBeyondFour n p (actualExponentCutoff C n p),
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
        (2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW]
    with n hcut
  intro p hp
  rcases band_prime_data hp with ⟨hp0, hY0, hpY⟩
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    (show 0 ≤ (actualExponentCutoff C n p : ℝ) by positivity).trans
      (hcut p hp)
  have hsq : (actualExponentCutoff C n p : ℝ) ^ 2 ≤
      (cutoffScale W * L n) ^ 2 := by
    exact (sq_le_sq₀ (by positivity) hscale0).2 (hcut p hp)
  apply (sum_diagonalBeyondFour_weighted_reciprocal_le hp0 hY0 hpY).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

/-- Literal one-high endpoint ledger (`JI` and, after transposition, `IJ`). -/
theorem eventually_actual_single_endpoint_ledger
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ _r ∈ highExponents (actualExponentCutoff C n p),
          1 / (n : ℝ)) ≤
        (cutoffScale W * L n) / (n : ℝ) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp
  have hnR : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  calc
    _ ≤ (actualExponentCutoff C n p : ℝ) * (1 / (n : ℝ)) :=
      sum_highExponents_const_le _ hnR
    _ ≤ (cutoffScale W * L n) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right (hcut p hp) hnR
    _ = (cutoffScale W * L n) / (n : ℝ) := by ring

/-- Literal double-high endpoint ledger. -/
theorem eventually_actual_jj_endpoint_ledger
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ _r ∈ highExponents (actualExponentCutoff C n p),
        ∑ _s ∈ highExponents (actualExponentCutoff C n q), 1 / (n : ℝ)) ≤
        ((cutoffScale W * L n) ^ 2) / (n : ℝ) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp q hq
  have hnR : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hnum :
      (actualExponentCutoff C n p : ℝ) *
          (actualExponentCutoff C n q : ℝ) ≤
        (cutoffScale W * L n) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hcut p hp) (hcut q hq) (by positivity) hscale0
  calc
    _ ≤ ((actualExponentCutoff C n p : ℝ) *
          (actualExponentCutoff C n q : ℝ)) * (1 / (n : ℝ)) :=
      sum_highExponents_pair_const_le _ _ hnR
    _ ≤ ((cutoffScale W * L n) ^ 2) * (1 / (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hnum hnR
    _ = ((cutoffScale W * L n) ^ 2) / (n : ℝ) := by ring

/-- Literal weighted diagonal endpoint ledger. -/
theorem eventually_actual_diagonal_endpoint_ledger
    (C : ℝ) (W : ℕ) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
          ((2 * r - 3 : ℕ) : ℝ) * (1 / (n : ℝ))) ≤
        (2 * (cutoffScale W * L n) ^ 2) / (n : ℝ) := by
  filter_upwards [eventually_actualExponentCutoff_cast_le C W hC hW,
    Filter.eventually_gt_atTop 1] with n hcut hn
  intro p hp
  have hnR : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  have hscale0 : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hsq : (actualExponentCutoff C n p : ℝ) ^ 2 ≤
      (cutoffScale W * L n) ^ 2 :=
    (sq_le_sq₀ (by positivity) hscale0).2 (hcut p hp)
  calc
    _ ≤ 2 * (actualExponentCutoff C n p : ℝ) ^ 2 * (1 / (n : ℝ)) :=
      sum_highExponents_diagonalWeight_const_le _ hnR
    _ ≤ 2 * (cutoffScale W * L n) ^ 2 * (1 / (n : ℝ)) := by
      gcongr
    _ = (2 * (cutoffScale W * L n) ^ 2) / (n : ℝ) := by ring

end

end Erdos390.Full.PaperPrimePowerTailLedger
