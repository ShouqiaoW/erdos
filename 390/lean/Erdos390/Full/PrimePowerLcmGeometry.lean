import Erdos390.Full.LocalFugacityBounds
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# Diagonal prime-power lcm geometry

For the physical-tilt transfer, the diagonal `JJ` orientation contains the
joint divisibility scale `lcm(p^k,p^l)`.  The number of ordered exponent
pairs whose maximum is `r` is exactly `2r-3`.  The identities below keep
that shell multiplicity literal and then invoke the already proved
arithmetic--geometric diagonal mass.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerLcmGeometry

open ArithmeticModel LocalFugacityBounds

noncomputable section

theorem lcm_pow_pow_eq_pow_max (p k l : ℕ) :
    Nat.lcm (p ^ k) (p ^ l) = p ^ max k l := by
  rcases le_total k l with hkl | hlk
  · rw [max_eq_right hkl, Nat.lcm_eq_right_iff_dvd]
    exact pow_dvd_pow p hkl
  · rw [max_eq_left hlk, Nat.lcm_eq_left_iff_dvd]
    exact pow_dvd_pow p hlk

/-- Exact finite shell decomposition of the diagonal reciprocal-lcm sum. -/
theorem sum_highExponents_pair_inv_lcm_eq_diagonalWeight
    (p A : ℕ) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r := by
  induction A with
  | zero => simp [highExponents]
  | succ A ih =>
      cases A with
      | zero => norm_num [highExponents]
      | succ A =>
          let T := Finset.Icc 2 (Nat.succ A)
          let R := Nat.succ (Nat.succ A)
          have hT : highExponents (Nat.succ A) = T := rfl
          have hR : highExponents R = insert R T := by
            apply Finset.ext
            intro x
            simp only [highExponents, T, R, Finset.mem_Icc,
              Finset.mem_insert]
            omega
          have hRT : R ∉ T := by
            dsimp only [R, T]
            simp
          have hkle (k : ℕ) (hk : k ∈ T) : k ≤ R := by
            have hk' := (Finset.mem_Icc.mp hk).2
            dsimp only [R]
            omega
          have hlcmLeft (k : ℕ) (hk : k ∈ T) :
              Nat.lcm (p ^ R) (p ^ k) = p ^ R := by
            rw [lcm_pow_pow_eq_pow_max, max_eq_left (hkle k hk)]
          have hlcmRight (k : ℕ) (hk : k ∈ T) :
              Nat.lcm (p ^ k) (p ^ R) = p ^ R := by
            rw [lcm_pow_pow_eq_pow_max, max_eq_right (hkle k hk)]
          have hcard : T.card = A := by
            dsimp only [T]
            simp
          change
            (∑ k ∈ highExponents R, ∑ l ∈ highExponents R,
                1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
              ∑ r ∈ highExponents R,
                ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r
          rw [hR]
          simp only [Finset.sum_insert hRT]
          rw [show
            (∑ l ∈ T, 1 / (Nat.lcm (p ^ R) (p ^ l) : ℝ)) =
                (T.card : ℝ) * (1 / (p : ℝ) ^ R) by
              calc
                (∑ l ∈ T, 1 / (Nat.lcm (p ^ R) (p ^ l) : ℝ)) =
                    ∑ _l ∈ T, 1 / (p : ℝ) ^ R := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  rw [hlcmLeft l hl]
                  norm_num only [Nat.cast_pow]
                _ = (T.card : ℝ) * (1 / (p : ℝ) ^ R) := by simp]
          rw [show
            (∑ k ∈ T,
                (1 / (Nat.lcm (p ^ k) (p ^ R) : ℝ) +
                  ∑ l ∈ T, 1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ))) =
              (T.card : ℝ) * (1 / (p : ℝ) ^ R) +
                ∑ k ∈ T, ∑ l ∈ T,
                  1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) by
            rw [Finset.sum_add_distrib]
            congr 1
            calc
              (∑ k ∈ T, 1 / (Nat.lcm (p ^ k) (p ^ R) : ℝ)) =
                  ∑ _k ∈ T, 1 / (p : ℝ) ^ R := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hlcmRight k hk]
                norm_num only [Nat.cast_pow]
              _ = (T.card : ℝ) * (1 / (p : ℝ) ^ R) := by simp]
          have ih' :
              (∑ k ∈ T, ∑ l ∈ T,
                  1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
                ∑ r ∈ T,
                  ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r := by
            simpa only [hT] using ih
          rw [ih', hcard]
          have hself : Nat.lcm (p ^ R) (p ^ R) = p ^ R := by simp
          rw [hself]
          norm_num only [Nat.cast_pow]
          have hweight : 2 * R - 3 = 2 * A + 1 := by
            dsimp only [R]
            omega
          rw [hweight]
          push_cast
          ring

/-- The diagonal reciprocal-lcm ledger has a fixed `p^{-2}` bound. -/
theorem sum_highExponents_pair_inv_lcm_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  rw [sum_highExponents_pair_inv_lcm_eq_diagonalWeight]
  calc
    (∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) ≤
      ∑ r ∈ highExponents A,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hden : 0 ≤ (p : ℝ) ^ r := by positivity
        have hw : 0 ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
        have hr0 : 0 ≤ (r : ℝ) := by positivity
        calc
          ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r =
              ((2 * r - 3 : ℕ) : ℝ) *
                (1 / (p : ℝ) ^ r) := by ring
          _ ≤ ((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
            apply mul_le_mul_of_nonneg_left _ hw
            exact div_le_div_of_nonneg_right (by linarith) hden
    _ ≤ quadraticHalfMass / (p : ℝ) ^ 2 :=
      sum_diagonalWeight_raddone_inv_pow_le hp.two_le

/-- The corresponding product-denominator double tail factors and is
bounded by `4 p^{-4}`. -/
theorem sum_highExponents_pair_inv_product_le
    {p A : ℕ} (hp : p.Prime) :
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ)) ≤
      4 / (p : ℝ) ^ 4 := by
  have htail :
      (∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ)) ≤
        2 / (p : ℝ) ^ 2 := by
    simpa only [highExponents] using
      (sum_inv_pow_tail_le (p := p) (r := 1) (A := A) hp.two_le)
  have htail0 :
      0 ≤ ∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ) := by positivity
  calc
    (∑ k ∈ highExponents A, ∑ l ∈ highExponents A,
        1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ)) =
      (∑ k ∈ highExponents A, 1 / ((p ^ k : ℕ) : ℝ)) *
        (∑ l ∈ highExponents A, 1 / ((p ^ l : ℕ) : ℝ)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l hl
          norm_num only [Nat.cast_mul]
          ring
    _ ≤ (2 / (p : ℝ) ^ 2) * (2 / (p : ℝ) ^ 2) :=
      mul_le_mul htail htail htail0 (by positivity)
    _ = 4 / (p : ℝ) ^ 4 := by ring

end

end Erdos390.Full.PrimePowerLcmGeometry
