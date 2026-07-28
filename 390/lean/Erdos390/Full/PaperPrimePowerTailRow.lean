import Erdos390.Full.PaperPrimePowerFourDisplays

/-!
# The literal beyond-four residual row

The residual functions of the four pointwise displays are exactly supported
on the finite beyond-four exponent sets.  This file identifies those sums
and applies the previously proved actual-cutoff tail ledgers.
-/

open Filter
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerTailRow

open ArithmeticModel Scale ValuationCutoff
open OmittedTiltPairChamber
open PaperPrimePowerTailLedger PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays
open PrimeSums

noncomputable section

theorem sum_eJI_eq
    (G : ℝ) (n p q A : ℕ) :
    (∑ r ∈ highExponents A, eJI G n p q r) =
      (G + G ^ 2) *
        (∑ r ∈ jiBeyondFour n p q A,
          1 / ((p : ℝ) ^ r * (q : ℝ))) := by
  unfold eJI covarianceTail jiBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [pairPower, pow_one]
  by_cases hle : p ^ r * q ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p ^ r * q := Nat.not_lt_of_ge hle
    simp only [if_pos hle, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p ^ r * q := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

theorem sum_eIJ_eq
    (G : ℝ) (n p q A : ℕ) :
    (∑ s ∈ highExponents A, eIJ G n p q s) =
      (G + G ^ 2) *
        (∑ s ∈ ijBeyondFour n p q A,
          1 / ((p : ℝ) * (q : ℝ) ^ s)) := by
  unfold eIJ covarianceTail ijBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [pairPower, pow_one]
  by_cases hle : p * q ^ s ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p * q ^ s := Nat.not_lt_of_ge hle
    simp only [if_pos hle, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p * q ^ s := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

theorem sum_eJJ_eq
    (G : ℝ) (n p q A B : ℕ) :
    (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        eJJ G n p q r s) =
      (G + G ^ 2) *
        (∑ rs ∈ jjBeyondFour n p q A B,
          1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) := by
  unfold eJJ covarianceTail jjBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  calc
    (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        if pairPower p q r s ≤ yNat n ^ 4 then 0
        else (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)) =
      (∑ r ∈ highExponents A, ∑ s ∈ highExponents B,
        if yNat n ^ 4 < p ^ r * q ^ s then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ r * (q : ℝ) ^ s)) else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      simp only [pairPower]
      by_cases hle : p ^ r * q ^ s ≤ yNat n ^ 4
      · have hnlt : ¬ yNat n ^ 4 < p ^ r * q ^ s := Nat.not_lt_of_ge hle
        simp only [if_pos hle, if_neg hnlt]
      · have hlt : yNat n ^ 4 < p ^ r * q ^ s := Nat.lt_of_not_ge hle
        simp only [if_neg hle, if_pos hlt]
        ring
    _ = ∑ rs ∈ (highExponents A).product (highExponents B),
        if yNat n ^ 4 < p ^ rs.1 * q ^ rs.2 then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) else 0 := by
      symm
      exact Finset.sum_product (highExponents A) (highExponents B)
        (fun rs ↦ if yNat n ^ 4 < p ^ rs.1 * q ^ rs.2 then
          (G + G ^ 2) * (1 / ((p : ℝ) ^ rs.1 * (q : ℝ) ^ rs.2)) else 0)

theorem sum_weighted_eD_eq
    (G : ℝ) (n p A : ℕ) :
    (∑ r ∈ highExponents A,
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) =
      G * (∑ r ∈ diagonalBeyondFour n p A,
        ((2 * r - 3 : ℕ) : ℝ) / (p : ℝ) ^ r) := by
  unfold eD probabilityTail diagonalBeyondFour
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hle : p ^ r ≤ yNat n ^ 4
  · have hnlt : ¬ yNat n ^ 4 < p ^ r := Nat.not_lt_of_ge hle
    simp only [if_pos hle, mul_zero, if_neg hnlt]
  · have hlt : yNat n ^ 4 < p ^ r := Nat.lt_of_not_ge hle
    simp only [if_neg hle, if_pos hlt]
    ring

/-- Actual-cutoff bound for the `JI` residual sum. -/
theorem eventually_sum_eJI_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p), eJI G n p q r) ≤
        (G + G ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))) := by
  filter_upwards [eventually_actual_ji_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eJI_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the `IJ` residual sum. -/
theorem eventually_sum_eIJ_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (actualExponentCutoff C n q), eIJ G n p q s) ≤
        (G + G ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))) := by
  filter_upwards [eventually_actual_ij_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eIJ_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the `JJ` residual sum. -/
theorem eventually_sum_eJJ_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        ∑ s ∈ highExponents (actualExponentCutoff C n q), eJJ G n p q r s) ≤
        (G + G ^ 2) * (((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ))) := by
  filter_upwards [eventually_actual_jj_reciprocal_tail_le C W hC hW]
    with n htail
  intro p hp q hq
  rw [sum_eJJ_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp q hq)
    (by nlinarith [sq_nonneg G])

/-- Actual-cutoff bound for the weighted diagonal residual sum. -/
theorem eventually_sum_weighted_eD_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
        G * ((2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
  filter_upwards [eventually_actual_diagonal_weighted_reciprocal_tail_le
    C W hC hW] with n htail
  intro p hp
  rw [sum_weighted_eD_eq]
  exact mul_le_mul_of_nonneg_left (htail p hp) hG

/-! ## One row majorant -/

/-- Explicit common majorant for all four outside-chamber residual rows. -/
def tailRowMajorant (G : ℝ) (W n : ℕ) : ℝ :=
  let T := G + G ^ 2
  let K := cutoffScale W * L n
  let Y := (yNat n : ℝ)
  T * ((K / Y) * (bandReciprocalSum n W + 1)) +
    T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) +
      6 * G * (K ^ 2 / Y ^ 2)

theorem tailRowMajorant_nonneg {G : ℝ} (hG : 0 ≤ G) {W n : ℕ}
    (hW : 1 < W) (hn : 1 < n) :
    0 ≤ tailRowMajorant G W n := by
  unfold tailRowMajorant
  dsimp only
  have hT : 0 ≤ G + G ^ 2 := by nlinarith [sq_nonneg G]
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hK : 0 ≤ cutoffScale W * L n :=
    mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hY : 0 ≤ (yNat n : ℝ) := by positivity
  have hYpow : 0 ≤ (yNat n : ℝ) ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hY _
  exact add_nonneg
    (add_nonneg
      (mul_nonneg hT (mul_nonneg (div_nonneg hK hY)
        (by linarith)))
      (mul_nonneg hT (div_nonneg (sq_nonneg _) hYpow)))
    (mul_nonneg (mul_nonneg (by norm_num) hG)
      (div_nonneg (sq_nonneg _) (sq_nonneg _)))

private theorem mul_div_sq_le_self {P X : ℝ}
    (hP : 1 ≤ P) (hX : 0 ≤ X) :
    P * (X / P ^ 2) ≤ X := by
  have hP0 : 0 < P := zero_lt_one.trans_le hP
  calc
    P * (X / P ^ 2) = X / P := by field_simp [hP0.ne']
    _ ≤ X := div_le_self hX hP

/-- The exact four residual ledgers fit into `tailRowMajorant`, uniformly in
the selected row prime. -/
theorem eventually_tail_row_le
    (G C : ℝ) (W : ℕ) (hG : 0 ≤ G) (hC : 0 < C) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            ((∑ r ∈ highExponents (actualExponentCutoff C n p),
                eJI G n p q r) +
              (∑ s ∈ highExponents (actualExponentCutoff C n q),
                eIJ G n p q s) +
              (∑ r ∈ highExponents (actualExponentCutoff C n p),
                ∑ s ∈ highExponents (actualExponentCutoff C n q),
                  eJJ G n p q r s))) +
          3 * (∑ r ∈ highExponents (actualExponentCutoff C n p),
            (((2 * r - 3 : ℕ) : ℝ) * eD G n p r))) ≤
        tailRowMajorant G W n := by
  filter_upwards [eventually_sum_eJI_le G C W hG hC hW,
    eventually_sum_eIJ_le G C W hG hC hW,
    eventually_sum_eJJ_le G C W hG hC hW,
    eventually_sum_weighted_eD_le G C W hG hC hW,
    Filter.eventually_gt_atTop 1]
    with n hJI hIJ hJJ hD hn
  intro p hpBand
  let T : ℝ := G + G ^ 2
  let K : ℝ := cutoffScale W * L n
  let Y : ℝ := yNat n
  have hpPrime := prime_of_mem_primeBand hpBand
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpPrime.one_le
  have hp0 : (0 : ℝ) ≤ p := zero_le_one.trans hp1
  have hY : 0 < Y := by
    dsimp only [Y]
    exact_mod_cast hpPrime.pos.trans_le (le_yNat_of_mem_primeBand hpBand)
  have hT : 0 ≤ T := by
    dsimp only [T]
    nlinarith [sq_nonneg G]
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact mul_nonneg (cutoffScale_pos hW).le
      (L_pos hn).le
  have hH : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hRec :
      (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ)) ≤
        bandReciprocalSum n W := by
    unfold bandReciprocalSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (by intro q hq hnot; positivity)
  have hSqSubset :
      (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) ≤
        bandReciprocalSquareSum n W := by
    unfold bandReciprocalSquareSum
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (by intro q hq hnot; positivity)
  have hWcast : (1 : ℝ) ≤ W := by exact_mod_cast hW.le
  have hSq :
      (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) ≤ 1 := by
    exact hSqSubset.trans ((bandReciprocalSquareSum_le n W hW.le).trans
      (div_le_self zero_le_one hWcast))
  have hJIsum :
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          eJI G n p q r) ≤
        (T * K / ((p : ℝ) ^ 2 * Y)) * bandReciprocalSum n W := by
    calc
      _ ≤ ∑ q ∈ (primeBand n W).erase p,
          T * (K / ((p : ℝ) ^ 2 * (q : ℝ) * Y)) := by
        exact Finset.sum_le_sum fun q hq ↦
          hJI p hpBand q ((Finset.mem_erase.mp hq).2)
      _ = (T * K / ((p : ℝ) ^ 2 * Y)) *
          (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (T * K / ((p : ℝ) ^ 2 * Y)) *
          bandReciprocalSum n W :=
        mul_le_mul_of_nonneg_left hRec (by positivity)
  have hIJsum :
      (∑ q ∈ (primeBand n W).erase p,
        ∑ s ∈ highExponents (actualExponentCutoff C n q),
          eIJ G n p q s) ≤ T * K / ((p : ℝ) * Y) := by
    calc
      _ ≤ ∑ q ∈ (primeBand n W).erase p,
          T * (K / ((p : ℝ) * (q : ℝ) ^ 2 * Y)) := by
        exact Finset.sum_le_sum fun q hq ↦
          hIJ p hpBand q ((Finset.mem_erase.mp hq).2)
      _ = (T * K / ((p : ℝ) * Y)) *
          (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (T * K / ((p : ℝ) * Y)) * 1 :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      _ = T * K / ((p : ℝ) * Y) := by ring
  have hJJsum :
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          ∑ s ∈ highExponents (actualExponentCutoff C n q),
            eJJ G n p q r s) ≤
        T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ)) := by
    calc
      _ ≤ ∑ q ∈ (primeBand n W).erase p,
          T * (K ^ 2 /
            ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) := by
        exact Finset.sum_le_sum fun q hq ↦
          hJJ p hpBand q ((Finset.mem_erase.mp hq).2)
      _ = (T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) *
          (∑ q ∈ (primeBand n W).erase p, 1 / (q : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      _ = T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ)) := by ring
  have hDsum :
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
        G * (2 * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ 2)) := by
    simpa only [T, K, Y] using hD p hpBand
  have hJIRow : (p : ℝ) *
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          eJI G n p q r) ≤
      T * ((K / Y) * bandReciprocalSum n W) := by
    calc
      _ ≤ (p : ℝ) *
          ((T * K / ((p : ℝ) ^ 2 * Y)) * bandReciprocalSum n W) :=
        mul_le_mul_of_nonneg_left hJIsum hp0
      _ = ((p : ℝ) * ((T * K / Y) / (p : ℝ) ^ 2)) *
          bandReciprocalSum n W := by ring
      _ ≤ (T * K / Y) * bandReciprocalSum n W :=
        mul_le_mul_of_nonneg_right
          (mul_div_sq_le_self hp1 (by positivity)) hH
      _ = T * ((K / Y) * bandReciprocalSum n W) := by ring
  have hIJRow : (p : ℝ) *
      (∑ q ∈ (primeBand n W).erase p,
        ∑ s ∈ highExponents (actualExponentCutoff C n q),
          eIJ G n p q s) ≤ T * (K / Y) := by
    calc
      _ ≤ (p : ℝ) * (T * K / ((p : ℝ) * Y)) :=
        mul_le_mul_of_nonneg_left hIJsum hp0
      _ = T * (K / Y) := by field_simp [hpPrime.ne_zero]
  have hJJRow : (p : ℝ) *
      (∑ q ∈ (primeBand n W).erase p,
        ∑ r ∈ highExponents (actualExponentCutoff C n p),
          ∑ s ∈ highExponents (actualExponentCutoff C n q),
            eJJ G n p q r s) ≤ T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by
    calc
      _ ≤ (p : ℝ) *
          (T * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ (2 / 3 : ℝ))) :=
        mul_le_mul_of_nonneg_left hJJsum hp0
      _ = (p : ℝ) *
          ((T * K ^ 2 / Y ^ (2 / 3 : ℝ)) / (p : ℝ) ^ 2) := by ring
      _ ≤ T * K ^ 2 / Y ^ (2 / 3 : ℝ) :=
        mul_div_sq_le_self hp1 (by positivity)
      _ = T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by ring
  have hDRow : (p : ℝ) * 3 *
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD G n p r)) ≤
      6 * G * (K ^ 2 / Y ^ 2) := by
    calc
      _ ≤ (p : ℝ) * 3 *
          (G * (2 * K ^ 2 / ((p : ℝ) ^ 2 * Y ^ 2))) :=
        mul_le_mul_of_nonneg_left hDsum (mul_nonneg hp0 (by norm_num))
      _ = 6 * G * ((p : ℝ) * ((K ^ 2 / Y ^ 2) / (p : ℝ) ^ 2)) := by
        ring
      _ ≤ 6 * G * (K ^ 2 / Y ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_div_sq_le_self hp1 (by positivity)) (by positivity)
  unfold tailRowMajorant
  dsimp only
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have htotal := add_le_add (add_le_add (add_le_add hJIRow hIJRow) hJJRow) hDRow
  dsimp only [T, K, Y] at htotal
  convert htotal using 1 <;> ring

/-! ## Vanishing of the row majorant -/

/-- A polynomial in `log n` is negligible compared with every fixed
positive power of `n`. -/
private theorem tendsto_L_sq_div_nat_rpow_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n ^ 2 / (n : ℝ) ^ a) atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (2 : ℝ) / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Tendsto
    (fun n : ℕ ↦ Real.log (n : ℝ) ^ (2 : ℝ) / (n : ℝ) ^ a)
      atTop (nhds 0) at hnat
  simpa [L, Real.rpow_natCast] using hnat

/-- A convenient real-power upper bound for `tailRowMajorant`. -/
def tailRowLimitMajorant (G : ℝ) (W n : ℕ) : ℝ :=
  let T := G + G ^ 2
  let c := cutoffScale W
  (13 * T * c) * (L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) +
    (T * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) +
      (6 * G * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ))

theorem tendsto_tailRowLimitMajorant_zero (G : ℝ) (W : ℕ) :
    Tendsto (tailRowLimitMajorant G W) atTop (nhds 0) := by
  have h1 := tendsto_L_sq_div_nat_rpow_zero
    (show (0 : ℝ) < 1 / 5 by norm_num)
  have h2 := tendsto_L_sq_div_nat_rpow_zero
    (show (0 : ℝ) < 2 / 15 by norm_num)
  have h3 := tendsto_L_sq_div_nat_rpow_zero
    (show (0 : ℝ) < 2 / 5 by norm_num)
  have hc1 : Tendsto
      (fun _n : ℕ ↦ 13 * (G + G ^ 2) * cutoffScale W)
      atTop (nhds (13 * (G + G ^ 2) * cutoffScale W)) :=
    tendsto_const_nhds
  have ht1 : Tendsto (fun n : ℕ ↦
      (13 * (G + G ^ 2) * cutoffScale W) *
        (L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hc1.mul h1
  have hc2 : Tendsto
      (fun _n : ℕ ↦ (G + G ^ 2) * cutoffScale W ^ 2)
      atTop (nhds ((G + G ^ 2) * cutoffScale W ^ 2)) :=
    tendsto_const_nhds
  have ht2 : Tendsto (fun n : ℕ ↦
      ((G + G ^ 2) * cutoffScale W ^ 2) *
        (L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hc2.mul h2
  have hc3 : Tendsto
      (fun _n : ℕ ↦ 6 * G * cutoffScale W ^ 2)
      atTop (nhds (6 * G * cutoffScale W ^ 2)) :=
    tendsto_const_nhds
  have ht3 : Tendsto (fun n : ℕ ↦
      (6 * G * cutoffScale W ^ 2) *
        (L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero] using hc3.mul h3
  unfold tailRowLimitMajorant
  dsimp only
  simpa only [add_zero] using (ht1.add ht2).add ht3

theorem eventually_tailRowMajorant_le_limit
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    ∀ᶠ n : ℕ in atTop,
      tailRowMajorant G W n ≤ tailRowLimitMajorant G W n := by
  filter_upwards [FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    eventually_bandReciprocalSum_le_logL W,
    (show Tendsto L atTop atTop by
      simpa [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (1 : ℝ)),
    Filter.eventually_gt_atTop 1] with n hlogY hband hL1 hn
  let T : ℝ := G + G ^ 2
  let c : ℝ := cutoffScale W
  let Y : ℝ := yNat n
  have hL : 0 < L n := L_pos hn
  have hT : 0 ≤ T := by
    dsimp only [T]
    nlinarith [sq_nonneg G]
  have hc : 0 ≤ c := (cutoffScale_pos hW).le
  have hYnonneg : 0 ≤ Y := by dsimp only [Y]; positivity
  have hlogYpos : 0 < Real.log Y := by
    have : 0 < (1 / 5 : ℝ) * L n := by positivity
    exact this.trans_le (by simpa only [Y] using hlogY)
  have hYone : 1 < Y := (Real.log_pos_iff hYnonneg).mp hlogYpos
  have hYpos : 0 < Y := zero_lt_one.trans hYone
  have hnRpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hnPow : (n : ℝ) ^ (1 / 5 : ℝ) ≤ Y := by
    calc
      (n : ℝ) ^ (1 / 5 : ℝ) =
          Real.exp ((1 / 5 : ℝ) * L n) := by
        rw [Real.rpow_def_of_pos hnRpos]
        congr 1
        unfold L
        ring
      _ ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr
        (by simpa only [Y] using hlogY)
      _ = Y := Real.exp_log hYpos
  have hnPowPos : 0 < (n : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnRpos _
  have hnPow23 : (n : ℝ) ^ (2 / 15 : ℝ) ≤
      Y ^ (2 / 3 : ℝ) := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 5 : ℝ))
      hnPow (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    calc
      (n : ℝ) ^ (2 / 15 : ℝ) =
          ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (2 / 3 : ℝ) := by
        convert Real.rpow_mul (Nat.cast_nonneg n) (1 / 5 : ℝ) (2 / 3 : ℝ)
          using 1
        all_goals norm_num
      _ ≤ Y ^ (2 / 3 : ℝ) := hmono
  have hnPow23Pos : 0 < (n : ℝ) ^ (2 / 15 : ℝ) :=
    Real.rpow_pos_of_pos hnRpos _
  have hnPow2 : (n : ℝ) ^ (2 / 5 : ℝ) ≤ Y ^ 2 := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 5 : ℝ))
      hnPow (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      (n : ℝ) ^ (2 / 5 : ℝ) =
          ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (2 : ℝ) := by
        convert Real.rpow_mul (Nat.cast_nonneg n) (1 / 5 : ℝ) (2 : ℝ)
          using 1
        all_goals norm_num
      _ ≤ Y ^ (2 : ℝ) := hmono
      _ = Y ^ 2 := by norm_num [Real.rpow_two]
  have hnPow2Pos : 0 < (n : ℝ) ^ (2 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnRpos _
  have hlogL : Real.log (L n) ≤ L n - 1 :=
    Real.log_le_sub_one_of_pos hL
  have hband' : bandReciprocalSum n W + 1 ≤ 13 * L n := by
    linarith
  have hH0 : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hK0 : 0 ≤ c * L n := mul_nonneg hc hL.le
  have hdiv1 : (c * L n) / Y ≤
      (c * L n) / (n : ℝ) ^ (1 / 5 : ℝ) :=
    div_le_div_of_nonneg_left hK0 hnPowPos hnPow
  have hinner1 : ((c * L n) / Y) * (bandReciprocalSum n W + 1) ≤
      ((c * L n) / (n : ℝ) ^ (1 / 5 : ℝ)) * (13 * L n) :=
    mul_le_mul hdiv1 hband' (add_nonneg hH0 zero_le_one)
      (div_nonneg hK0 hnPowPos.le)
  have hterm1 : T * (((c * L n) / Y) *
      (bandReciprocalSum n W + 1)) ≤
      (13 * T * c) * (L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) := by
    calc
      _ ≤ T * (((c * L n) / (n : ℝ) ^ (1 / 5 : ℝ)) *
          (13 * L n)) := mul_le_mul_of_nonneg_left hinner1 hT
      _ = _ := by ring
  have hnum2 : 0 ≤ (c * L n) ^ 2 := sq_nonneg _
  have hdiv2 : (c * L n) ^ 2 / Y ^ (2 / 3 : ℝ) ≤
      (c * L n) ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ) :=
    div_le_div_of_nonneg_left hnum2 hnPow23Pos hnPow23
  have hterm2 : T * ((c * L n) ^ 2 / Y ^ (2 / 3 : ℝ)) ≤
      (T * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) := by
    calc
      _ ≤ T * ((c * L n) ^ 2 /
          (n : ℝ) ^ (2 / 15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv2 hT
      _ = _ := by ring
  have hdiv3 : (c * L n) ^ 2 / Y ^ 2 ≤
      (c * L n) ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ) :=
    div_le_div_of_nonneg_left hnum2 hnPow2Pos hnPow2
  have hterm3 : 6 * G * ((c * L n) ^ 2 / Y ^ 2) ≤
      (6 * G * c ^ 2) * (L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ)) := by
    calc
      _ ≤ 6 * G * ((c * L n) ^ 2 /
          (n : ℝ) ^ (2 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv3 (mul_nonneg (by norm_num) hG)
      _ = _ := by ring
  unfold tailRowMajorant tailRowLimitMajorant
  dsimp only [T, c, Y]
  exact add_le_add (add_le_add hterm1 hterm2) hterm3

/-- The complete literal beyond-four residual row vanishes. -/
theorem tendsto_tailRowMajorant_zero
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Tendsto (tailRowMajorant G W) atTop (nhds 0) := by
  have hupper := eventually_tailRowMajorant_le_limit G W hG hW
  have hlower : ∀ᶠ n : ℕ in atTop, 0 ≤ tailRowMajorant G W n := by
    filter_upwards [Filter.eventually_gt_atTop 1] with n hn
    exact tailRowMajorant_nonneg hG hW hn
  exact squeeze_zero' hlower hupper (tendsto_tailRowLimitMajorant_zero G W)

/-- The polynomial tail remains negligible after the one harmonic
`log (L n)` loss used by the moving low band. -/
private theorem tendsto_L_sq_div_nat_rpow_mul_logL_zero
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n)) atTop (nhds 0) := by
  have hcube : Tendsto (fun n : ℕ ↦
      L n ^ 3 / (n : ℝ) ^ a) atTop (nhds 0) := by
    have hreal : Tendsto
        (fun x : ℝ ↦ Real.log x ^ (3 : ℝ) / x ^ a)
        atTop (nhds 0) :=
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ) ha).tendsto_div_nhds_zero
    have hnat := hreal.comp tendsto_natCast_atTop_atTop
    change Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ (3 : ℝ) / (n : ℝ) ^ a)
        atTop (nhds 0) at hnat
    simpa [L, Real.rpow_natCast] using hnat
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL1
    exact mul_nonneg (div_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _))
      (Real.log_nonneg hL1)
  have hupper : ∀ᶠ n : ℕ in atTop,
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) ≤
        L n ^ 3 / (n : ℝ) ^ a := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL1
    have hL0 : 0 ≤ L n := zero_le_one.trans hL1
    have hlog0 : 0 ≤ Real.log (L n) := Real.log_nonneg hL1
    have hlogLe : Real.log (L n) ≤ L n :=
      (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hL1)).trans (by linarith)
    have hden : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by positivity) _
    calc
      (L n ^ 2 / (n : ℝ) ^ a) * Real.log (L n) =
          (L n ^ 2 * Real.log (L n)) / (n : ℝ) ^ a := by ring
      _ ≤ (L n ^ 2 * L n) / (n : ℝ) ^ a :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlogLe (sq_nonneg _)) hden
      _ = L n ^ 3 / (n : ℝ) ^ a := by ring
  exact squeeze_zero' hlower hupper hcube

/-- `tailRowMajorant` has the sharp rate required to divide by the moving
low-cell scale `alpha_0 \asymp 1 / log L`. -/
theorem tendsto_tailRowMajorant_mul_logL_zero
    (G : ℝ) (W : ℕ) (hG : 0 ≤ G) (hW : 1 < W) :
    Tendsto (fun n : ℕ ↦
      tailRowMajorant G W n * Real.log (L n)) atTop (nhds 0) := by
  have h1 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 1 / 5 by norm_num)
  have h2 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 2 / 15 by norm_num)
  have h3 := tendsto_L_sq_div_nat_rpow_mul_logL_zero
    (show (0 : ℝ) < 2 / 5 by norm_num)
  have hlimitRate : Tendsto (fun n : ℕ ↦
      tailRowLimitMajorant G W n * Real.log (L n)) atTop (nhds 0) := by
    have ht1 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 13 * (G + G ^ 2) * cutoffScale W) atTop
      (nhds (13 * (G + G ^ 2) * cutoffScale W))).mul h1
    have ht2 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ (G + G ^ 2) * cutoffScale W ^ 2) atTop
      (nhds ((G + G ^ 2) * cutoffScale W ^ 2))).mul h2
    have ht3 := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ 6 * G * cutoffScale W ^ 2) atTop
      (nhds (6 * G * cutoffScale W ^ 2))).mul h3
    have hsum := (ht1.add ht2).add ht3
    have hsum0 : Tendsto (fun n : ℕ ↦
        (13 * (G + G ^ 2) * cutoffScale W) *
            ((L n ^ 2 / (n : ℝ) ^ (1 / 5 : ℝ)) * Real.log (L n)) +
        ((G + G ^ 2) * cutoffScale W ^ 2) *
            ((L n ^ 2 / (n : ℝ) ^ (2 / 15 : ℝ)) * Real.log (L n)) +
        (6 * G * cutoffScale W ^ 2) *
            ((L n ^ 2 / (n : ℝ) ^ (2 / 5 : ℝ)) * Real.log (L n)))
        atTop (nhds 0) := by simpa only [mul_zero, add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold tailRowLimitMajorant
    ring
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : ∀ᶠ n : ℕ in atTop,
      0 ≤ tailRowMajorant G W n * Real.log (L n) := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hL1
    exact mul_nonneg (tailRowMajorant_nonneg hG hW hn)
      (Real.log_nonneg hL1)
  have hupper : ∀ᶠ n : ℕ in atTop,
      tailRowMajorant G W n * Real.log (L n) ≤
        tailRowLimitMajorant G W n * Real.log (L n) := by
    filter_upwards [eventually_tailRowMajorant_le_limit G W hG hW,
      hLTop.eventually (eventually_ge_atTop (1 : ℝ))] with n hrow hL1
    exact mul_le_mul_of_nonneg_right hrow (Real.log_nonneg hL1)
  exact squeeze_zero' hlower hupper hlimitRate

end

end Erdos390.Full.PaperPrimePowerTailRow
