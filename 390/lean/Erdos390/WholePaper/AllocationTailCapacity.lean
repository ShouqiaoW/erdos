import Erdos390.WholePaper.LeastPrimeTail
import Erdos390.WholePaper.Constants

/-! # Exact capacity estimate for one least-prime allocation block -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem alpha_lt_one_div_two_mul_sq {a r : ℕ}
    (ha : 0 < a) (har : a ≤ r) :
    alpha r < 1 / (2 * (a : ℚ) ^ 2) := by
  rw [alpha]
  apply one_div_lt_one_div_of_lt
  · positivity
  · have haR : (0 : ℚ) < a := by exact_mod_cast ha
    have harR : (a : ℚ) ≤ r := by exact_mod_cast har
    have hsq : (a : ℚ) ^ 2 ≤ (r : ℚ) ^ 2 := by
      exact (sq_le_sq₀ haR.le (Nat.cast_nonneg r)).2 harR
    calc
      2 * (a : ℚ) ^ 2 ≤ 2 * (r : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ < ((r : ℚ) + 1) * (2 * (r : ℚ) + 1) := by
        rw [show ((r : ℚ) + 1) * (2 * (r : ℚ) + 1) =
            2 * (r : ℚ) ^ 2 + (3 * (r : ℚ) + 1) by ring]
        exact lt_add_of_pos_right _ (by positivity)

theorem allocationTail_alpha_block_sum_lt
    {a p : ℕ} (ha : 0 < a) (hap : a < p) :
    (∑ r ∈ Finset.Icc a (p - 1), alpha r) <
      ((p - a : ℕ) : ℚ) / (2 * (a : ℚ) ^ 2) := by
  let rows := Finset.Icc a (p - 1)
  have haMem : a ∈ rows := by
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hsum :
      (∑ r ∈ rows, alpha r) <
        ∑ _r ∈ rows, (1 / (2 * (a : ℚ) ^ 2)) := by
    exact Finset.sum_lt_sum_of_nonempty ⟨a, haMem⟩ fun r hr ↦
      alpha_lt_one_div_two_mul_sq ha (Finset.mem_Icc.mp hr).1
  have hcard : rows.card = p - a := by
    dsimp only [rows]
    rw [Nat.card_Icc]
    omega
  have hconst :
      (∑ _r ∈ rows, (1 / (2 * (a : ℚ) ^ 2))) =
        (rows.card : ℚ) * (1 / (2 * (a : ℚ) ^ 2)) := by
    simp
  rw [hconst, hcard] at hsum
  simpa only [rows, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
    one_mul] using hsum

theorem nagura_gap_fraction_lt_three_div_twenty_five
    {a p : ℕ} (ha : 0 < a) (hap : a < p)
    (hNagura : 5 * p < 6 * a) :
    (p : ℚ) * ((p - a : ℕ) : ℚ) /
        (2 * (a : ℚ) ^ 2) <
      (3 : ℚ) / 25 := by
  have haR : (0 : ℚ) < a := by exact_mod_cast ha
  have hapR : (a : ℚ) < p := by exact_mod_cast hap
  have hNaguraR : (5 : ℚ) * p < 6 * a := by exact_mod_cast hNagura
  have hsubCast : (((p - a : ℕ) : ℚ)) = (p : ℚ) - a := by
    rw [Nat.cast_sub hap.le]
  rw [hsubCast]
  have hpPos : (0 : ℚ) < p := haR.trans hapR
  have hgapPos : (0 : ℚ) < (p : ℚ) - a := sub_pos.mpr hapR
  have hpBound : (p : ℚ) < (6 / 5 : ℚ) * a := by
    linarith
  have hgapBound : (p : ℚ) - a < (1 / 5 : ℚ) * a := by
    linarith
  have hproduct :
      (p : ℚ) * ((p : ℚ) - a) <
        ((6 / 5 : ℚ) * a) * ((1 / 5 : ℚ) * a) :=
    mul_lt_mul hpBound hgapBound.le hgapPos
      (by positivity)
  have hdenom : (0 : ℚ) < 2 * (a : ℚ) ^ 2 := by positivity
  apply (div_lt_iff₀ hdenom).2
  calc
    (p : ℚ) * ((p : ℚ) - a) <
        ((6 / 5 : ℚ) * a) * ((1 / 5 : ℚ) * a) := hproduct
    _ = (3 / 25 : ℚ) * (2 * (a : ℚ) ^ 2) := by ring

/-- The exact strict capacity estimate used for every tail prime above the
finite certificate. -/
theorem allocationTail_block_capacity_lt_C0Rat
    {pPrev p : ℕ} (hpPrevPos : 0 < pPrev) (hPrevP : pPrev < p)
    (hNagura : 5 * p < 6 * pPrev) :
    (((p - 1 : ℕ) : ℚ)) *
        (∑ r ∈ Finset.Icc pPrev (p - 1), alpha r) < C0Rat := by
  have hsum := allocationTail_alpha_block_sum_lt hpPrevPos hPrevP
  have hpPredLt : ((p - 1 : ℕ) : ℚ) < (p : ℚ) := by
    exact_mod_cast Nat.pred_lt (Nat.ne_of_gt (hpPrevPos.trans hPrevP))
  have hscaled := mul_lt_mul_of_pos_left hsum
    (show (0 : ℚ) < (p - 1 : ℕ) by
      exact_mod_cast (by omega : 0 < p - 1))
  have hquotPos :
      (0 : ℚ) < ((p - pPrev : ℕ) : ℚ) /
        (2 * (pPrev : ℚ) ^ 2) := by
    apply div_pos
    · exact_mod_cast Nat.sub_pos_of_lt hPrevP
    · positivity
  have hreplace :
      ((p - 1 : ℕ) : ℚ) *
          (((p - pPrev : ℕ) : ℚ) /
            (2 * (pPrev : ℚ) ^ 2)) <
        (p : ℚ) * ((p - pPrev : ℕ) : ℚ) /
          (2 * (pPrev : ℚ) ^ 2) := by
    calc
      ((p - 1 : ℕ) : ℚ) *
          (((p - pPrev : ℕ) : ℚ) /
            (2 * (pPrev : ℚ) ^ 2)) <
          (p : ℚ) *
            (((p - pPrev : ℕ) : ℚ) /
              (2 * (pPrev : ℚ) ^ 2)) :=
        mul_lt_mul_of_pos_right hpPredLt hquotPos
      _ = (p : ℚ) * ((p - pPrev : ℕ) : ℚ) /
          (2 * (pPrev : ℚ) ^ 2) := by ring
  have hthree := nagura_gap_fraction_lt_three_div_twenty_five
    hpPrevPos hPrevP hNagura
  exact (((hscaled.trans hreplace).trans hthree).trans
    three_div_twenty_five_lt_C0Rat)

end

end Erdos390.WholePaper
