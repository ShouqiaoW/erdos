import Erdos390.WholePaper.TailValuationCore

/-!
# Two-sided fixed-prime tail valuation bounds

The factorial quotient over `(a,a+h]` has `p`-valuation
`h/(p-1) + O(log(a+h))`.  This file records an exact integer version of
both sides.  The lower bound comes from Legendre's digit-sum identity and
is strong enough for the strict reserve in the central-anchor construction.
-/

namespace Erdos390.WholePaper

noncomputable section

private theorem digits_sum_le_pred_mul_length
    {p n : ℕ} (hp : p.Prime) :
    (p.digits n).sum ≤ (p - 1) * (p.digits n).length := by
  have listBound : ∀ l : List ℕ,
      (∀ d ∈ l, d < p) → l.sum ≤ (p - 1) * l.length := by
    intro l hd
    induction l with
    | nil => simp
    | cons d l ih =>
        have hdHead : d ≤ p - 1 := by
          have := hd d (by simp)
          omega
        have hdTail : ∀ e ∈ l, e < p := by
          intro e he
          exact hd e (by simp [he])
        have ih' := ih hdTail
        simp only [List.sum_cons, List.length_cons]
        calc
          d + l.sum ≤ (p - 1) + (p - 1) * l.length :=
            Nat.add_le_add hdHead ih'
          _ = (p - 1) * (l.length + 1) := by
            rw [Nat.mul_succ]
            omega
  exact listBound (p.digits n) (fun d hd ↦
    Nat.digits_lt_base hp.one_lt hd)

theorem digits_sum_le_pred_mul_log2_add_one
    {p n : ℕ} (hp : p.Prime) :
    (p.digits n).sum ≤ (p - 1) * (Nat.log2 n + 1) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hlength := digits_sum_le_pred_mul_length (n := n) hp
  rw [Nat.digits_len p n hp.one_lt hn] at hlength
  have hlog : Nat.log p n ≤ Nat.log 2 n :=
    Nat.log_anti_left Nat.one_lt_two hp.two_le
  rw [← Nat.log2_eq_log_two] at hlog
  exact hlength.trans (Nat.mul_le_mul_left (p - 1)
    (Nat.add_le_add_right hlog 1))

/-- Exact lower Legendre bound, written without integer division. -/
theorem factorialValuation_lower_cross
    {h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
      (h.factorial.factorization p + Nat.log2 h + 1) := by
  have hdigitsLe : (p.digits h).sum ≤ h := Nat.digit_sum_le p h
  have hlegendre := Nat.sub_one_mul_factorization_factorial
    (n := h) hp
  have hrecover :
      (p - 1) * h.factorial.factorization p + (p.digits h).sum = h := by
    omega
  have hdigitsBound := digits_sum_le_pred_mul_log2_add_one
    (n := h) hp
  calc
    h = (p - 1) * h.factorial.factorization p +
        (p.digits h).sum := hrecover.symm
    _ ≤ (p - 1) * h.factorial.factorization p +
        (p - 1) * (Nat.log2 h + 1) :=
      Nat.add_le_add_left hdigitsBound _
    _ = (p - 1) *
        (h.factorial.factorization p + Nat.log2 h + 1) := by ring

/-- The interval `(a,a+h]` contains at least the valuation of `h!`, hence
inherits the exact lower Legendre bound. -/
theorem factorialValuationSub_lower_cross
    {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
      ((a + h).factorial.factorization p - a.factorial.factorization p +
        Nat.log2 h + 1) := by
  have htail : h.factorial.factorization p ≤
      (a + h).factorial.factorization p - a.factorial.factorization p := by
    rw [factorialValuationSub_eq_choose_add_factorialValuation]
    omega
  exact (factorialValuation_lower_cross hp).trans
    (Nat.mul_le_mul_left (p - 1) (by omega))

/-- Exact two-sided version of
`v_p(∏_{a<j≤a+h} j) = h/(p-1) + O(log(a+h))`. -/
theorem factorialValuationSub_twoSided
    {a h p : ℕ} (hp : p.Prime) :
    h ≤ (p - 1) *
        ((a + h).factorial.factorization p - a.factorial.factorization p +
          Nat.log2 h + 1) ∧
      (a + h).factorial.factorization p - a.factorial.factorization p ≤
        h / (p - 1) + Nat.log2 (a + h) := by
  exact ⟨factorialValuationSub_lower_cross hp,
    factorialValuationSub_le_div_pred_add_log2 hp⟩

end

end Erdos390.WholePaper
