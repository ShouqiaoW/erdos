import Erdos390.WholePaper.MovingLayerLowerBound
import Erdos390.WholePaper.NoAdmissibleBelowTwoN

/-! # Per-prime factorial-tail valuation estimates -/

namespace Erdos390.WholePaper

noncomputable section

theorem factorialValuation_eq_choose_add_factorialValuation_add
    {a h p : ℕ} :
    (a + h).factorial.factorization p =
      (Nat.choose (a + h) h).factorization p +
        h.factorial.factorization p + a.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (a + h) h :=
    Nat.choose_pos (Nat.le_add_left h a)
  have hfactorization := congrArg Nat.factorization
    (Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left h a))
  simp only [Nat.add_sub_cancel_right] at hfactorization
  rw [Nat.factorization_mul
      (mul_ne_zero hchoosePos.ne' (Nat.factorial_ne_zero h))
      (Nat.factorial_ne_zero a),
    Nat.factorization_mul hchoosePos.ne' (Nat.factorial_ne_zero h)] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply] using hcoordinate.symm

theorem factorialValuationSub_eq_choose_add_factorialValuation
    {a h p : ℕ} :
    (a + h).factorial.factorization p - a.factorial.factorization p =
      (Nat.choose (a + h) h).factorization p + h.factorial.factorization p := by
  rw [factorialValuation_eq_choose_add_factorialValuation_add]
  omega

theorem factorialValuationSub_le_div_pred_add_log2
    {a h p : ℕ} (hp : p.Prime) :
    (a + h).factorial.factorization p - a.factorial.factorization p ≤
      h / (p - 1) + Nat.log2 (a + h) := by
  rw [factorialValuationSub_eq_choose_add_factorialValuation]
  have hchoose :
      (Nat.choose (a + h) h).factorization p ≤ Nat.log2 (a + h) := by
    calc
      (Nat.choose (a + h) h).factorization p ≤ Nat.log p (a + h) :=
        Nat.factorization_choose_le_log
      _ ≤ Nat.log 2 (a + h) :=
        Nat.log_anti_left Nat.one_lt_two hp.two_le
      _ = Nat.log2 (a + h) := Nat.log2_eq_log_two.symm
  have hfactorial :
      h.factorial.factorization p ≤ h / (p - 1) :=
    Nat.factorization_factorial_le_div_pred hp h
  omega

theorem centralFactorialValuation_eq_choose_add {n p : ℕ} :
    (2 * n).factorial.factorization p =
      (Nat.choose (2 * n) n).factorization p +
        2 * n.factorial.factorization p := by
  have hchoosePos : 0 < Nat.choose (2 * n) n :=
    Nat.choose_pos (by omega)
  have hfactorization := congrArg Nat.factorization
    (centralChoose_mul_factorial_sq n)
  rw [Nat.factorization_mul hchoosePos.ne'
      (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfactorization
  have hcoordinate := congrArg (fun v : ℕ →₀ ℕ ↦ v p) hfactorization
  simpa only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul,
    Nat.cast_ofNat] using hcoordinate.symm

theorem centralFactorialValuationSub_eq_chooseValuation {n p : ℕ} :
    (2 * n).factorial.factorization p - 2 * n.factorial.factorization p =
      (Nat.choose (2 * n) n).factorization p := by
  rw [centralFactorialValuation_eq_choose_add]
  omega

theorem fullFactorialValuationSub_eq_central_add_tail
    {n h p : ℕ} :
    (2 * n + h).factorial.factorization p -
        2 * n.factorial.factorization p =
      (Nat.choose (2 * n) n).factorization p +
        ((2 * n + h).factorial.factorization p -
          (2 * n).factorial.factorization p) := by
  have htail := factorialValuation_eq_choose_add_factorialValuation_add
    (a := 2 * n) (h := h) (p := p)
  have hcentral := centralFactorialValuation_eq_choose_add (n := n) (p := p)
  omega

theorem fullFactorialValuationSub_le_central_add_tailCapacity
    {n h p : ℕ} (hp : p.Prime) :
    (2 * n + h).factorial.factorization p -
        2 * n.factorial.factorization p ≤
      (Nat.choose (2 * n) n).factorization p +
        (h / (p - 1) + Nat.log2 (2 * n + h)) := by
  rw [fullFactorialValuationSub_eq_central_add_tail]
  exact Nat.add_le_add_left
    (factorialValuationSub_le_div_pred_add_log2 (a := 2 * n) hp) _

end

end Erdos390.WholePaper
