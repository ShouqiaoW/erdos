import Erdos390.WholePaper.CentralPromotion

/-! # Expanded statement audit for residual central promotion -/

namespace Erdos390.WholePaper

noncomputable section

example {n B : ℕ} (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    n < 2 ^ Nat.clog 2 (n / B + 1) * B ∧
      2 ^ Nat.clog 2 (n / B + 1) * B ≤ 2 * n := by
  exact ⟨promotionExponent_spec hB,
    promotedBlock_le_two_mul hB hBupper⟩

example {n B k : ℕ} (hk : k < Nat.clog 2 (n / B + 1)) :
    2 ^ k * B ≤ n := by
  exact promotionExponent_minimal hk

example {n B p : ℕ} (hp : 0 < p) (hpB : p ≤ B) :
    Nat.clog 2 (n / B + 1) ≤ 1 + Nat.log2 (n / p) := by
  exact promotionExponent_le_one_add_log2 hp hpB

example {n p : ℕ} (hn : 0 < n) :
    2 ^ Nat.clog 2
          (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) *
        p ^ (Nat.choose (2 * n) n).factorization p ∈
      Finset.Ioc n (2 * n) := by
  exact promotedCentralFactor_mem_centralInterval hn

example {n p : ℕ} (hp : p.Prime) (hpOdd : p ≠ 2) :
    (2 ^ Nat.clog 2
          (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) *
        p ^ (Nat.choose (2 * n) n).factorization p).factorization p =
      (Nat.choose (2 * n) n).factorization p := by
  exact promotedCentralFactor_factorization_odd hp hpOdd

example {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hqExponent : 0 < (Nat.choose (2 * n) n).factorization q)
    (hfactor :
      2 ^ Nat.clog 2
            (n / (p ^ (Nat.choose (2 * n) n).factorization p) + 1) *
          p ^ (Nat.choose (2 * n) n).factorization p =
        2 ^ Nat.clog 2
            (n / (q ^ (Nat.choose (2 * n) n).factorization q) + 1) *
          q ^ (Nat.choose (2 * n) n).factorization q) :
    p = q := by
  exact promotedCentralFactor_injective_on_positive_support
    hp hq hpExponent hqExponent hfactor

end

end Erdos390.WholePaper
