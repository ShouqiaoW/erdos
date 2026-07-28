import Erdos390.WholePaper.BankOrdinaryDonorRelation

/-! # Expanded statement audit for the ordinary marker--donor relation -/

namespace Erdos390.WholePaper

noncomputable section

example (j : ℕ) : bankOrdinaryScale j = 4 * (4 / 3 : ℚ) ^ j := rfl

example (n : ℕ) (Q : ℚ) (P : ℕ) :
    InOrdinaryBankMarkerInterval n Q P ↔
      4 * (n : ℚ) < 3 * Q * (P : ℚ) ∧
        2 * Q * (P : ℚ) ≤ 3 * (n : ℚ) := Iff.rfl

example (Q : ℚ) (u : ℕ) :
    InOrdinaryBankDonorWindow Q u ↔
      4 * Q ≤ 3 * (u : ℚ) ∧ 2 * (u : ℚ) ≤ 3 * Q := Iff.rfl

example (Q : ℚ) (u : ℕ) :
    InOrdinaryBankBulkDonorWindow Q u ↔
      7 * Q ≤ 5 * (u : ℚ) ∧ 20 * (u : ℚ) ≤ 29 * Q := Iff.rfl

example {n M P u : ℕ} {Q : ℚ} :
    (P, u) ∈ bankOrdinaryEligibleRelation n M Q ↔
      0 < Q ∧ P.Prime ∧ 0 < u ∧
        InOrdinaryBankMarkerInterval n Q P ∧
        InOrdinaryBankDonorWindow Q u ∧
        u ∈ Nat.smoothNumbers
          (Erdos390.Full.ArithmeticModel.yNat n + 1) ∧
        2 * n < P * u ∧ P * u ≤ M := by
  exact mem_bankOrdinaryEligibleRelation

example {n M P u : ℕ} {Q : ℚ} :
    (P, u) ∈ bankOrdinaryBulkRelation n M Q ↔
      0 < Q ∧ P.Prime ∧ 0 < u ∧
        InOrdinaryBankBulkDonorWindow Q u ∧
        u ∈ Nat.smoothNumbers
          (Erdos390.Full.ArithmeticModel.yNat n + 1) ∧
        2 * n < P * u ∧ P * u ≤ M := by
  exact mem_bankOrdinaryBulkRelation

example {n M : ℕ} {Q : ℚ} (hM : 10 * M ≤ 21 * n) :
    bankOrdinaryBulkRelation n M Q ⊆
      bankOrdinaryEligibleRelation n M Q :=
  bankOrdinaryBulkRelation_subset_eligible hM

example {n M P : ℕ} {Q : ℚ} (hP : 0 < P) :
    bankDonorMultiplicity (bankOrdinaryEligibleRelation n M Q) P ≤
      M / P - (2 * n) / P :=
  bankOrdinary_donorMultiplicity_le_div_sub_div hP

example (scale : SmallDescentScale) :
    InOrdinaryBankDonorWindow (smallDescentScaleValue scale)
      (bankOrdinarySmallDonor scale) :=
  bankOrdinarySmallDonor_mem_window scale

end

end Erdos390.WholePaper
