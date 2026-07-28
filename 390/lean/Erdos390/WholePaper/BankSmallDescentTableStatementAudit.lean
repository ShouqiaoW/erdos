import Erdos390.WholePaper.BankSmallDescentTable

/-! Expanded statement audit for the literal fifteen-pair small table. -/

namespace Erdos390.WholePaper

noncomputable section

example : smallDescentTable =
    [(6, 5), (7, 6), (9, 7), (10, 9), (11, 9),
      (12, 10), (13, 11), (14, 12), (15, 12), (17, 14),
      (18, 15), (19, 15), (20, 15), (21, 17), (22, 18)] := rfl

example (scale : SmallDescentScale) (q b : ℕ) :
    (smallDescentScaleNumerator scale <
        q * smallDescentScaleDenominator scale ∧
      3 * q * smallDescentScaleDenominator scale ≤
        4 * smallDescentScaleNumerator scale ∧
      3 * smallDescentScaleNumerator scale <
        4 * b * smallDescentScaleDenominator scale) ↔
    (smallDescentScaleValue scale < (q : ℚ) ∧
      (q : ℚ) ≤ 4 * smallDescentScaleValue scale / 3 ∧
      3 * smallDescentScaleValue scale / 4 < (b : ℚ)) := by
  simpa only [InSmallGeometricDescentCellCross,
    InSmallGeometricDescentCell] using
      inSmallGeometricDescentCellCross_iff scale q b

example {q b : ℕ}
    (hmem : (q, b) ∈
      [(6, 5), (7, 6), (9, 7), (10, 9), (11, 9),
        (12, 10), (13, 11), (14, 12), (15, 12), (17, 14),
        (18, 15), (19, 15), (20, 15), (21, 17), (22, 18)]) :
    6 ≤ q ∧
      ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo b ∧
      5 ≤ b ∧ b < q ∧
      ∃ scale : SmallDescentScale,
        smallDescentScaleValue scale < (q : ℚ) ∧
          (q : ℚ) ≤ 4 * smallDescentScaleValue scale / 3 ∧
          3 * smallDescentScaleValue scale / 4 < (b : ℚ) := by
  have hmem' : (q, b) ∈ smallDescentTable := by
    simpa only [smallDescentTable] using hmem
  simpa only [InSmallGeometricDescentCell] using
    certifiedSmallDescentPair_literal_of_mem hmem'

example {q b : ℕ} (hmem : (q, b) ∈ smallDescentTable) :
    b = 5 ∨ ∃ c : ℕ, (b, c) ∈ smallDescentTable :=
  smallDescentTable_target_terminal_or_continues hmem

end

end Erdos390.WholePaper
