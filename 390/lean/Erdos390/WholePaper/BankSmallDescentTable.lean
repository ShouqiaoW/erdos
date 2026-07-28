import Erdos390.WholePaper.BankGeometricDescentCore

/-!
# Kernel-checked finite table for the five small descent scales

The fifteen source/target pairs are the literal table in Section 5.  All
checks here are finite: strict descent, avoidance of powers of two, and the
three rational cell inequalities.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The five nonbottom geometric scales at or below `20`. -/
inductive SmallDescentScale where
  | one
  | two
  | three
  | four
  | five
  deriving DecidableEq, Fintype

/-- Numerator of the exact rational value `Q_j = 4(4/3)^j`. -/
def smallDescentScaleNumerator : SmallDescentScale → ℕ
  | .one => 16
  | .two => 64
  | .three => 256
  | .four => 1024
  | .five => 4096

/-- Denominator of the exact rational value `Q_j = 4(4/3)^j`. -/
def smallDescentScaleDenominator : SmallDescentScale → ℕ
  | .one => 3
  | .two => 9
  | .three => 27
  | .four => 81
  | .five => 243

/-- The exact rational values `Q_j = 4(4/3)^j`, for `1 ≤ j ≤ 5`. -/
def smallDescentScaleValue (scale : SmallDescentScale) : ℚ :=
  smallDescentScaleNumerator scale / smallDescentScaleDenominator scale

/-- Literal source and target cell inequalities for one small scale. -/
def InSmallGeometricDescentCell
    (scale : SmallDescentScale) (q b : ℕ) : Prop :=
  smallDescentScaleValue scale < (q : ℚ) ∧
    (q : ℚ) ≤ 4 * smallDescentScaleValue scale / 3 ∧
    3 * smallDescentScaleValue scale / 4 < (b : ℚ)

/-- Exact natural-number cross-multiplications equivalent to the three cell
inequalities.  This is the form checked by kernel reduction. -/
def InSmallGeometricDescentCellCross
    (scale : SmallDescentScale) (q b : ℕ) : Prop :=
  smallDescentScaleNumerator scale <
      q * smallDescentScaleDenominator scale ∧
    3 * q * smallDescentScaleDenominator scale ≤
      4 * smallDescentScaleNumerator scale ∧
    3 * smallDescentScaleNumerator scale <
      4 * b * smallDescentScaleDenominator scale

instance decidableInSmallGeometricDescentCellCross
    (scale : SmallDescentScale) (q b : ℕ) :
    Decidable (InSmallGeometricDescentCellCross scale q b) := by
  unfold InSmallGeometricDescentCellCross
  exact inferInstance

private theorem cross_iff_rational_cell
    (N D q b : ℕ) (hD : 0 < D) :
    (N < q * D ∧ 3 * q * D ≤ 4 * N ∧ 3 * N < 4 * b * D) ↔
      (N : ℚ) / D < q ∧
        (q : ℚ) ≤ 4 * ((N : ℚ) / D) / 3 ∧
        3 * ((N : ℚ) / D) / 4 < b := by
  have hDQ : (0 : ℚ) < D := by exact_mod_cast hD
  have hthree : (0 : ℚ) < 3 := by norm_num
  have hfour : (0 : ℚ) < 4 := by norm_num
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    have h₁Q : (N : ℚ) < q * D := by exact_mod_cast h₁
    have h₂Q : (3 : ℚ) * q * D ≤ 4 * N := by exact_mod_cast h₂
    have h₃Q : (3 : ℚ) * N < 4 * b * D := by exact_mod_cast h₃
    refine ⟨(div_lt_iff₀ hDQ).2 ?_, ?_, ?_⟩
    · simpa only using h₁Q
    · apply (le_div_iff₀ hthree).2
      rw [show (4 : ℚ) * (N / D) = (4 * N) / D by ring]
      apply (le_div_iff₀ hDQ).2
      ring_nf at h₂Q ⊢
      exact h₂Q
    · apply (div_lt_iff₀ hfour).2
      rw [show (3 : ℚ) * (N / D) = (3 * N) / D by ring]
      apply (div_lt_iff₀ hDQ).2
      ring_nf at h₃Q ⊢
      exact h₃Q
  · rintro ⟨h₁, h₂, h₃⟩
    have h₁Q : (N : ℚ) < q * D := (div_lt_iff₀ hDQ).1 h₁
    have h₂Q : (3 : ℚ) * q * D ≤ 4 * N := by
      have h₂a := (le_div_iff₀ hthree).1 h₂
      rw [show (4 : ℚ) * (N / D) = (4 * N) / D by ring] at h₂a
      have h₂b := (le_div_iff₀ hDQ).1 h₂a
      ring_nf at h₂b ⊢
      exact h₂b
    have h₃Q : (3 : ℚ) * N < 4 * b * D := by
      have h₃a := (div_lt_iff₀ hfour).1 h₃
      rw [show (3 : ℚ) * (N / D) = (3 * N) / D by ring] at h₃a
      have h₃b := (div_lt_iff₀ hDQ).1 h₃a
      ring_nf at h₃b ⊢
      exact h₃b
    exact ⟨by exact_mod_cast h₁Q, by exact_mod_cast h₂Q,
      by exact_mod_cast h₃Q⟩

/-- The kernel-reducible cross-products are exactly the paper's literal
rational cell inequalities. -/
theorem inSmallGeometricDescentCellCross_iff
    (scale : SmallDescentScale) (q b : ℕ) :
    InSmallGeometricDescentCellCross scale q b ↔
      InSmallGeometricDescentCell scale q b := by
  unfold InSmallGeometricDescentCellCross InSmallGeometricDescentCell
    smallDescentScaleValue
  exact cross_iff_rational_cell _ _ q b (by
    cases scale <;> decide)

/-- Reusable certificate carried by every displayed small-table pair. -/
def IsCertifiedSmallDescentPair (q b : ℕ) : Prop :=
  6 ≤ q ∧
    ¬ IsPowerOfTwo q ∧
    ¬ IsPowerOfTwo b ∧
    5 ≤ b ∧
    b < q ∧
    ∃ scale : SmallDescentScale,
      InSmallGeometricDescentCellCross scale q b

instance decidableIsCertifiedSmallDescentPair (q b : ℕ) :
    Decidable (IsCertifiedSmallDescentPair q b) := by
  unfold IsCertifiedSmallDescentPair
  exact inferInstance

/-- A certificate with its witnessing small scale made explicit. -/
def IsCertifiedSmallDescentEntry
    (scale : SmallDescentScale) (q b : ℕ) : Prop :=
  6 ≤ q ∧
    ¬ IsPowerOfTwo q ∧
    ¬ IsPowerOfTwo b ∧
    5 ≤ b ∧
    b < q ∧
    InSmallGeometricDescentCellCross scale q b

instance decidableIsCertifiedSmallDescentEntry
    (scale : SmallDescentScale) (q b : ℕ) :
    Decidable (IsCertifiedSmallDescentEntry scale q b) := by
  unfold IsCertifiedSmallDescentEntry
  exact inferInstance

theorem certifiedSmallDescentPair_of_entry
    {scale : SmallDescentScale} {q b : ℕ}
    (h : IsCertifiedSmallDescentEntry scale q b) :
    IsCertifiedSmallDescentPair q b := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    scale, h.2.2.2.2.2⟩

/-- The unique small scale used by every source appearing in the table. -/
def smallDescentScaleForSource (q : ℕ) : SmallDescentScale :=
  if q ≤ 7 then .one
  else if q ≤ 9 then .two
  else if q ≤ 12 then .three
  else if q ≤ 15 then .four
  else .five

/-- The literal fifteen-pair descent table from Section 5. -/
def smallDescentTable : List (ℕ × ℕ) :=
  [(6, 5), (7, 6), (9, 7), (10, 9), (11, 9),
    (12, 10), (13, 11), (14, 12), (15, 12), (17, 14),
    (18, 15), (19, 15), (20, 15), (21, 17), (22, 18)]

/-- Every entry of the literal table has a kernel-checked certificate.  The
conjunction deliberately exposes all fifteen checks to the kernel. -/
theorem smallDescentTable_certified :
    IsCertifiedSmallDescentEntry .one 6 5 ∧
    IsCertifiedSmallDescentEntry .one 7 6 ∧
    IsCertifiedSmallDescentEntry .two 9 7 ∧
    IsCertifiedSmallDescentEntry .three 10 9 ∧
    IsCertifiedSmallDescentEntry .three 11 9 ∧
    IsCertifiedSmallDescentEntry .three 12 10 ∧
    IsCertifiedSmallDescentEntry .four 13 11 ∧
    IsCertifiedSmallDescentEntry .four 14 12 ∧
    IsCertifiedSmallDescentEntry .four 15 12 ∧
    IsCertifiedSmallDescentEntry .five 17 14 ∧
    IsCertifiedSmallDescentEntry .five 18 15 ∧
    IsCertifiedSmallDescentEntry .five 19 15 ∧
    IsCertifiedSmallDescentEntry .five 20 15 ∧
    IsCertifiedSmallDescentEntry .five 21 17 ∧
    IsCertifiedSmallDescentEntry .five 22 18 := by
  decide

/-- Membership in the table is a reusable terminal for all descent and cell
properties, without re-running the finite computation downstream. -/
theorem certifiedSmallDescentPair_of_mem
    {q b : ℕ} (hmem : (q, b) ∈ smallDescentTable) :
    6 ≤ q ∧
      ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo b ∧
      5 ≤ b ∧
      b < q ∧
      ∃ scale : SmallDescentScale,
        InSmallGeometricDescentCellCross scale q b := by
  change IsCertifiedSmallDescentPair q b
  simp only [smallDescentTable, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    apply certifiedSmallDescentPair_of_entry
      (scale := smallDescentScaleForSource q)
    injection h with hq hb
    subst q
    subst b
    decide

/-- Literal-rational version of the reusable table terminal. -/
theorem certifiedSmallDescentPair_literal_of_mem
    {q b : ℕ} (hmem : (q, b) ∈ smallDescentTable) :
    6 ≤ q ∧
      ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo b ∧
      5 ≤ b ∧
      b < q ∧
      ∃ scale : SmallDescentScale,
        InSmallGeometricDescentCell scale q b := by
  obtain ⟨hq, hqPower, hbPower, hb, hbq, scale, hcell⟩ :=
    certifiedSmallDescentPair_of_mem hmem
  exact ⟨hq, hqPower, hbPower, hb, hbq, scale,
    (inSmallGeometricDescentCellCross_iff scale q b).mp hcell⟩

/-- Every nonterminal target is itself a displayed source, so the finite
table can be iterated until the terminal core `5`. -/
theorem smallDescentTable_target_terminal_or_continues
    {q b : ℕ} (hmem : (q, b) ∈ smallDescentTable) :
    b = 5 ∨ ∃ c : ℕ, (b, c) ∈ smallDescentTable := by
  simp only [smallDescentTable, List.mem_cons, List.not_mem_nil,
    or_false] at hmem ⊢
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals simp_all

end

end Erdos390.WholePaper
