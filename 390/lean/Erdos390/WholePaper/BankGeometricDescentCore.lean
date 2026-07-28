import Erdos390.WholePaper.Definitions

/-!
# Literal finite algebra for the large-core bank descent

This module contains only the discrete ceiling, power-of-two avoidance, and
exact inequalities used by the geometric descent in Section 5.  It has no
donor-counting or prime-distribution input.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- A computational characterization of the nonzero powers of two.  Using
`Nat.log` makes the finite small-table certificate kernel reducible. -/
def IsPowerOfTwo (m : ℕ) : Prop :=
  m = 2 ^ Nat.log 2 m

instance decidableIsPowerOfTwo (m : ℕ) : Decidable (IsPowerOfTwo m) := by
  unfold IsPowerOfTwo
  exact inferInstance

/-- The computational definition has the expected mathematical meaning. -/
theorem isPowerOfTwo_iff (m : ℕ) :
    IsPowerOfTwo m ↔ ∃ k : ℕ, m = 2 ^ k := by
  constructor
  · intro h
    exact ⟨Nat.log 2 m, h⟩
  · rintro ⟨k, rfl⟩
    simp [IsPowerOfTwo, Nat.log_pow]

/-- Above the bottom range, the predecessor of a power of two is not itself
a power of two. -/
theorem pred_not_powerOfTwo_of_powerOfTwo {m : ℕ}
    (hm : IsPowerOfTwo m) (hm5 : 5 ≤ m) :
    ¬ IsPowerOfTwo (m - 1) := by
  obtain ⟨k, hk⟩ := (isPowerOfTwo_iff m).mp hm
  rw [isPowerOfTwo_iff]
  rintro ⟨l, hl⟩
  rw [hk] at hm5 hl
  cases k with
  | zero => norm_num at hm5
  | succ k =>
      cases l with
      | zero =>
          norm_num at hl
          omega
      | succ l =>
          have hkmod : (2 ^ Nat.succ k) % 2 = 0 := by
            simp [pow_succ]
          have hlmod : (2 ^ Nat.succ l) % 2 = 0 := by
            simp [pow_succ]
          have hkpos : 0 < 2 ^ Nat.succ k := by positivity
          have hpredmod : (2 ^ Nat.succ k - 1) % 2 = 1 := by omega
          have hmod := congrArg (fun x : ℕ ↦ x % 2) hl
          omega

/-- The literal integer ceiling `b₀ = ⌈4q/5⌉`. -/
def largeCoreCeil (q : ℕ) : ℕ :=
  (4 * q) ⌈/⌉ 5

/-- An explicit division formula for the ceiling. -/
theorem largeCoreCeil_eq_add_four_div (q : ℕ) :
    largeCoreCeil q = (4 * q + 4) / 5 := by
  simp [largeCoreCeil, Nat.ceilDiv_eq_add_pred_div]

/-- The literal large-core rule: subtract one precisely when the ceiling is
a power of two. -/
def largeCoreStep (q : ℕ) : ℕ :=
  if IsPowerOfTwo (largeCoreCeil q) then largeCoreCeil q - 1
  else largeCoreCeil q

theorem largeCoreStep_of_powerOfTwo {q : ℕ}
    (h : IsPowerOfTwo (largeCoreCeil q)) :
    largeCoreStep q = largeCoreCeil q - 1 := by
  simp [largeCoreStep, h]

theorem largeCoreStep_of_not_powerOfTwo {q : ℕ}
    (h : ¬ IsPowerOfTwo (largeCoreCeil q)) :
    largeCoreStep q = largeCoreCeil q := by
  simp [largeCoreStep, h]

theorem largeCoreCeil_ge_five {q : ℕ} (hq : 6 ≤ q) :
    5 ≤ largeCoreCeil q := by
  simp [largeCoreCeil, Nat.ceilDiv_eq_add_pred_div]
  omega

/-- The branch correction always produces a non-power. -/
theorem largeCoreStep_not_powerOfTwo {q : ℕ} (hq : 6 ≤ q) :
    ¬ IsPowerOfTwo (largeCoreStep q) := by
  unfold largeCoreStep
  split
  next h =>
    exact pred_not_powerOfTwo_of_powerOfTwo h (largeCoreCeil_ge_five hq)
  next h => exact h

/-- The large-core rule never drops below the terminal core `5`. -/
theorem largeCoreStep_ge_five {q : ℕ} (hq : 6 ≤ q) :
    5 ≤ largeCoreStep q := by
  unfold largeCoreStep
  split
  next h =>
    have hceil := largeCoreCeil_ge_five hq
    have hne : largeCoreCeil q ≠ 5 := by
      intro heq
      rw [heq] at h
      exact (by decide : ¬ IsPowerOfTwo 5) h
    omega
  next _ => exact largeCoreCeil_ge_five hq

theorem largeCoreStep_le_ceil (q : ℕ) :
    largeCoreStep q ≤ largeCoreCeil q := by
  unfold largeCoreStep
  split <;> omega

/-- Exact lower cross-multiplication for
`largeCoreStep q ≥ 4q/5 - 1`. -/
theorem largeCoreStep_cross_lower {q : ℕ} (hq : 6 ≤ q) :
    4 * q ≤ 5 * largeCoreStep q + 5 := by
  have hceil : 4 * q ≤ 5 * largeCoreCeil q := by
    rw [largeCoreCeil]
    exact (ceilDiv_le_iff_le_mul (a := 5) (b := 4 * q)
      (c := (4 * q) ⌈/⌉ 5) (by norm_num)).mp le_rfl
  unfold largeCoreStep
  split
  next _ =>
    have := largeCoreCeil_ge_five hq
    omega
  next _ => omega

/-- Exact upper cross-multiplication for
`largeCoreStep q < 4q/5 + 1`. -/
theorem largeCoreStep_cross_upper (q : ℕ) :
    5 * largeCoreStep q < 4 * q + 5 := by
  have hceil : 5 * largeCoreCeil q < 4 * q + 5 := by
    simp [largeCoreCeil, Nat.ceilDiv_eq_add_pred_div]
    omega
  have hle := largeCoreStep_le_ceil q
  omega

/-- In particular the core strictly decreases once `q ≥ 6`. -/
theorem largeCoreStep_lt_self {q : ℕ} (hq : 6 ≤ q) :
    largeCoreStep q < q := by
  have h := largeCoreStep_cross_upper q
  omega

/-- Exact integer form of the strict `17/20` contraction. -/
theorem largeCoreStep_cross_seventeen {q : ℕ} (hq : 21 ≤ q) :
    20 * largeCoreStep q < 17 * q := by
  have h := largeCoreStep_cross_upper q
  omega

/-- Literal rational form of the elementary upper ceiling estimate. -/
theorem largeCoreStep_le_four_fifths_add_one (q : ℕ) :
    (largeCoreStep q : ℚ) ≤ 4 * (q : ℚ) / 5 + 1 := by
  have h := largeCoreStep_cross_upper q
  have hq : (5 : ℚ) * largeCoreStep q < 4 * q + 5 := by
    exact_mod_cast h
  linarith

/-- Literal rational form of the `17/20` contraction. -/
theorem largeCoreStep_lt_seventeen_twentieths {q : ℕ} (hq : 21 ≤ q) :
    (largeCoreStep q : ℚ) < 17 * (q : ℚ) / 20 := by
  have h := largeCoreStep_cross_seventeen hq
  have hq' : (20 : ℚ) * largeCoreStep q < 17 * q := by
    exact_mod_cast h
  linarith

/-- A source core lies in the paper's geometric cell `(Q,4Q/3]`. -/
def CoreInGeometricCell (Q : ℚ) (q : ℕ) : Prop :=
  Q < (q : ℚ) ∧ (q : ℚ) ≤ 4 * Q / 3

/-- The source and target satisfy all three strict/non-strict cell
inequalities used by an ordinary descent edge. -/
def InGeometricDescentCell (Q : ℚ) (q b : ℕ) : Prop :=
  CoreInGeometricCell Q q ∧ 3 * Q / 4 < (b : ℚ)

/-- Complete large-cell algebra.  The source non-power hypothesis is retained
explicitly because it is the induction invariant of the paper's path. -/
theorem largeCoreStep_spec {Q : ℚ} {q : ℕ}
    (hQ : 20 < Q) (hq : 6 ≤ q) (hqNonpower : ¬ IsPowerOfTwo q)
    (hcell : CoreInGeometricCell Q q) :
    ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo (largeCoreStep q) ∧
      5 ≤ largeCoreStep q ∧
      largeCoreStep q < q ∧
      InGeometricDescentCell Q q (largeCoreStep q) ∧
      4 * q ≤ 5 * largeCoreStep q + 5 ∧
      5 * largeCoreStep q < 4 * q + 5 ∧
      20 * largeCoreStep q < 17 * q := by
  have hq20Q : (20 : ℚ) < q := hQ.trans hcell.1
  have hq20 : 20 < q := by exact_mod_cast hq20Q
  have hq21 : 21 ≤ q := by omega
  have hlower := largeCoreStep_cross_lower hq
  have hlowerQ : (4 : ℚ) * q ≤ 5 * largeCoreStep q + 5 := by
    exact_mod_cast hlower
  have hbCell : 3 * Q / 4 < (largeCoreStep q : ℚ) := by
    linarith [hcell.1]
  exact ⟨hqNonpower, largeCoreStep_not_powerOfTwo hq,
    largeCoreStep_ge_five hq, largeCoreStep_lt_self hq,
    ⟨hcell, hbCell⟩, hlower, largeCoreStep_cross_upper q,
    largeCoreStep_cross_seventeen hq21⟩

/-- Two exact `17/20` contractions starting below `4Q/3` finish below `Q`.
This is the arithmetic heart of the at-most-two-edges-per-large-cell claim. -/
theorem two_seventeen_twentieth_steps_below_cell
    {Q : ℚ} {q₀ q₁ q₂ : ℕ}
    (hQ : 20 < Q) (hq₀ : (q₀ : ℚ) ≤ 4 * Q / 3)
    (h₀₁ : 20 * q₁ < 17 * q₀)
    (h₁₂ : 20 * q₂ < 17 * q₁) :
    (q₂ : ℚ) < Q := by
  have hcomp : 400 * q₂ < 289 * q₀ := by omega
  have hcompQ : (400 : ℚ) * q₂ < 289 * q₀ := by
    exact_mod_cast hcomp
  linarith

/-- If the first target remains in the same large cell, the second target
has already crossed below that cell. -/
theorem two_consecutive_largeCoreSteps_leave_cell
    {Q : ℚ} {q : ℕ} (hQ : 20 < Q)
    (hsource : CoreInGeometricCell Q q)
    (hfirst : CoreInGeometricCell Q (largeCoreStep q)) :
    ((largeCoreStep (largeCoreStep q) : ℕ) : ℚ) < Q := by
  have hq20Q : (20 : ℚ) < q := hQ.trans hsource.1
  have hfirst20Q : (20 : ℚ) < largeCoreStep q := hQ.trans hfirst.1
  have hq21 : 21 ≤ q := by
    have : 20 < q := by exact_mod_cast hq20Q
    omega
  have hfirst21 : 21 ≤ largeCoreStep q := by
    have : 20 < largeCoreStep q := by exact_mod_cast hfirst20Q
    omega
  exact two_seventeen_twentieth_steps_below_cell hQ hsource.2
    (largeCoreStep_cross_seventeen hq21)
    (largeCoreStep_cross_seventeen hfirst21)

end

end Erdos390.WholePaper
