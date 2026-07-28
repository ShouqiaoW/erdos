import Erdos390.WholePaper.BankRoughSignatures

/-!
# Complete rough/smooth decomposition

The complete rough label retains exactly the prime-power coordinates above
`y`.  This file defines the complementary literal quotient and proves that
the two pieces recover the original natural number, with exact complementary
factorizations and no auxiliary decomposition hypothesis.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The literal complementary factor after removing the complete rough
label. -/
def completeSmoothPart (y a : ℕ) : ℕ :=
  a / completeRoughLabel y a

/-! ## Positivity, divisibility, and product recovery -/

/-- A complete rough label is always positive, including for `a = 0`, when
the empty factorization gives label `1`. -/
theorem completeRoughLabel_pos (y a : ℕ) :
    0 < completeRoughLabel y a := by
  rw [completeRoughLabel]
  apply Nat.prod_pow_pos_of_zero_notMem_support
  rw [Finsupp.notMem_support_iff, completeRoughSignature_apply]
  simp

theorem completeRoughLabel_ne_zero (y a : ℕ) :
    completeRoughLabel y a ≠ 0 :=
  (completeRoughLabel_pos y a).ne'

/-- Literal Finsupp form of the high-prime factorization. -/
theorem completeRoughLabel_factorization_eq_filter_gt (y a : ℕ) :
    (completeRoughLabel y a).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughSignature] using
    completeRoughLabel_factorization y a

/-- Coordinate form of the exact high-prime factorization. -/
theorem completeRoughLabel_factorization_apply (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeRoughLabel_factorization_eq_filter_gt y a)
  simpa only [Finsupp.filter_apply] using h

/-- The retained high-prime product is a literal divisor of the original
number. -/
theorem completeRoughLabel_dvd (y a : ℕ) :
    completeRoughLabel y a ∣ a := by
  by_cases ha : a = 0
  · rw [ha]
    exact dvd_zero _
  · rw [← Nat.factorization_le_iff_dvd
      (completeRoughLabel_ne_zero y a) ha,
      completeRoughLabel_factorization_eq_filter_gt]
    intro p
    rw [Finsupp.filter_apply]
    split_ifs <;> simp

/-- The requested multiplication direction: the original number is the
rough label times its literal complementary quotient. -/
theorem completeRough_decomposition (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a := by
  calc
    a = a / completeRoughLabel y a * completeRoughLabel y a :=
      (Nat.div_mul_cancel (completeRoughLabel_dvd y a)).symm
    _ = completeRoughLabel y a * (a / completeRoughLabel y a) :=
      Nat.mul_comm _ _
    _ = completeRoughLabel y a * completeSmoothPart y a := rfl

/-- Product recovery in the opposite orientation. -/
theorem completeRoughLabel_mul_completeSmoothPart (y a : ℕ) :
    completeRoughLabel y a * completeSmoothPart y a = a :=
  (completeRough_decomposition y a).symm

/-! ## The complementary low-prime factorization -/

/-- The quotient retains exactly the complementary coordinates `p ≤ y`. -/
theorem completeSmoothPart_factorization_eq_filter_le (y a : ℕ) :
    (completeSmoothPart y a).factorization =
      a.factorization.filter (fun p ↦ p ≤ y) := by
  rw [completeSmoothPart,
    Nat.factorization_div (completeRoughLabel_dvd y a),
    completeRoughLabel_factorization_eq_filter_gt]
  ext p
  simp only [Finsupp.filter_apply]
  by_cases hpLow : p ≤ y
  · have hpNotHigh : ¬y < p := Nat.not_lt_of_ge hpLow
    simp [hpLow, hpNotHigh]
  · have hpHigh : y < p := Nat.lt_of_not_ge hpLow
    simp [hpLow, hpHigh]

/-- Coordinate form of the exact low-prime factorization. -/
theorem completeSmoothPart_factorization_apply (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 := by
  have h := congrArg (fun f : ℕ →₀ ℕ ↦ f p)
    (completeSmoothPart_factorization_eq_filter_le y a)
  simpa only [Finsupp.filter_apply] using h

/-- Nonzero high-part coordinates lie strictly above the cutoff. -/
theorem completeRoughLabel_factorization_support
    {y a p : ℕ}
    (hp : (completeRoughLabel y a).factorization p ≠ 0) :
    y < p := by
  rw [completeRoughLabel_factorization_apply] at hp
  by_contra hpHigh
  simp [hpHigh] at hp

/-- Nonzero smooth-part coordinates lie weakly below the cutoff. -/
theorem completeSmoothPart_factorization_support
    {y a p : ℕ}
    (hp : (completeSmoothPart y a).factorization p ≠ 0) :
    p ≤ y := by
  rw [completeSmoothPart_factorization_apply] at hp
  by_contra hpLow
  simp [hpLow] at hp

/-- Every prime divisor of the complete rough label is above `y`. -/
theorem prime_dvd_completeRoughLabel_gt
    {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) :
    y < p := by
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeRoughLabel_ne_zero y a) hpDvd
  exact completeRoughLabel_factorization_support hfactorPos.ne'

/-- For a positive original number, the complementary quotient is positive. -/
theorem completeSmoothPart_pos {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a := by
  rw [completeSmoothPart]
  apply Nat.div_pos
  · exact Nat.le_of_dvd ha (completeRoughLabel_dvd y a)
  · exact completeRoughLabel_pos y a

/-- For a positive original number, the complementary quotient is literally
`(y+1)`-smooth in Mathlib's positive-number convention. -/
theorem completeSmoothPart_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) := by
  rw [Nat.mem_smoothNumbers']
  intro p hp hpDvd
  have hfactorPos := hp.factorization_pos_of_dvd
    (completeSmoothPart_pos ha).ne' hpDvd
  have hpLow : p ≤ y :=
    completeSmoothPart_factorization_support hfactorPos.ne'
  omega

/-! ## Uniqueness and the smooth-label criterion -/

/-- Uniqueness of the decomposition under the literal complementary
factorization-support conditions. -/
theorem completeRoughDecomposition_unique
    {y a rough smooth : ℕ}
    (hrough : rough ≠ 0) (hsmooth : smooth ≠ 0)
    (hproduct : a = rough * smooth)
    (hroughSupport : ∀ p, rough.factorization p ≠ 0 → y < p)
    (hsmoothSupport : ∀ p, smooth.factorization p ≠ 0 → p ≤ y) :
    rough = completeRoughLabel y a ∧
      smooth = completeSmoothPart y a := by
  have hfactorization :
      a.factorization = rough.factorization + smooth.factorization := by
    rw [hproduct, Nat.factorization_mul hrough hsmooth]
  have hroughEq : rough = completeRoughLabel y a := by
    apply Nat.eq_of_factorization_eq' hrough
      (completeRoughLabel_ne_zero y a)
    rw [completeRoughLabel_factorization_eq_filter_gt]
    ext p
    have hcoordinate :=
      congrArg (fun f : ℕ →₀ ℕ ↦ f p) hfactorization
    simp only [Finsupp.add_apply] at hcoordinate
    rw [Finsupp.filter_apply]
    by_cases hpHigh : y < p
    · rw [if_pos hpHigh]
      have hsmoothZero : smooth.factorization p = 0 := by
        by_contra hsmoothNonzero
        exact (Nat.not_le_of_gt hpHigh)
          (hsmoothSupport p hsmoothNonzero)
      simpa only [hsmoothZero, add_zero] using hcoordinate.symm
    · rw [if_neg hpHigh]
      by_contra hroughNonzero
      exact hpHigh (hroughSupport p hroughNonzero)
  refine ⟨hroughEq, ?_⟩
  apply Nat.mul_left_cancel (completeRoughLabel_pos y a)
  calc
    completeRoughLabel y a * smooth = rough * smooth := by
      rw [hroughEq]
    _ = a := hproduct.symm
    _ = completeRoughLabel y a * completeSmoothPart y a :=
      completeRough_decomposition y a

/-- For positive `a`, the rough label is `1` exactly when `a` is
`(y+1)`-smooth. -/
theorem completeRoughLabel_eq_one_iff_mem_smoothNumbers
    {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    have haPart : a = completeSmoothPart y a := by
      simpa only [hlabel, one_mul] using
        completeRough_decomposition y a
    rw [haPart]
    exact completeSmoothPart_mem_smoothNumbers ha
  · intro haSmooth
    by_contra hlabel
    obtain ⟨p, hp, hpDvdLabel⟩ :=
      Nat.exists_prime_and_dvd hlabel
    have hpHigh : y < p :=
      prime_dvd_completeRoughLabel_gt hp hpDvdLabel
    have hpDvdA : p ∣ a :=
      hpDvdLabel.trans (completeRoughLabel_dvd y a)
    have hpLow :=
      (Nat.mem_smoothNumbers').mp haSmooth p hp hpDvdA
    omega

/-- The exact total version records the unavoidable zero exception in
Mathlib's definition of smooth numbers. -/
theorem completeRoughLabel_eq_one_iff_eq_zero_or_mem_smoothNumbers
    (y a : ℕ) :
    completeRoughLabel y a = 1 ↔
      a = 0 ∨ a ∈ Nat.smoothNumbers (y + 1) := by
  constructor
  · intro hlabel
    by_cases ha : a = 0
    · exact Or.inl ha
    · exact Or.inr
        ((completeRoughLabel_eq_one_iff_mem_smoothNumbers
          (Nat.pos_of_ne_zero ha)).mp hlabel)
  · rintro (rfl | haSmooth)
    · rw [completeRoughLabel, completeRoughSignature,
        Nat.factorization_zero, Finsupp.filter_zero,
        Finsupp.prod_zero_index]
    · exact
        (completeRoughLabel_eq_one_iff_mem_smoothNumbers
          (Nat.pos_of_ne_zero
            (Nat.ne_zero_of_mem_smoothNumbers haSmooth))).mpr haSmooth

end

end Erdos390.WholePaper
