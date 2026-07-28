import Erdos390.Full.ArithmeticModel
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Exact multiple-counting moment bounds

The omitted-local-score step in Lemma 7.5 expands a valuation score into
divisor indicators and then counts common multiples.  This file proves that
finite combinatorial step for an arbitrary set of positive integers bounded
by one physical endpoint.  No smooth-number estimate or probability-model
assumption enters here.
-/

open scoped BigOperators

namespace Erdos390.Full.DivisibilityMomentBounds

open ArithmeticModel

noncomputable section

/-- A subset of positive integers up to `M` has at most `M / D` members
divisible by a modulus `D`. -/
theorem card_filter_dvd_le_div (S : Finset ℕ) {M D : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M) :
    (S.filter (D ∣ ·)).card ≤ M / D := by
  have hsubset : S.filter (D ∣ ·) ⊆
      (Finset.Ioc 0 M).filter (D ∣ ·) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨Finset.mem_Ioc.mpr ⟨hSpos m hm.1, hSle m hm.1⟩, hm.2⟩
  calc
    (S.filter (D ∣ ·)).card ≤
        ((Finset.Ioc 0 M).filter (D ∣ ·)).card :=
      Finset.card_le_card hsubset
    _ = M / D := Nat.Ioc_filter_dvd_card_eq_div M D

/-- A finite sum of an actual divisor indicator is the cardinality of the
corresponding filtered set. -/
theorem sum_divInd_eq_card_filter (S : Finset ℕ) (D : ℕ) :
    (∑ m ∈ S, divInd D m) = ((S.filter (D ∣ ·)).card : ℝ) := by
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [divInd]

/-- Products of divisor indicators combine by least common multiple. -/
theorem divInd_mul_eq_lcm (a b m : ℕ) :
    divInd a m * divInd b m = divInd (Nat.lcm a b) m := by
  by_cases ha : a ∣ m
  · by_cases hb : b ∣ m
    · have hlcm : Nat.lcm a b ∣ m := Nat.lcm_dvd ha hb
      simp [divInd, ha, hb, hlcm]
    · have hnlcm : ¬Nat.lcm a b ∣ m := by
        intro h
        exact hb ((Nat.dvd_lcm_right a b).trans h)
      simp [divInd, ha, hb, hnlcm]
  · have hnlcm : ¬Nat.lcm a b ∣ m := by
      intro h
      exact ha ((Nat.dvd_lcm_left a b).trans h)
    simp [divInd, ha, hnlcm]

/-- For coprime moduli, products of divisor indicators use the ordinary
product modulus. -/
theorem divInd_mul_eq_product_of_coprime {a b m : ℕ}
    (hcop : Nat.Coprime a b) :
    divInd a m * divInd b m = divInd (a * b) m := by
  rw [divInd_mul_eq_lcm, hcop.lcm_eq_mul]

/-- The finite divisor-indicator score attached to a family of moduli. -/
def divisorScore (R : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ a ∈ R, divInd a m

private theorem coprime_lcm_right {D a b : ℕ}
    (hDa : Nat.Coprime D a) (hDb : Nat.Coprime D b) :
    Nat.Coprime D (Nat.lcm a b) := by
  have hab : Nat.lcm a b ∣ a * b :=
    Nat.lcm_dvd (dvd_mul_right a b) (dvd_mul_left b a)
  exact (hDa.mul_right hDb).of_dvd_right hab

private theorem sum_divInd_le_real_div (S : Finset ℕ) {M N : ℕ}
    (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M) :
    (∑ m ∈ S, divInd N m) ≤ (M : ℝ) / (N : ℝ) := by
  rw [sum_divInd_eq_card_filter]
  calc
    ((S.filter (N ∣ ·)).card : ℝ) ≤ ((M / N : ℕ) : ℝ) := by
      exact_mod_cast card_filter_dvd_le_div S hSpos hSle
    _ ≤ (M : ℝ) / (N : ℝ) := Nat.cast_div_le

/-- Exact first-moment multiple-counting bound.  The coprimality condition
is precisely the paper's omission of the forced local primes from the
global score. -/
theorem sum_marked_divisorScore_le (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    (∑ m ∈ S, divInd D m * divisorScore R m) ≤
      ((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) := by
  have hterm : ∀ a ∈ R,
      (∑ m ∈ S, divInd (D * a) m) ≤
        ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
    intro a ha
    calc
      (∑ m ∈ S, divInd (D * a) m) ≤
          (M : ℝ) / ((D * a : ℕ) : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
        have hD0 : (D : ℝ) ≠ 0 := by positivity
        have ha0 : (a : ℝ) ≠ 0 := by
          exact_mod_cast (hRpos a ha).ne'
        norm_num only [Nat.cast_mul]
        field_simp [hD0, ha0]
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) =
        ∑ a ∈ R, ∑ m ∈ S, divInd (D * a) m := by
      unfold divisorScore
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro m hm
      exact divInd_mul_eq_product_of_coprime (hcop a ha)
    _ ≤ ∑ a ∈ R,
        ((M : ℝ) / (D : ℝ)) * (1 / (a : ℝ)) := by
      exact Finset.sum_le_sum fun a ha => hterm a ha
    _ = ((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) := by
      rw [Finset.mul_sum]

/-- Exact second-moment multiple-counting bound.  Same-modulus terms are
handled by `lcm`, so this statement already includes the diagonal
prime-power ledger rather than silently treating all marks as independent.
-/
theorem sum_marked_divisorScore_sq_le (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    (∑ m ∈ S, divInd D m * divisorScore R m ^ 2) ≤
      ((M : ℝ) / (D : ℝ)) *
        ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ) := by
  have hterm : ∀ a ∈ R, ∀ b ∈ R,
      (∑ m ∈ S, divInd (D * Nat.lcm a b) m) ≤
        ((M : ℝ) / (D : ℝ)) *
          (1 / (Nat.lcm a b : ℝ)) := by
    intro a ha b hb
    have hlcmPos : 0 < Nat.lcm a b :=
      Nat.lcm_pos (hRpos a ha) (hRpos b hb)
    calc
      (∑ m ∈ S, divInd (D * Nat.lcm a b) m) ≤
          (M : ℝ) / ((D * Nat.lcm a b : ℕ) : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = ((M : ℝ) / (D : ℝ)) *
          (1 / (Nat.lcm a b : ℝ)) := by
        have hD0 : (D : ℝ) ≠ 0 := by positivity
        have hlcm0 : (Nat.lcm a b : ℝ) ≠ 0 := by positivity
        norm_num only [Nat.cast_mul]
        field_simp [hD0, hlcm0]
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m ^ 2) =
        ∑ a ∈ R, ∑ b ∈ R,
          ∑ m ∈ S, divInd (D * Nat.lcm a b) m := by
      unfold divisorScore
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro m hm
      rw [divInd_mul_eq_lcm]
      exact divInd_mul_eq_product_of_coprime
        (coprime_lcm_right (hcop a ha) (hcop b hb))
    _ ≤ ∑ a ∈ R, ∑ b ∈ R,
        ((M : ℝ) / (D : ℝ)) *
          (1 / (Nat.lcm a b : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum fun b hb => hterm a ha b hb
    _ = ((M : ℝ) / (D : ℝ)) *
        ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ) := by
      simp only [Finset.mul_sum]

/-- Exact first marked moment without a coprimality assumption.  The price
for retaining a forced local prime in the score is the literal lcm ledger;
no product-denominator replacement is made. -/
theorem sum_marked_divisorScore_lcm_le (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a) :
    (∑ m ∈ S, divInd D m * divisorScore R m) ≤
      (M : ℝ) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
  have hterm : ∀ a ∈ R,
      (∑ m ∈ S, divInd (Nat.lcm D a) m) ≤
        (M : ℝ) * (1 / (Nat.lcm D a : ℝ)) := by
    intro a ha
    have hlcmPos : 0 < Nat.lcm D a := Nat.lcm_pos hD (hRpos a ha)
    calc
      (∑ m ∈ S, divInd (Nat.lcm D a) m) ≤
          (M : ℝ) / (Nat.lcm D a : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = (M : ℝ) * (1 / (Nat.lcm D a : ℝ)) := by ring
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) =
        ∑ a ∈ R, ∑ m ∈ S, divInd (Nat.lcm D a) m := by
      unfold divisorScore
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro m hm
      exact divInd_mul_eq_lcm D a m
    _ ≤ ∑ a ∈ R,
        (M : ℝ) * (1 / (Nat.lcm D a : ℝ)) := by
      exact Finset.sum_le_sum fun a ha ↦ hterm a ha
    _ = (M : ℝ) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
      rw [Finset.mul_sum]

/-- Exact second marked moment without omitting the forced local prime.
The denominator is the genuine three-way lcm
`lcm D (lcm a b)`.  This is the finite ledger needed by the nuisance-row
Taylor remainder. -/
theorem sum_marked_divisorScore_sq_lcm_le
    (S R : Finset ℕ) {M D : ℕ}
    (hD : 0 < D) (hSpos : ∀ m ∈ S, 0 < m)
    (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a) :
    (∑ m ∈ S, divInd D m * divisorScore R m ^ 2) ≤
      (M : ℝ) *
        ∑ a ∈ R, ∑ b ∈ R,
          1 / (Nat.lcm D (Nat.lcm a b) : ℝ) := by
  have hterm : ∀ a ∈ R, ∀ b ∈ R,
      (∑ m ∈ S, divInd (Nat.lcm D (Nat.lcm a b)) m) ≤
        (M : ℝ) *
          (1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) := by
    intro a ha b hb
    have habPos : 0 < Nat.lcm a b :=
      Nat.lcm_pos (hRpos a ha) (hRpos b hb)
    have htotalPos : 0 < Nat.lcm D (Nat.lcm a b) :=
      Nat.lcm_pos hD habPos
    calc
      (∑ m ∈ S, divInd (Nat.lcm D (Nat.lcm a b)) m) ≤
          (M : ℝ) / (Nat.lcm D (Nat.lcm a b) : ℝ) :=
        sum_divInd_le_real_div S hSpos hSle
      _ = (M : ℝ) *
          (1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) := by ring
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m ^ 2) =
        ∑ a ∈ R, ∑ b ∈ R,
          ∑ m ∈ S, divInd (Nat.lcm D (Nat.lcm a b)) m := by
      unfold divisorScore
      simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro m hm
      rw [divInd_mul_eq_lcm]
      exact divInd_mul_eq_lcm D (Nat.lcm a b) m
    _ ≤ ∑ a ∈ R, ∑ b ∈ R,
        (M : ℝ) *
          (1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum fun b hb ↦ hterm a ha b hb
    _ = (M : ℝ) *
        ∑ a ∈ R, ∑ b ∈ R,
          1 / (Nat.lcm D (Nat.lcm a b) : ℝ) := by
      simp only [Finset.mul_sum]

/-- Uniform average over a nonempty finite cell. -/
def uniformAverage (S : Finset ℕ) (F : ℕ → ℝ) : ℝ :=
  (∑ m ∈ S, F m) / (S.card : ℝ)

private theorem endpoint_card_ratio_le {S : Finset ℕ} {M : ℕ} {c : ℝ}
    (hc : 0 < c) (hM : 0 < M)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ)) :
    (M : ℝ) / (S.card : ℝ) ≤ 1 / c := by
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hMle : (M : ℝ) ≤ (S.card : ℝ) / c :=
    (le_div_iff₀ hc).2 (by simpa [mul_comm] using hcard)
  calc
    (M : ℝ) / (S.card : ℝ) ≤
        ((S.card : ℝ) / c) / (S.card : ℝ) :=
      div_le_div_of_nonneg_right hMle hcardPos.le
    _ = 1 / c := by field_simp [ne_of_gt hc, ne_of_gt hcardPos]

/-- Normalized first omitted-score moment.  A lower density bound for the
cell converts the exact endpoint count into the paper's `1/D` scale. -/
theorem uniformAverage_marked_divisorScore_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    uniformAverage S (fun m => divInd D m * divisorScore R m) ≤
      (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ) := by
  have hsum := sum_marked_divisorScore_le S R hD hSpos hSle hRpos hcop
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hrecipNonneg : 0 ≤ ∑ a ∈ R, 1 / (a : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    positivity
  have hfactor : 0 ≤ (1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ) :=
    mul_nonneg (by positivity) hrecipNonneg
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) / (S.card : ℝ) ≤
        (((M : ℝ) / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) /
          (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ((1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) := by ring
    _ ≤ (1 / c) *
        ((1 / (D : ℝ)) * ∑ a ∈ R, 1 / (a : ℝ)) :=
      mul_le_mul_of_nonneg_right hratio hfactor
    _ = (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ) := by ring

/-- Normalized second omitted-score moment, retaining the exact same-prime
`lcm` contribution. -/
theorem uniformAverage_marked_divisorScore_sq_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a)
    (hcop : ∀ a ∈ R, Nat.Coprime D a) :
    uniformAverage S (fun m => divInd D m * divisorScore R m ^ 2) ≤
      (1 / (c * (D : ℝ))) *
        ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ) := by
  have hsum :=
    sum_marked_divisorScore_sq_le S R hD hSpos hSle hRpos hcop
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hrecipNonneg :
      0 ≤ ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    have hlcm : 0 < Nat.lcm a b :=
      Nat.lcm_pos (hRpos a ha) (hRpos b hb)
    positivity
  have hfactor :
      0 ≤ (1 / (D : ℝ)) *
        ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ) :=
    mul_nonneg (by positivity) hrecipNonneg
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m ^ 2) / (S.card : ℝ) ≤
        (((M : ℝ) / (D : ℝ)) *
          ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ)) /
            (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ((1 / (D : ℝ)) *
          ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ)) := by ring
    _ ≤ (1 / c) *
        ((1 / (D : ℝ)) *
          ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ)) :=
      mul_le_mul_of_nonneg_right hratio hfactor
    _ = (1 / (c * (D : ℝ))) *
        ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ) := by ring

/-- Normalized literal-lcm first moment.  Unlike
`uniformAverage_marked_divisorScore_le`, this theorem also applies when the
score family contains the forced prime. -/
theorem uniformAverage_marked_divisorScore_lcm_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a) :
    uniformAverage S (fun m ↦ divInd D m * divisorScore R m) ≤
      (1 / c) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
  have hsum := sum_marked_divisorScore_lcm_le
    S R hD hSpos hSle hRpos
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hledger0 : 0 ≤
      ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    have hlcm : 0 < Nat.lcm D a := Nat.lcm_pos hD (hRpos a ha)
    positivity
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m) / (S.card : ℝ) ≤
        ((M : ℝ) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ)) /
          (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) := by ring
    _ ≤ (1 / c) * ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hledger0

/-- Normalized literal three-way-lcm second moment. -/
theorem uniformAverage_marked_divisorScore_sq_lcm_le
    (S R : Finset ℕ) {M D : ℕ} {c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hRpos : ∀ a ∈ R, 0 < a) :
    uniformAverage S (fun m ↦ divInd D m * divisorScore R m ^ 2) ≤
      (1 / c) *
        ∑ a ∈ R, ∑ b ∈ R,
          1 / (Nat.lcm D (Nat.lcm a b) : ℝ) := by
  have hsum := sum_marked_divisorScore_sq_lcm_le
    S R hD hSpos hSle hRpos
  have hcardPos : 0 < (S.card : ℝ) := by
    have hcM : 0 < c * (M : ℝ) := mul_pos hc (by exact_mod_cast hM)
    exact hcM.trans_le hcard
  have hratio := endpoint_card_ratio_le hc hM hcard
  have hledger0 : 0 ≤
      ∑ a ∈ R, ∑ b ∈ R,
        1 / (Nat.lcm D (Nat.lcm a b) : ℝ) := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    have hab : 0 < Nat.lcm a b :=
      Nat.lcm_pos (hRpos a ha) (hRpos b hb)
    have htotal : 0 < Nat.lcm D (Nat.lcm a b) := Nat.lcm_pos hD hab
    positivity
  unfold uniformAverage
  calc
    (∑ m ∈ S, divInd D m * divisorScore R m ^ 2) /
          (S.card : ℝ) ≤
        ((M : ℝ) *
          ∑ a ∈ R, ∑ b ∈ R,
            1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) /
              (S.card : ℝ) :=
      div_le_div_of_nonneg_right hsum hcardPos.le
    _ = ((M : ℝ) / (S.card : ℝ)) *
        ∑ a ∈ R, ∑ b ∈ R,
          1 / (Nat.lcm D (Nat.lcm a b) : ℝ) := by ring
    _ ≤ (1 / c) *
        ∑ a ∈ R, ∑ b ∈ R,
          1 / (Nat.lcm D (Nat.lcm a b) : ℝ) :=
      mul_le_mul_of_nonneg_right hratio hledger0

end

end Erdos390.Full.DivisibilityMomentBounds
