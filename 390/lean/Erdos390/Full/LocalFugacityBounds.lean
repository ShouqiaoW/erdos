import Erdos390.Full.LocalFugacity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Uniform bounds for restored local fugacity coefficients

The local restoration in Lemma 7.5 must retain both the factor `1 / L`
and the geometric factor `p^{-r}`.  Cardinality bounds on the exponent set
are too crude for that purpose.  This module proves the required shifted
geometric estimates directly for the actual coefficients
`exp (eta/L)^a - exp (eta/L)^(a-1)`.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityBounds

open LocalFugacity

noncomputable section

private theorem sub_injective_on_Icc (k A : ℕ) :
    Set.InjOn (fun a : ℕ ↦ a - k) (↑(Finset.Icc k A) : Set ℕ) := by
  intro a ha b hb hab
  have hka : k ≤ a := (Finset.mem_Icc.mp ha).1
  have hkb : k ≤ b := (Finset.mem_Icc.mp hb).1
  change a - k = b - k at hab
  calc
    a = (a - k) + k := (Nat.sub_add_cancel hka).symm
    _ = (b - k) + k := congrArg (fun z : ℕ ↦ z + k) hab
    _ = b := Nat.sub_add_cancel hkb

/-- Every finite shifted half-geometric tail is bounded by the complete
geometric series. -/
theorem sum_shifted_half_le_two (k A : ℕ) :
    (∑ a ∈ Finset.Icc k A,
        (1 / (2 : ℝ)) ^ (a - k)) ≤ 2 := by
  let s := Finset.Icc k A
  let g : ℕ → ℕ := fun a ↦ a - k
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc k A
  have heq :
      (∑ a ∈ s, (1 / (2 : ℝ)) ^ (a - k)) =
        ∑ i ∈ s.image g, (1 / (2 : ℝ)) ^ i := by
    symm
    rw [Finset.sum_image]
    exact hinj
  rw [heq]
  exact (summable_geometric_two.sum_le_tsum (s.image g)
    (fun i hi ↦ by positivity)).trans_eq tsum_geometric_two

private def linearHalfTerm (i : ℕ) : ℝ :=
  ((i : ℝ) + 3) * (1 / (2 : ℝ)) ^ i

private theorem summable_linearHalfTerm : Summable linearHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  convert hlin.add hconst using 1
  funext i
  unfold linearHalfTerm
  ring

private theorem tsum_linearHalfTerm_eq_eight :
    ∑' i : ℕ, linearHalfTerm i = 8 := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable
      (fun i : ℕ ↦ 3 * (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two.mul_left 3
  rw [show linearHalfTerm = fun i : ℕ ↦
      (i : ℝ) * (1 / (2 : ℝ)) ^ i +
        3 * (1 / (2 : ℝ)) ^ i by
    funext i
    unfold linearHalfTerm
    ring]
  rw [hlin.tsum_add hconst,
    tsum_coe_mul_geometric_of_norm_lt_one hx,
    tsum_mul_left, tsum_geometric_two]
  norm_num

/-- Shifted arithmetic--geometric tails have an absolute numerical bound.
This is the aggregate `r+1` ledger used below. -/
theorem sum_shifted_linear_half_le_eight (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) ≤ 8 := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s, ((r : ℝ) + 1) *
          (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, linearHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      unfold linearHalfTerm g
      norm_num only [Nat.cast_sub hr2]
      ring
    · exact hinj
  rw [heq]
  exact (summable_linearHalfTerm.sum_le_tsum (s.image g)
      (fun i hi ↦ by unfold linearHalfTerm; positivity)).trans_eq
    tsum_linearHalfTerm_eq_eight

/-- A finite reciprocal-power tail beginning at exponent `r+1` has the
same bound as the corresponding infinite geometric tail. -/
theorem sum_inv_pow_tail_le {p r A : ℕ} (hp : 2 ≤ p) :
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      2 / (p : ℝ) ^ (r + 1) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    (∑ a ∈ Finset.Icc (r + 1) A,
        1 / ((p ^ a : ℕ) : ℝ)) ≤
      ∑ a ∈ Finset.Icc (r + 1) A,
        (1 / (p : ℝ) ^ (r + 1)) *
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      apply Finset.sum_le_sum
      intro a ha
      have hra : r + 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have hpPow : (2 : ℝ) ^ (a - (r + 1)) ≤
          (p : ℝ) ^ (a - (r + 1)) := by gcongr
      have haSplit : a = (r + 1) + (a - (r + 1)) := by omega
      have hpowSplit : (p : ℝ) ^ a =
          (p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1)) := by
        conv_lhs => rw [haSplit]
        rw [pow_add]
      norm_num only [Nat.cast_pow]
      rw [hpowSplit]
      calc
        1 / ((p : ℝ) ^ (r + 1) * (p : ℝ) ^ (a - (r + 1))) ≤
            1 / ((p : ℝ) ^ (r + 1) *
              (2 : ℝ) ^ (a - (r + 1))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ (r + 1)) *
            (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ (r + 1)) *
        ∑ a ∈ Finset.Icc (r + 1) A,
          (1 / (2 : ℝ)) ^ (a - (r + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ (r + 1)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_shifted_half_le_two (r + 1) A)
        (by positivity)
    _ = 2 / (p : ℝ) ^ (r + 1) := by ring

/-- The complete finite `r+1` reciprocal-power ledger begins at `p^{-2}`
with an absolute constant. -/
theorem sum_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) / (p : ℝ) ^ r) ≤
      8 / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hnum : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2)) ≤
            ((r : ℝ) + 1) /
              ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2)) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            (((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          ((r : ℝ) + 1) * (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * 8 :=
      mul_le_mul_of_nonneg_left (sum_shifted_linear_half_le_eight R)
        (by positivity)
    _ = 8 / (p : ℝ) ^ 2 := by ring

private def quadraticHalfTerm (i : ℕ) : ℝ :=
  (((2 * i + 1) * (i + 3) : ℕ) : ℝ) *
    (1 / (2 : ℝ)) ^ i

private theorem summable_quadraticHalfTerm : Summable quadraticHalfTerm := by
  have hx : ‖(1 / (2 : ℝ))‖ < 1 := by norm_num
  have hsq : Summable
      (fun i : ℕ ↦ (i : ℝ) ^ 2 * (1 / (2 : ℝ)) ^ i) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hx
  have hlin : Summable
      (fun i : ℕ ↦ (i : ℝ) * (1 / (2 : ℝ)) ^ i) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hx).summable
  have hconst : Summable (fun i : ℕ ↦ (1 / (2 : ℝ)) ^ i) :=
    summable_geometric_two
  convert ((hsq.mul_left 2).add (hlin.mul_left 7)).add
    (hconst.mul_left 3) using 1
  funext i
  unfold quadraticHalfTerm
  push_cast
  ring

/-- A fixed absolute constant for the diagonal coefficient ledger.  Its
precise numerical value is irrelevant; what matters is that it is defined
before every tilt box and is proved finite by an arithmetic--geometric
series. -/
def quadraticHalfMass : ℝ := ∑' i : ℕ, quadraticHalfTerm i

theorem quadraticHalfMass_nonneg : 0 ≤ quadraticHalfMass := by
  unfold quadraticHalfMass
  exact tsum_nonneg fun i ↦ by
    unfold quadraticHalfTerm
    positivity

theorem sum_shifted_quadratic_half_le_mass (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R,
        (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
          (1 / (2 : ℝ)) ^ (r - 2)) ≤ quadraticHalfMass := by
  let s := Finset.Icc 2 R
  let g : ℕ → ℕ := fun r ↦ r - 2
  have hinj : Set.InjOn g (↑s : Set ℕ) := by
    simpa only [s, g] using sub_injective_on_Icc 2 R
  have heq :
      (∑ r ∈ s,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) =
        ∑ i ∈ s.image g, quadraticHalfTerm i := by
    symm
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hweight : 2 * r - 3 = 2 * (r - 2) + 1 := by omega
      have hshift : r + 1 = (r - 2) + 3 := by omega
      unfold quadraticHalfTerm g
      rw [hweight]
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show (r : ℝ) + 1 = ((r - 2 : ℕ) : ℝ) + 3 by
        exact_mod_cast hshift]
    · exact hinj
  rw [heq, quadraticHalfMass]
  exact summable_quadraticHalfTerm.sum_le_tsum (s.image g)
    (fun i hi ↦ by unfold quadraticHalfTerm; positivity)

/-- The exact diagonal weight `(2r-3)` still aggregates on the
`p^{-2}` scale. -/
theorem sum_diagonalWeight_raddone_inv_pow_le {p R : ℕ} (hp : 2 ≤ p) :
    (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) ≤
      quadraticHalfMass / (p : ℝ) ^ 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        (1 / (p : ℝ) ^ 2) *
          ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
      have hpPow : (2 : ℝ) ^ (r - 2) ≤ (p : ℝ) ^ (r - 2) := by
        gcongr
      have hrSplit : r = 2 + (r - 2) := by omega
      have hpowSplit : (p : ℝ) ^ r =
          (p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2) := by
        conv_lhs => rw [hrSplit]
        rw [pow_add]
      rw [hpowSplit]
      have hweight0 : (0 : ℝ) ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
      have hnum0 : 0 ≤ (r : ℝ) + 1 := by positivity
      calc
        ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (p : ℝ) ^ (r - 2))) ≤
            ((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) /
                ((p : ℝ) ^ 2 * (2 : ℝ) ^ (r - 2))) := by
          gcongr
        _ = (1 / (p : ℝ) ^ 2) *
            ((((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
              (1 / (2 : ℝ)) ^ (r - 2)) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ) ^ 2) *
        (∑ r ∈ Finset.Icc 2 R,
          (((2 * r - 3 : ℕ) : ℝ) * ((r : ℝ) + 1)) *
            (1 / (2 : ℝ)) ^ (r - 2)) := by
      rw [Finset.mul_sum]
    _ ≤ (1 / (p : ℝ) ^ 2) * quadraticHalfMass :=
      mul_le_mul_of_nonneg_left (sum_shifted_quadratic_half_le_mass R)
        (by positivity)
    _ = quadraticHalfMass / (p : ℝ) ^ 2 := by ring

/-- The weighted coefficient mass used when restoring one omitted local
prime.  The exponent cutoff is finite and literal. -/
def coefficientTail (p A r : ℕ) (eta L : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 A,
    |coefficient (Real.exp (eta / L)) a| /
      ((p ^ max r a : ℕ) : ℝ)

theorem coefficientTail_nonneg (p A r : ℕ) (eta L : ℝ) :
    0 ≤ coefficientTail p A r eta L := by
  unfold coefficientTail
  positivity

/-- Pointwise coefficient majorant at the common exponent cutoff. -/
theorem abs_coefficient_exp_div_le_at_cutoff
    {B eta L : ℝ} {a A : ℕ}
    (ha : 0 < a) (haA : a ≤ A) (hB : 0 ≤ B)
    (hL : 0 < L) (hBL : B ≤ L) (heta : |eta| ≤ B) :
    |coefficient (Real.exp (eta / L)) a| ≤
      (2 * B / L) * Real.exp (B * (A : ℝ) / L) := by
  have hraw := abs_coefficient_exp_div_le
    (B := B) (η := eta) (L := L) ha hL hBL heta
  have hcoef : 0 ≤ 2 * B / L := by positivity
  have hexp : Real.exp (B * (a : ℝ) / L) ≤
      Real.exp (B * (A : ℝ) / L) := by
    apply Real.exp_le_exp.mpr
    have haAR : (a : ℝ) ≤ (A : ℝ) := by exact_mod_cast haA
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left haAR hB) hL.le
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp hcoef)

/-- Exact scale of the one-prime restoration tail.  Unlike a cardinality
bound, this retains `1/L` uniformly in the exponent cutoff. -/
theorem coefficientTail_le
    {p A r : ℕ} {B eta L : ℝ}
    (hp : 2 ≤ p) (hB : 0 ≤ B) (hL : 0 < L)
    (hBL : B ≤ L) (heta : |eta| ≤ B) :
    coefficientTail p A r eta L ≤
      ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) *
        (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
  classical
  let s := Finset.Icc 1 A
  let K : ℝ := (2 * B / L) * Real.exp (B * (A : ℝ) / L)
  let low := s.filter (fun a ↦ a ≤ r)
  let high := s.filter (fun a ↦ ¬a ≤ r)
  have hpR : (0 : ℝ) < (p : ℝ) := by positivity
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hcoeff : ∀ a ∈ s,
      |coefficient (Real.exp (eta / L)) a| ≤ K := by
    intro a ha
    have ha' := Finset.mem_Icc.mp ha
    simpa only [K] using abs_coefficient_exp_div_le_at_cutoff
      ha'.1 ha'.2 hB hL hBL heta
  have hsplit :
      (∑ a ∈ s,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) =
        (∑ a ∈ low,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) +
        (∑ a ∈ high,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) := by
    dsimp only [low, high]
    exact (Finset.sum_filter_add_sum_filter_not s (fun a ↦ a ≤ r)
      (fun a ↦ |coefficient (Real.exp (eta / L)) a| /
        ((p ^ max r a : ℕ) : ℝ))).symm
  have hlowSubset : low ⊆ Finset.Icc 1 r := by
    intro a ha
    have ha' := Finset.mem_filter.mp ha
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ha'.1).1, ha'.2⟩
  have hlowCard : low.card ≤ r := by
    calc
      low.card ≤ (Finset.Icc 1 r).card := Finset.card_le_card hlowSubset
      _ = r := by simp
  have hlow :
      (∑ a ∈ low,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) ≤
        (r : ℝ) * (K / (p : ℝ) ^ r) := by
    calc
      _ ≤ ∑ a ∈ low, K / (p : ℝ) ^ r := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' := Finset.mem_filter.mp ha
        have har : a ≤ r := ha'.2
        norm_num only [Nat.cast_pow]
        rw [max_eq_left har]
        exact div_le_div_of_nonneg_right (hcoeff a ha'.1) (by positivity)
      _ = (low.card : ℝ) * (K / (p : ℝ) ^ r) := by simp
      _ ≤ (r : ℝ) * (K / (p : ℝ) ^ r) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlowCard)
          (div_nonneg hK (by positivity))
  have hhighSet : high = Finset.Icc (r + 1) A := by
    ext a
    simp only [high, s, Finset.mem_filter, Finset.mem_Icc]
    omega
  have hhigh :
      (∑ a ∈ high,
          |coefficient (Real.exp (eta / L)) a| /
            ((p ^ max r a : ℕ) : ℝ)) ≤
        K * (2 / (p : ℝ) ^ (r + 1)) := by
    rw [hhighSet]
    calc
      _ ≤ ∑ a ∈ Finset.Icc (r + 1) A,
          K * (1 / (p : ℝ) ^ a) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha' := Finset.mem_Icc.mp ha
        have hra : r ≤ a := by omega
        norm_num only [Nat.cast_pow]
        rw [max_eq_right hra]
        calc
          |coefficient (Real.exp (eta / L)) a| / (p : ℝ) ^ a ≤
              K / (p : ℝ) ^ a :=
            div_le_div_of_nonneg_right
              (hcoeff a (by simp only [s, Finset.mem_Icc]; omega))
              (by positivity)
          _ = K * (1 / (p : ℝ) ^ a) := by ring
      _ = K * (∑ a ∈ Finset.Icc (r + 1) A,
          1 / (p : ℝ) ^ a) := by
        rw [Finset.mul_sum]
      _ ≤ K * (2 / (p : ℝ) ^ (r + 1)) := by
        have htail := sum_inv_pow_tail_le (A := A) (r := r) hp
        norm_num only [Nat.cast_pow] at htail
        exact mul_le_mul_of_nonneg_left htail hK
  have htailScale :
      2 / (p : ℝ) ^ (r + 1) ≤ 1 / (p : ℝ) ^ r := by
    rw [pow_succ]
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hpow : (0 : ℝ) < (p : ℝ) ^ r := by positivity
    apply (div_le_iff₀ (mul_pos hpow hpR)).2
    field_simp [hpow.ne', hpR.ne']
    nlinarith
  unfold coefficientTail
  change (∑ a ∈ s,
      |coefficient (Real.exp (eta / L)) a| /
        ((p ^ max r a : ℕ) : ℝ)) ≤ _
  rw [hsplit]
  calc
    _ ≤ (r : ℝ) * (K / (p : ℝ) ^ r) +
        K * (2 / (p : ℝ) ^ (r + 1)) := add_le_add hlow hhigh
    _ ≤ (r : ℝ) * (K / (p : ℝ) ^ r) +
        K * (1 / (p : ℝ) ^ r) := by gcongr
    _ = K * (((r : ℝ) + 1) / (p : ℝ) ^ r) := by ring
    _ = ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) *
        (((r : ℝ) + 1) / (p : ℝ) ^ r) := by rfl

/-- Summing every restored exponent `r ≥ 2` preserves the natural
`p^{-2}` scale, with the coefficient majorant still carrying `1/L`. -/
theorem sum_coefficientTail_le
    {p A R : ℕ} {B eta L : ℝ}
    (hp : 2 ≤ p) (hB : 0 ≤ B) (hL : 0 < L)
    (hBL : B ≤ L) (heta : |eta| ≤ B) :
    (∑ r ∈ Finset.Icc 2 R, coefficientTail p A r eta L) ≤
      8 * ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) /
        (p : ℝ) ^ 2 := by
  let K : ℝ := (2 * B / L) * Real.exp (B * (A : ℝ) / L)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        K * (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
      apply Finset.sum_le_sum
      intro r hr
      simpa only [K] using coefficientTail_le hp hB hL hBL heta
    _ = K * (∑ r ∈ Finset.Icc 2 R,
        ((r : ℝ) + 1) / (p : ℝ) ^ r) := by
      rw [Finset.mul_sum]
    _ ≤ K * (8 / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (sum_raddone_inv_pow_le hp) hK
    _ = 8 * ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) /
        (p : ℝ) ^ 2 := by
      dsimp only [K]
      ring

/-- The same restoration tail with the exact diagonal identity weight
`2r-3`; the absolute constant is fixed before `B`, `W`, and the ODE box. -/
theorem sum_diagonalWeight_coefficientTail_le
    {p A R : ℕ} {B eta L : ℝ}
    (hp : 2 ≤ p) (hB : 0 ≤ B) (hL : 0 < L)
    (hBL : B ≤ L) (heta : |eta| ≤ B) :
    (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) * coefficientTail p A r eta L) ≤
      ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) *
        (quadraticHalfMass / (p : ℝ) ^ 2) := by
  let K : ℝ := (2 * B / L) * Real.exp (B * (A : ℝ) / L)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R,
        K * (((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hw : 0 ≤ ((2 * r - 3 : ℕ) : ℝ) := by positivity
      calc
        ((2 * r - 3 : ℕ) : ℝ) * coefficientTail p A r eta L ≤
            ((2 * r - 3 : ℕ) : ℝ) *
              (K * (((r : ℝ) + 1) / (p : ℝ) ^ r)) :=
          mul_le_mul_of_nonneg_left
            (by simpa only [K] using coefficientTail_le hp hB hL hBL heta)
            hw
        _ = K * (((2 * r - 3 : ℕ) : ℝ) *
            (((r : ℝ) + 1) / (p : ℝ) ^ r)) := by ring
    _ = K * (∑ r ∈ Finset.Icc 2 R,
        ((2 * r - 3 : ℕ) : ℝ) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r)) := by
      rw [Finset.mul_sum]
    _ ≤ K * (quadraticHalfMass / (p : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_diagonalWeight_raddone_inv_pow_le hp) hK
    _ = ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) *
        (quadraticHalfMass / (p : ℝ) ^ 2) := by rfl

/-- The unweighted absolute coefficient mass is bounded without an
infinite expansion.  Combined with the paper's valuation cutoff
`A = O_W(L)`, this is a fixed `B,W` constant and controls literal endpoint
errors in the restored numerator and denominator. -/
theorem sum_abs_coefficient_le
    {A : ℕ} {B eta L : ℝ}
    (hB : 0 ≤ B) (hL : 0 < L) (hBL : B ≤ L)
    (heta : |eta| ≤ B) :
    (∑ a ∈ Finset.Icc 1 A,
        |coefficient (Real.exp (eta / L)) a|) ≤
      (A : ℝ) *
        ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) := by
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 A,
        ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) := by
      apply Finset.sum_le_sum
      intro a ha
      have ha' := Finset.mem_Icc.mp ha
      exact abs_coefficient_exp_div_le_at_cutoff
        ha'.1 ha'.2 hB hL hBL heta
    _ = (A : ℝ) *
        ((2 * B / L) * Real.exp (B * (A : ℝ) / L)) := by simp

end

end Erdos390.Full.LocalFugacityBounds
