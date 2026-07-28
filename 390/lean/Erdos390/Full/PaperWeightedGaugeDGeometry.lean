import Erdos390.Full.PaperWeightedInverseExport

/-!
# Finite `D`-pairing geometry in the paper's sharp gauge

These are the exact finite weighted inequalities used when covariance
Cauchy--Schwarz is combined with the sharp-gauge inverse.  No continuum
centre or limiting weight is introduced.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band] [Nonempty Band]

/-- The arithmetic diagonal pairing on the raw gauge. -/
def rawDPairing (H alpha : Band → ℝ)
    (q r : RawGaugeSpace H alpha) : ℝ :=
  ∑ j, H j * q.1 j * r.1 j

/-- Smallest literal sharp diagonal weight of the finite arithmetic band
family. -/
def rawDLowerWeight (H alpha : Band → ℝ) : ℝ :=
  let s : Finset ℝ := Finset.univ.image (fun j ↦ H j * alpha j ^ 2)
  s.min' (by
    classical
    exact Finset.univ_nonempty.image _)

theorem rawDLowerWeight_le (H alpha : Band → ℝ) (j : Band) :
    rawDLowerWeight H alpha ≤ H j * alpha j ^ 2 := by
  classical
  unfold rawDLowerWeight
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- Positivity of the literal finite minimum. -/
theorem rawDLowerWeight_pos
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0) :
    0 < rawDLowerWeight H alpha := by
  classical
  let s : Finset ℝ := Finset.univ.image (fun j ↦ H j * alpha j ^ 2)
  have hs : s.Nonempty := Finset.univ_nonempty.image _
  have hmem := Finset.min'_mem s hs
  obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hmem
  have hAlphaSq : 0 < alpha j ^ 2 := sq_pos_of_ne_zero (hAlpha j)
  unfold rawDLowerWeight
  change 0 < s.min' hs
  rw [← hEq]
  exact mul_pos (hH j) hAlphaSq

/-- The `D` quadratic form controls the paper's sharp supremum norm by the
smallest literal sharp diagonal weight. -/
theorem rawDLowerWeight_mul_paperSharpNorm_sq_le
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q : RawGaugeSpace H alpha) :
    rawDLowerWeight H alpha *
        paperSharpNorm H alpha hAlpha q ^ 2 ≤
      rawDPairing H alpha q q := by
  classical
  let f : Band → ℝ := fun j ↦ q.1 j / alpha j
  obtain ⟨j, hj, hsup⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty
      (fun k : Band ↦ ‖f k‖₊)
  have hnorm : paperSharpNorm H alpha hAlpha q = |f j| := by
    rw [paperSharpNorm_eq_piNorm]
    change ‖f‖ = |f j|
    rw [Pi.norm_def, ← Finset.sup'_eq_sup Finset.univ_nonempty, hsup]
    simp only [coe_nnnorm, Real.norm_eq_abs]
  have hmin0 : 0 ≤ rawDLowerWeight H alpha :=
    (rawDLowerWeight_pos H alpha hH hAlpha).le
  have hterm :
      rawDLowerWeight H alpha * |f j| ^ 2 ≤ H j * q.1 j ^ 2 := by
    calc
      rawDLowerWeight H alpha * |f j| ^ 2 ≤
          (H j * alpha j ^ 2) * |f j| ^ 2 :=
        mul_le_mul_of_nonneg_right (rawDLowerWeight_le H alpha j)
          (sq_nonneg _)
      _ = H j * q.1 j ^ 2 := by
        dsimp only [f]
        rw [sq_abs]
        field_simp [hAlpha j]
  rw [hnorm]
  exact hterm.trans (by
    unfold rawDPairing
    simpa only [pow_two, mul_assoc] using
      (Finset.single_le_sum
        (fun k hk ↦ mul_nonneg (hH k).le (sq_nonneg (q.1 k)))
        (Finset.mem_univ j)))

/-- Absolute `D` pairing is bounded by the total sharp weight times the two
paper-sharp norms. -/
theorem abs_rawDPairing_le_sharpWeightTotal_mul
    (H alpha : Band → ℝ) (hH : ∀ j, 0 < H j)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (q r : RawGaugeSpace H alpha) :
    |rawDPairing H alpha q r| ≤
      sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
        paperSharpNorm H alpha hAlpha r := by
  have hq (j : Band) :
      |q.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha q := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ q.1 k / alpha k)).mp le_rfl j)
  have hr (j : Band) :
      |r.1 j / alpha j| ≤ paperSharpNorm H alpha hAlpha r := by
    rw [paperSharpNorm_eq_piNorm]
    simpa only [Real.norm_eq_abs] using
      ((pi_norm_le_iff_of_nonempty
        (fun k ↦ r.1 k / alpha k)).mp le_rfl j)
  have hq0 : 0 ≤ paperSharpNorm H alpha hAlpha q := norm_nonneg _
  have hr0 : 0 ≤ paperSharpNorm H alpha hAlpha r := norm_nonneg _
  calc
    |rawDPairing H alpha q r| ≤
        ∑ j, |H j * q.1 j * r.1 j| := by
      unfold rawDPairing
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (H j * alpha j ^ 2) *
          paperSharpNorm H alpha hAlpha q *
            paperSharpNorm H alpha hAlpha r := by
      apply Finset.sum_le_sum
      intro j hj
      have hweight : 0 ≤ H j * alpha j ^ 2 :=
        mul_nonneg (hH j).le (sq_nonneg _)
      have hratio :
          |q.1 j / alpha j| * |r.1 j / alpha j| ≤
            paperSharpNorm H alpha hAlpha q *
              paperSharpNorm H alpha hAlpha r :=
        mul_le_mul (hq j) (hr j) (abs_nonneg _) hq0
      calc
        |H j * q.1 j * r.1 j| =
            (H j * alpha j ^ 2) *
              (|q.1 j / alpha j| * |r.1 j / alpha j|) := by
          rw [abs_mul, abs_mul, abs_of_pos (hH j), abs_div, abs_div,
            ← sq_abs]
          field_simp [abs_ne_zero.mpr (hAlpha j)]
        _ ≤ (H j * alpha j ^ 2) *
              (paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r) :=
          mul_le_mul_of_nonneg_left hratio hweight
        _ = (H j * alpha j ^ 2) *
              paperSharpNorm H alpha hAlpha q *
                paperSharpNorm H alpha hAlpha r := by ring
    _ = sharpWeightTotal H alpha * paperSharpNorm H alpha hAlpha q *
          paperSharpNorm H alpha hAlpha r := by
      unfold sharpWeightTotal sharpWeight
      rw [← Finset.sum_mul, ← Finset.sum_mul]

end Erdos390.Full.PaperWeightedInverseExport
