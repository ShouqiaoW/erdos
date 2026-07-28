import Erdos390.Full.ArithmeticBandGeometry
import Erdos390.Full.PrimeBandQuadrature

/-!
# Actual positive-cell prime-band transfer

This file connects the exact arithmetic band geometry to the unconditional
two-endpoint PNT quadrature.  A certificate records that each finite band is
literally a prime interval `(A_j,Y_j]` inside the actual moving prime band.
From that elementary membership statement we derive, rather than assume,

* `H_j = sum_{A_j < p <= Y_j} 1/p`, and
* `H_j * alpha_j = (sum_{A_j < p <= Y_j} log p / p) / log y`.

The final theorems then import the uniform constants and threshold from
`PrimeBandQuadrature`; no Mertens constant or moving-cell asymptotic appears
as a structure field.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PositiveCellTransfer

open ArithmeticModel PrimeSums PrimeBandQuadrature
open ArithmeticBandGeometry

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]

/-- Stability of a quotient under independent numerator and denominator
errors.  This elementary estimate is the deterministic ratio step used when
passing from convergence of `H` and `H alpha` to convergence of `alpha`. -/
lemma abs_div_sub_div_le {a b c d e₁ e₂ : ℝ}
    (hb : 0 < b) (hd : d ≠ 0)
    (hac : |a - c| ≤ e₁) (hbd : |b - d| ≤ e₂) :
    |a / b - c / d| ≤
      e₁ / b + |c| * e₂ / (b * |d|) := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hidentity :
      a / b - c / d = (a - c) / b + c * (d - b) / (b * d) := by
    field_simp [hb0, hd]
    ring
  rw [hidentity]
  calc
    |(a - c) / b + c * (d - b) / (b * d)| ≤
        |(a - c) / b| + |c * (d - b) / (b * d)| :=
      abs_add_le _ _
    _ = |a - c| / b + |c| * |b - d| / (b * |d|) := by
      simp only [abs_div, abs_mul, abs_of_pos hb, abs_sub_comm]
    _ ≤ e₁ / b + |c| * e₂ / (b * |d|) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right hac (le_of_lt hb)
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbd (abs_nonneg c))
          (mul_nonneg (le_of_lt hb) (abs_nonneg d))

/-- Relative form of a one-denominator error estimate. -/
lemma abs_div_sub_one_le {x y e : ℝ} (hy : y ≠ 0)
    (hxy : |x - y| ≤ e) :
    |x / y - 1| ≤ e / |y| := by
  have hidentity : x / y - 1 = (x - y) / y := by
    field_simp [hy]
  rw [hidentity, abs_div]
  exact div_le_div_of_nonneg_right hxy (abs_nonneg y)

/-- The concrete endpoint data certifying that every arithmetic band is one
positive prime interval inside `W < p <= floor(y)`. -/
structure IntervalCertificate (P : Partition n W Band) where
  lower : Band → ℕ
  upper : Band → ℕ
  lower_le_upper : ∀ j, lower j ≤ upper j
  cutoff_le_lower : ∀ j, W ≤ lower j
  upper_le_yNat : ∀ j, upper j ≤ yNat n
  band_eq_iff : ∀ (p : ArithmeticBandGeometry.BandPrime n W) (j : Band),
    P.band p = j ↔ lower j < p.1 ∧ p.1 ≤ upper j

namespace IntervalCertificate

variable {P : Partition n W Band} (E : IntervalCertificate P)

/-- Natural primes in the certified interval. -/
def cellPrimes (j : Band) : Finset ℕ :=
  primesUpTo (E.upper j) \ primesUpTo (E.lower j)

/-- Continuum harmonic mass of the certified endpoint interval. -/
def continuumMass (j : Band) : ℝ :=
  Real.log (Real.log (E.upper j : ℝ)) -
    Real.log (Real.log (E.lower j : ℝ))

/-- Continuum first logarithmic moment on the arithmetic scale `log y`. -/
def continuumMoment (j : Band) : ℝ :=
  (Real.log (E.upper j : ℝ) -
    Real.log (E.lower j : ℝ)) / Real.log (y n)

/-- Continuum cell center, defined as first moment divided by mass. -/
def continuumCenter (j : Band) : ℝ :=
  E.continuumMoment j / E.continuumMass j

omit [DecidableEq Band] in
lemma mem_cellPrimes_iff {j : Band} {p : ℕ} :
    p ∈ E.cellPrimes j ↔
      p.Prime ∧ E.lower j < p ∧ p ≤ E.upper j := by
  rw [cellPrimes, Finset.mem_sdiff]
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_hzero, hpUpper⟩, hpPrime⟩, hpLower⟩
    refine ⟨hpPrime, ?_, hpUpper⟩
    by_contra hnot
    apply hpLower
    exact ⟨⟨Nat.zero_le p, Nat.le_of_not_gt hnot⟩, hpPrime⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    refine ⟨⟨⟨Nat.zero_le p, hpUpper⟩, hpPrime⟩, ?_⟩
    rintro ⟨⟨_hzero, hpLower'⟩, _hpPrime⟩
    exact (Nat.not_lt_of_ge hpLower') hpLower

private lemma primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y := by
  intro p hp
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
  exact ⟨⟨hp.1.1, hp.1.2.trans hAY⟩, hp.2⟩

omit [DecidableEq Band] in
lemma cellReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, 1 / (p : ℝ)) =
      fullReciprocalSum (E.upper j) - fullReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub (f := fun p : ℕ => 1 / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      1 / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j), 1 / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j), 1 / (p : ℝ)
  exact eq_sub_of_add_eq hsum

omit [DecidableEq Band] in
lemma cellLogReciprocalSum_eq_sub (j : Band) :
    (∑ p ∈ E.cellPrimes j, Real.log (p : ℝ) / (p : ℝ)) =
      fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j) := by
  have hsub := primesUpTo_mono (E.lower_le_upper j)
  have hsum := Finset.sum_sdiff hsub
    (f := fun p : ℕ => Real.log (p : ℝ) / (p : ℝ))
  change (∑ p ∈ primesUpTo (E.upper j) \ primesUpTo (E.lower j),
      Real.log (p : ℝ) / (p : ℝ)) =
    (∑ p ∈ primesUpTo (E.upper j),
      Real.log (p : ℝ) / (p : ℝ)) -
      ∑ p ∈ primesUpTo (E.lower j),
        Real.log (p : ℝ) / (p : ℝ)
  exact eq_sub_of_add_eq hsum

lemma fiber_reciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, 1 / (q : ℝ) := by
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : ArithmeticBandGeometry.BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl

lemma fiber_logReciprocalSum_eq_cell (j : Band) :
    (∑ p ∈ P.data.fiber j,
      Real.log (p.1 : ℝ) / (p.1 : ℝ)) =
      ∑ q ∈ E.cellPrimes j, Real.log (q : ℝ) / (q : ℝ) := by
  apply Finset.sum_bij (fun p _hp => p.1)
  · intro p hp
    have hpBand : P.band p = j := by
      simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
    exact E.mem_cellPrimes_iff.mpr
      ⟨prime_of_mem_primeBand p.2, (E.band_eq_iff p j).mp hpBand⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    exact Subtype.ext heq
  · intro q hq
    have hqData := E.mem_cellPrimes_iff.mp hq
    have hqBand : q ∈ primeBand n W := by
      exact mem_primeBand.mpr
        ⟨hqData.1,
          (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : ArithmeticBandGeometry.BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl

/-- Exact arithmetic identification of the harmonic cell mass. -/
theorem mass_eq_fullReciprocalSum_sub (j : Band) :
    P.mass j = fullReciprocalSum (E.upper j) -
      fullReciprocalSum (E.lower j) := by
  change (∑ p ∈ P.data.fiber j, 1 / (p.1 : ℝ)) = _
  rw [E.fiber_reciprocalSum_eq_cell, E.cellReciprocalSum_eq_sub]

private lemma mass_mul_center_eq_weightedCoordSum (j : Band) :
    P.mass j * P.center j =
      ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1 := by
  change P.data.mass j *
      ((∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j) = _
  field_simp [ne_of_gt (P.data.mass_pos j)]

/-- Exact arithmetic identification of the centered first cell moment. -/
theorem mass_mul_center_eq_fullLogReciprocalSum_sub (j : Band) :
    P.mass j * P.center j =
      (fullLogReciprocalSum (E.upper j) -
        fullLogReciprocalSum (E.lower j)) / Real.log (y n) := by
  rw [mass_mul_center_eq_weightedCoordSum (P := P)]
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) *
        (Real.log (p.1 : ℝ) / Real.log (y n))) = _
  calc
    (∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) *
          (Real.log (p.1 : ℝ) / Real.log (y n))) =
        (∑ p ∈ P.data.fiber j,
          Real.log (p.1 : ℝ) / (p.1 : ℝ)) /
            Real.log (y n) := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro p hp
              ring
    _ = (∑ q ∈ E.cellPrimes j,
          Real.log (q : ℝ) / (q : ℝ)) /
            Real.log (y n) := by rw [E.fiber_logReciprocalSum_eq_cell]
    _ = _ := by rw [E.cellLogReciprocalSum_eq_sub]

/-- The exact deterministic ratio transfer.  Once the arithmetic mass and
first moment have been compared with their continuum counterparts, this
proves the corresponding center estimate without identifying arithmetic and
continuum centers. -/
theorem center_error_le_of_mass_moment_errors (j : Band)
    {eMass eMoment : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hMoment :
      |P.mass j * P.center j - E.continuumMoment j| ≤ eMoment)
    (hContinuumMass : E.continuumMass j ≠ 0) :
    |P.center j - E.continuumCenter j| ≤
      eMoment / P.mass j +
        |E.continuumMoment j| * eMass /
          (P.mass j * |E.continuumMass j|) := by
  have hmass : 0 < P.mass j := P.data.mass_pos j
  have hcenter :
      P.center j = (P.mass j * P.center j) / P.mass j := by
    rw [mul_div_cancel_left₀]
    exact ne_of_gt hmass
  rw [hcenter, continuumCenter]
  exact abs_div_sub_div_le hmass hContinuumMass hMoment hMass

/-- Relative mass convergence obtained from the same absolute endpoint
estimate.  This is the form used for the moving low cell, where the
continuum mass itself grows. -/
theorem mass_ratio_error_le (j : Band) {eMass : ℝ}
    (hMass : |P.mass j - E.continuumMass j| ≤ eMass)
    (hContinuumMass : E.continuumMass j ≠ 0) :
    |P.mass j / E.continuumMass j - 1| ≤
      eMass / |E.continuumMass j| := by
  exact abs_div_sub_one_le hContinuumMass hMass

/-- Uniform unconditional quadrature for every certified positive-cell mass.
The constants are selected before the moving endpoints. -/
theorem exists_mass_quadrature_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ j : Band,
      X₀ ≤ E.lower j →
      |P.mass j -
        (Real.log (Real.log (E.upper j : ℝ)) -
          Real.log (Real.log (E.lower j : ℝ)))| ≤
        5 * C / Real.log (E.lower j : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀, hbound⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  refine ⟨C, hC, X₀, fun j hj => ?_⟩
  rw [E.mass_eq_fullReciprocalSum_sub]
  exact hbound (E.lower j) (E.upper j) hj (E.lower_le_upper j)

/-- Uniform unconditional quadrature for `H_j alpha_j`.  The displayed
error is the first-logarithmic-moment PNT error divided by the exact
arithmetic scale `log y`. -/
theorem exists_mass_mul_center_quadrature_bound (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ j : Band,
      X₀ ≤ E.lower j →
      |P.mass j * P.center j -
        (Real.log (E.upper j : ℝ) -
          Real.log (E.lower j : ℝ)) / Real.log (y n)| ≤
        (C * (2 + (Real.log (E.upper j : ℝ) -
          Real.log (E.lower j : ℝ))) /
            Real.log (E.lower j : ℝ) ^ 3) /
          |Real.log (y n)| := by
  obtain ⟨C, hC, X₀, hbound⟩ :=
    exists_fullLogReciprocalSum_interval_error_bound
  refine ⟨C, hC, X₀, fun j hj => ?_⟩
  have hlogy : 0 < Real.log (y n) := by
    rw [Erdos390.Full.Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast hn))
  rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
  rw [← sub_div]
  rw [abs_div]
  exact div_le_div_of_nonneg_right
    (hbound (E.lower j) (E.upper j) hj (E.lower_le_upper j))
    (abs_nonneg (Real.log (y n)))

end IntervalCertificate

end Erdos390.Full.PositiveCellTransfer
