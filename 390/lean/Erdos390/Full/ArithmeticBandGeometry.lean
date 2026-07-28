import Erdos390.Full.ArithmeticModel
import Erdos390.Lemma84

/-!
# Exact arithmetic band geometry

This instantiates the finite weighted-band algebra with the paper's actual
prime set, harmonic weights `1/p`, and logarithmic coordinates `t_p`.  In
particular the centering identity is arithmetic, not a continuum identity;
this is the correction required by the audit of Section 8.4.
-/

namespace Erdos390.Full

noncomputable section

open ArithmeticModel

namespace ArithmeticBandGeometry

abbrev BandPrime (n W : ℕ) := {p : ℕ // p ∈ primeBand n W}

/-- A permitted finite partition of the actual prime band. -/
structure Partition (n W : ℕ) (Band : Type*) [Fintype Band] where
  band : BandPrime n W → Band
  fiber_nonempty : ∀ j, ∃ p, band p = j

namespace Partition

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]

instance : Fintype (BandPrime n W) :=
  Fintype.ofFinset (primeBand n W) (fun _ ↦ Iff.rfl)

instance : DecidableEq (BandPrime n W) := inferInstance

def data (P : Partition n W Band) :
    Erdos390.Lemma84.WeightedBandData (BandPrime n W) Band where
  weight := fun p ↦ 1 / (p.1 : ℝ)
  weight_pos := by
    intro p
    exact one_div_pos.mpr (by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos)
  coord := fun p ↦ tPrime n p.1
  band := P.band
  fiber_nonempty := P.fiber_nonempty

abbrev mass (P : Partition n W Band) (j : Band) : ℝ :=
  P.data.mass j

abbrev center (P : Partition n W Band) (j : Band) : ℝ :=
  P.data.center j

abbrev variance (P : Partition n W Band) : ℝ :=
  P.data.cellVariance

abbrev centerEnergy (P : Partition n W Band) : ℝ :=
  P.data.centerEnergy

/-- Exact arithmetic harmonic centering in each band. -/
theorem center_fiber_sum (P : Partition n W Band) (j : Band) :
    ∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * (P.center j - tPrime n p.1) = 0 := by
  exact P.data.center_fiber_sum j

/-- The exact finite arithmetic decomposition highlighted in the audit:
for a gauge vector `q`, no continuum center occurs and every cross term
vanishes band by band. -/
theorem physicalSq_expansion (P : Partition n W Band)
    (q : Band → ℝ) (lambda mu : ℝ) (hq : P.data.inGauge q) :
    P.data.physicalSq (fun j ↦ q j + lambda * P.center j) mu =
      P.data.bandNormSq q +
        (lambda - mu) ^ 2 * P.centerEnergy + mu ^ 2 * P.variance := by
  exact P.data.physicalSq_expansion q lambda mu hq

def minimizingMu (P : Partition n W Band) (lambda : ℝ) : ℝ :=
  lambda * P.centerEnergy / (P.centerEnergy + P.variance)

/-- Exact completion of squares, hence the arithmetic distance is at least
the gauge norm. -/
theorem physicalSq_completion (P : Partition n W Band)
    (q : Band → ℝ) (lambda mu : ℝ) (hq : P.data.inGauge q)
    (hden : P.centerEnergy + P.variance ≠ 0) :
    P.data.physicalSq (fun j ↦ q j + lambda * P.center j) mu =
      P.data.bandNormSq q +
        lambda ^ 2 * (P.centerEnergy * P.variance) /
          (P.centerEnergy + P.variance) +
        (P.centerEnergy + P.variance) *
          (mu - P.minimizingMu lambda) ^ 2 := by
  exact P.data.physical_completion q lambda mu hq hden

theorem physicalSq_minimizer_value (P : Partition n W Band)
    (q : Band → ℝ) (lambda : ℝ) (hq : P.data.inGauge q)
    (hden : P.centerEnergy + P.variance ≠ 0) :
    P.data.physicalSq (fun j ↦ q j + lambda * P.center j)
        (P.minimizingMu lambda) =
      P.data.bandNormSq q +
        lambda ^ 2 * (P.centerEnergy * P.variance) /
          (P.centerEnergy + P.variance) := by
  rw [P.physicalSq_completion q lambda (P.minimizingMu lambda) hq hden]
  simp

/-- The exact arithmetic completion of squares gives a lower bound at every
physical coefficient, not only at the minimizing coefficient.  This is the
finite-`n` quotient gap used for the compensated slow direction; in
particular, it does not compare an arithmetic centre with a continuum
centre. -/
theorem physicalSq_ge_gauge_add_harmonic_gap
    (P : Partition n W Band)
    (q : Band → ℝ) (lambda mu : ℝ) (hq : P.data.inGauge q)
    (hden : 0 < P.centerEnergy + P.variance) :
    P.data.bandNormSq q +
        lambda ^ 2 * (P.centerEnergy * P.variance) /
          (P.centerEnergy + P.variance) ≤
      P.data.physicalSq (fun j ↦ q j + lambda * P.center j) mu := by
  rw [P.physicalSq_completion q lambda mu hq hden.ne']
  exact le_add_of_nonneg_right (mul_nonneg hden.le (sq_nonneg _))

/-- If the within-cell variance is no larger than the centre energy, the
physical quotient distance for the coefficient `q + center` is at least
half of the literal arithmetic variance.  All quantities in the statement
are the finite prime-band quantities. -/
theorem half_variance_le_physicalSq
    (P : Partition n W Band)
    (q : Band → ℝ) (mu : ℝ) (hq : P.data.inGauge q)
    (hcenter : 0 < P.centerEnergy)
    (hvariance : P.variance ≤ P.centerEnergy) :
    P.variance / 2 ≤
      P.data.physicalSq (fun j ↦ q j + P.center j) mu := by
  have hvar : 0 ≤ P.variance :=
    P.data.primeNormSq_nonneg P.data.cellDeviation
  have hden : 0 < P.centerEnergy + P.variance :=
    add_pos_of_pos_of_nonneg hcenter hvar
  have hfrac :
      P.variance / 2 ≤
        P.centerEnergy * P.variance /
          (P.centerEnergy + P.variance) := by
    apply (le_div_iff₀ hden).2
    nlinarith
  have hgap := P.physicalSq_ge_gauge_add_harmonic_gap
    q 1 mu hq hden
  have hband : 0 ≤ P.data.bandNormSq q :=
    P.data.bandNormSq_nonneg q
  norm_num only [one_pow, one_mul] at hgap
  linarith

theorem physicalSq_ge_gauge (P : Partition n W Band)
    (q : Band → ℝ) (lambda mu : ℝ) (hq : P.data.inGauge q) :
    P.data.bandNormSq q ≤
      P.data.physicalSq (fun j ↦ q j + lambda * P.center j) mu := by
  rw [P.physicalSq_expansion q lambda mu hq]
  have hA : 0 ≤ P.centerEnergy := P.data.bandNormSq_nonneg P.data.center
  have hV : 0 ≤ P.variance := P.data.primeNormSq_nonneg P.data.cellDeviation
  have h₁ : 0 ≤ (lambda - mu) ^ 2 * P.centerEnergy :=
    mul_nonneg (sq_nonneg _) hA
  have h₂ : 0 ≤ mu ^ 2 * P.variance := mul_nonneg (sq_nonneg _) hV
  linarith

end Partition

end ArithmeticBandGeometry

end

end Erdos390.Full
