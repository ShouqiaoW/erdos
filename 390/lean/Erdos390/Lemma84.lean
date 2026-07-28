import Mathlib

/-!
# The finite-dimensional core of Lemma 8.4

This file formalizes only the algebraic part of the moving-low-cell
arithmetic quotient argument.  The Poisson--Dickman gap, prime
quadrature, and marked covariance estimates occur below as fields of an
explicit input structure.  Thus this file contains no postulate claiming
those analytic results.
-/

namespace Erdos390.Lemma84

open scoped BigOperators

noncomputable section

section WeightedBands

variable {Prime Band : Type*}
variable [Fintype Prime] [Fintype Band]
variable [DecidableEq Prime] [DecidableEq Band]

/-- Finite prime weights, their logarithmic coordinates, and a partition
into bands. -/
structure WeightedBandData (Prime Band : Type*) [Fintype Prime]
    [Fintype Band] [DecidableEq Prime] [DecidableEq Band] where
  weight : Prime → ℝ
  weight_pos : ∀ p, 0 < weight p
  coord : Prime → ℝ
  band : Prime → Band
  fiber_nonempty : ∀ j, ∃ p, band p = j

namespace WeightedBandData

variable (d : WeightedBandData Prime Band)

def fiber (j : Band) : Finset Prime :=
  Finset.univ.filter fun p => d.band p = j

def mass (j : Band) : ℝ :=
  ∑ p ∈ d.fiber j, d.weight p

def center (j : Band) : ℝ :=
  (∑ p ∈ d.fiber j, d.weight p * d.coord p) / d.mass j

def bandInner (x y : Band → ℝ) : ℝ :=
  ∑ j, d.mass j * x j * y j

def bandNormSq (x : Band → ℝ) : ℝ :=
  d.bandInner x x

def inGauge (q : Band → ℝ) : Prop :=
  d.bandInner d.center q = 0

def lift (b : Band → ℝ) (p : Prime) : ℝ :=
  b (d.band p)

def primeInner (x y : Prime → ℝ) : ℝ :=
  ∑ p, d.weight p * x p * y p

def primeNormSq (x : Prime → ℝ) : ℝ :=
  d.primeInner x x

def cellDeviation (p : Prime) : ℝ :=
  d.center (d.band p) - d.coord p

def cellVariance : ℝ :=
  d.primeNormSq d.cellDeviation

def centerEnergy : ℝ :=
  d.bandNormSq d.center

def gaugeCoefficient (b : Band → ℝ) : ℝ :=
  d.bandInner d.center b / d.centerEnergy

def gaugePart (b : Band → ℝ) (j : Band) : ℝ :=
  b j - d.gaugeCoefficient b * d.center j

def coordEnergy : ℝ :=
  d.primeNormSq d.coord

def residual (b : Band → ℝ) (mu : ℝ) (p : Prime) : ℝ :=
  d.lift b p - mu * d.coord p

def physicalSq (b : Band → ℝ) (mu : ℝ) : ℝ :=
  d.primeNormSq (d.residual b mu)

def physicalMinimizer (b : Band → ℝ) : ℝ :=
  d.primeInner d.coord (d.lift b) / d.coordEnergy

def primeQuadratic (E : Prime → Prime → ℝ) (c : Prime → ℝ) : ℝ :=
  ∑ p, ∑ r, E p r * c p * c r

theorem primeInner_add_left (x y z : Prime → ℝ) :
    d.primeInner (fun p => x p + y p) z =
      d.primeInner x z + d.primeInner y z := by
  unfold primeInner
  calc
    (∑ p, d.weight p * (x p + y p) * z p) =
        ∑ p, (d.weight p * x p * z p + d.weight p * y p * z p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := Finset.sum_add_distrib

theorem primeInner_add_right (x y z : Prime → ℝ) :
    d.primeInner x (fun p => y p + z p) =
      d.primeInner x y + d.primeInner x z := by
  unfold primeInner
  calc
    (∑ p, d.weight p * x p * (y p + z p)) =
        ∑ p, (d.weight p * x p * y p + d.weight p * x p * z p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := Finset.sum_add_distrib

theorem primeInner_smul_left (a : ℝ) (x y : Prime → ℝ) :
    d.primeInner (fun p => a * x p) y = a * d.primeInner x y := by
  unfold primeInner
  calc
    (∑ p, d.weight p * (a * x p) * y p) =
        ∑ p, a * (d.weight p * x p * y p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm

theorem primeInner_smul_right (a : ℝ) (x y : Prime → ℝ) :
    d.primeInner x (fun p => a * y p) = a * d.primeInner x y := by
  unfold primeInner
  calc
    (∑ p, d.weight p * x p * (a * y p)) =
        ∑ p, a * (d.weight p * x p * y p) := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm

theorem primeInner_comm (x y : Prime → ℝ) :
    d.primeInner x y = d.primeInner y x := by
  apply Finset.sum_congr rfl
  intro p hp
  ring

theorem primeNormSq_add (x y : Prime → ℝ) :
    d.primeNormSq (fun p => x p + y p) =
      d.primeNormSq x + d.primeNormSq y + 2 * d.primeInner x y := by
  unfold primeNormSq
  rw [d.primeInner_add_left, d.primeInner_add_right,
    d.primeInner_add_right, d.primeInner_comm y x]
  ring

theorem primeNormSq_smul (a : ℝ) (x : Prime → ℝ) :
    d.primeNormSq (fun p => a * x p) = a ^ 2 * d.primeNormSq x := by
  unfold primeNormSq
  rw [d.primeInner_smul_left, d.primeInner_smul_right]
  ring

theorem primeNormSq_nonneg (x : Prime → ℝ) : 0 ≤ d.primeNormSq x := by
  unfold primeNormSq primeInner
  apply Finset.sum_nonneg
  intro p hp
  have hw : 0 ≤ d.weight p := le_of_lt (d.weight_pos p)
  nlinarith [sq_nonneg (x p)]

theorem bandNormSq_nonneg (x : Band → ℝ) : 0 ≤ d.bandNormSq x := by
  unfold bandNormSq bandInner
  apply Finset.sum_nonneg
  intro j hj
  have hH : 0 ≤ d.mass j := by
    unfold mass
    apply Finset.sum_nonneg
    intro p hp
    exact le_of_lt (d.weight_pos p)
  nlinarith [sq_nonneg (x j)]

/-- A symmetric normalized prime-row bound controls the whole quadratic
error.  With `weight p = 1 / p`, its hypothesis is exactly
`sup_p p * sum_r |E p r| ≤ ε`. -/
theorem symmetric_prime_row_quadratic_error
    (E : Prime → Prime → ℝ) (c : Prime → ℝ) (eps : ℝ)
    (hsymm : ∀ p r, E p r = E r p)
    (hrow : ∀ p, (∑ r, |E p r|) ≤ eps * d.weight p) :
    |primeQuadratic E c| ≤ eps * d.primeNormSq c := by
  let Sabs : ℝ := ∑ p, ∑ r, |E p r * c p * c r|
  let Srow : ℝ := ∑ p, c p ^ 2 * (∑ r, |E p r|)
  have htriangle : |primeQuadratic E c| ≤ Sabs := by
    unfold primeQuadratic Sabs
    calc
      |∑ p, ∑ r, E p r * c p * c r| ≤
          ∑ p, |∑ r, E p r * c p * c r| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p, ∑ r, |E p r * c p * c r| := by
        apply Finset.sum_le_sum
        intro p hp
        exact Finset.abs_sum_le_sum_abs _ _
  have hpair (p r : Prime) :
      2 * |E p r * c p * c r| ≤
        |E p r| * (c p ^ 2 + c r ^ 2) := by
    have hab : 2 * |c p| * |c r| ≤ |c p| ^ 2 + |c r| ^ 2 := by
      nlinarith [sq_nonneg (|c p| - |c r|)]
    calc
      2 * |E p r * c p * c r| =
          |E p r| * (2 * |c p| * |c r|) := by
            simp only [abs_mul]
            ring
      _ ≤ |E p r| * (|c p| ^ 2 + |c r| ^ 2) :=
        mul_le_mul_of_nonneg_left hab (abs_nonneg _)
      _ = |E p r| * (c p ^ 2 + c r ^ 2) := by
        rw [sq_abs, sq_abs]
  have hpairSum :
      2 * Sabs ≤ ∑ p, ∑ r, |E p r| * (c p ^ 2 + c r ^ 2) := by
    unfold Sabs
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    exact hpair p r
  have hsymSum :
      (∑ p, ∑ r, |E p r| * (c p ^ 2 + c r ^ 2)) = 2 * Srow := by
    have hfirst :
        (∑ p, ∑ r, |E p r| * c p ^ 2) = Srow := by
      unfold Srow
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have hsecond :
        (∑ p, ∑ r, |E p r| * c r ^ 2) = Srow := by
      rw [Finset.sum_comm]
      unfold Srow
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      rw [hsymm r p]
      ring
    calc
      (∑ p, ∑ r, |E p r| * (c p ^ 2 + c r ^ 2)) =
          (∑ p, ∑ r, |E p r| * c p ^ 2) +
            (∑ p, ∑ r, |E p r| * c r ^ 2) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
      _ = 2 * Srow := by rw [hfirst, hsecond]; ring
  have hrowSum : Srow ≤ eps * d.primeNormSq c := by
    unfold Srow primeNormSq primeInner
    calc
      (∑ p, c p ^ 2 * ∑ r, |E p r|) ≤
          ∑ p, c p ^ 2 * (eps * d.weight p) := by
            apply Finset.sum_le_sum
            intro p hp
            exact mul_le_mul_of_nonneg_left (hrow p) (sq_nonneg _)
      _ = eps * ∑ p, d.weight p * c p * c p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  rw [hsymSum] at hpairSum
  nlinarith

theorem mem_fiber_iff {p : Prime} {j : Band} :
    p ∈ d.fiber j ↔ d.band p = j := by
  simp [fiber]

theorem mass_pos (j : Band) : 0 < d.mass j := by
  apply Finset.sum_pos
  · intro p hp
    exact d.weight_pos p
  · obtain ⟨p, hp⟩ := d.fiber_nonempty j
    exact ⟨p, by simp [fiber, hp]⟩

theorem mass_ne_zero (j : Band) : d.mass j ≠ 0 :=
  ne_of_gt (d.mass_pos j)

/-- The definition of the arithmetic band center gives exact weighted
centering on each fiber. -/
theorem center_fiber_sum (j : Band) :
    ∑ p ∈ d.fiber j, d.weight p * (d.center j - d.coord p) = 0 := by
  let H : ℝ := d.mass j
  let N : ℝ := ∑ p ∈ d.fiber j, d.weight p * d.coord p
  have hH : H ≠ 0 := by
    exact d.mass_ne_zero j
  change ∑ p ∈ d.fiber j, d.weight p * (N / H - d.coord p) = 0
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hleft :
      (∑ p ∈ d.fiber j, d.weight p * (N / H)) = H * (N / H) := by
    rw [← Finset.sum_mul]
    rfl
  rw [hleft]
  change H * (N / H) - N = 0
  field_simp
  ring

/-- Cellwise centering annihilates every coefficient which is constant
on each band. -/
theorem centered_against_lift (r : Band → ℝ) :
    d.primeInner (d.lift r) d.cellDeviation = 0 := by
  unfold primeInner
  rw [← Finset.sum_fiberwise Finset.univ d.band
    (fun p => d.weight p * d.lift r p * d.cellDeviation p)]
  apply Finset.sum_eq_zero
  intro j hj
  calc
    (∑ p ∈ Finset.univ with d.band p = j,
        d.weight p * d.lift r p * d.cellDeviation p) =
        r j * (∑ p ∈ d.fiber j,
          d.weight p * (d.center j - d.coord p)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr
          · rfl
          · intro p hp
            have hpj : d.band p = j := (Finset.mem_filter.mp hp).2
            simp only [lift, cellDeviation, hpj]
            ring
    _ = 0 := by rw [d.center_fiber_sum j, mul_zero]

theorem primeInner_lifts (x y : Band → ℝ) :
    d.primeInner (d.lift x) (d.lift y) = d.bandInner x y := by
  unfold primeInner bandInner
  rw [← Finset.sum_fiberwise Finset.univ d.band
    (fun p => d.weight p * d.lift x p * d.lift y p)]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    (∑ p ∈ Finset.univ with d.band p = j,
        d.weight p * d.lift x p * d.lift y p) =
        ∑ p ∈ d.fiber j, d.weight p * x j * y j := by
          apply Finset.sum_congr
          · rfl
          · intro p hp
            have hpj : d.band p = j := (Finset.mem_filter.mp hp).2
            simp only [lift, hpj]
    _ = (∑ p ∈ d.fiber j, d.weight p) * x j * y j := by
          rw [Finset.sum_mul]
          rw [Finset.sum_mul]
    _ = d.mass j * x j * y j := rfl

theorem bandInner_comm (x y : Band → ℝ) :
    d.bandInner x y = d.bandInner y x := by
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bandInner_add_right (x y z : Band → ℝ) :
    d.bandInner x (fun j => y j + z j) =
      d.bandInner x y + d.bandInner x z := by
  unfold bandInner
  calc
    (∑ j, d.mass j * x j * (y j + z j)) =
        ∑ j, (d.mass j * x j * y j + d.mass j * x j * z j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := Finset.sum_add_distrib

theorem bandInner_smul_right (a : ℝ) (x y : Band → ℝ) :
    d.bandInner x (fun j => a * y j) = a * d.bandInner x y := by
  unfold bandInner
  calc
    (∑ j, d.mass j * x j * (a * y j)) =
        ∑ j, a * (d.mass j * x j * y j) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
    _ = _ := (Finset.mul_sum Finset.univ _ a).symm

theorem bandNormSq_add (x y : Band → ℝ) :
    d.bandNormSq (fun j => x j + y j) =
      d.bandNormSq x + d.bandNormSq y + 2 * d.bandInner x y := by
  unfold bandNormSq
  rw [d.bandInner_add_right]
  have haddLeft :
      d.bandInner (fun j => x j + y j) x =
        d.bandInner x x + d.bandInner y x := by
    rw [d.bandInner_comm, d.bandInner_add_right]
    rw [d.bandInner_comm x x, d.bandInner_comm x y]
  have haddRight :
      d.bandInner (fun j => x j + y j) y =
        d.bandInner x y + d.bandInner y y := by
    rw [d.bandInner_comm, d.bandInner_add_right]
    rw [d.bandInner_comm y x, d.bandInner_comm y y]
  rw [haddLeft, haddRight, d.bandInner_comm y x]
  ring

theorem bandNormSq_smul (a : ℝ) (x : Band → ℝ) :
    d.bandNormSq (fun j => a * x j) = a ^ 2 * d.bandNormSq x := by
  unfold bandNormSq
  rw [d.bandInner_smul_right]
  rw [d.bandInner_comm, d.bandInner_smul_right]
  rw [d.bandInner_comm]
  ring

theorem coord_decomposition (p : Prime) :
    d.coord p = d.lift d.center p - d.cellDeviation p := by
  simp [lift, cellDeviation]

theorem coordEnergy_eq :
    d.coordEnergy = d.centerEnergy + d.cellVariance := by
  let a : Prime → ℝ := d.lift d.center
  let g : Prime → ℝ := d.cellDeviation
  have hcoord : d.coord = fun p => a p + (-1 : ℝ) * g p := by
    funext p
    rw [d.coord_decomposition p]
    change a p - g p = a p + (-1 : ℝ) * g p
    ring
  have hag : d.primeInner a g = 0 := by
    simpa [a, g] using d.centered_against_lift d.center
  have haa : d.primeNormSq a = d.centerEnergy := by
    simpa [a, primeNormSq, centerEnergy, bandNormSq] using
      d.primeInner_lifts d.center d.center
  calc
    d.coordEnergy = d.primeNormSq (fun p => a p + (-1 : ℝ) * g p) := by
      rw [show d.coordEnergy = d.primeNormSq d.coord by rfl, hcoord]
    _ = d.primeNormSq a + d.primeNormSq (fun p => (-1 : ℝ) * g p) +
          2 * d.primeInner a (fun p => (-1 : ℝ) * g p) :=
      d.primeNormSq_add a (fun p => (-1 : ℝ) * g p)
    _ = d.centerEnergy + d.cellVariance := by
      rw [d.primeNormSq_smul, d.primeInner_smul_right, haa, hag]
      simp [g, cellVariance]

theorem physicalSq_expansion (q : Band → ℝ) (lambda mu : ℝ)
    (hq : d.inGauge q) :
    d.physicalSq (fun j => q j + lambda * d.center j) mu =
      d.bandNormSq q + (lambda - mu) ^ 2 * d.centerEnergy +
        mu ^ 2 * d.cellVariance := by
  let x : Prime → ℝ := d.lift q
  let a : Prime → ℝ := d.lift d.center
  let g : Prime → ℝ := d.cellDeviation
  let y : Prime → ℝ := fun p => (lambda - mu) * a p
  let z : Prime → ℝ := fun p => mu * g p
  have hres :
      d.residual (fun j => q j + lambda * d.center j) mu =
        fun p => (x p + y p) + z p := by
    funext p
    unfold residual lift
    rw [show d.coord p = a p - g p by
      simpa [a, g] using d.coord_decomposition p]
    simp only [x, a, y, z, g, lift]
    ring
  have hxx : d.primeNormSq x = d.bandNormSq q := by
    simpa [x, primeNormSq, bandNormSq] using d.primeInner_lifts q q
  have haa : d.primeNormSq a = d.centerEnergy := by
    simpa [a, primeNormSq, centerEnergy, bandNormSq] using
      d.primeInner_lifts d.center d.center
  have hgg : d.primeNormSq g = d.cellVariance := rfl
  have hxa : d.primeInner x a = 0 := by
    calc
      d.primeInner x a = d.bandInner q d.center := by
        simpa [x, a] using d.primeInner_lifts q d.center
      _ = d.bandInner d.center q := d.bandInner_comm q d.center
      _ = 0 := hq
  have hxg : d.primeInner x g = 0 := by
    simpa [x, g] using d.centered_against_lift q
  have hag : d.primeInner a g = 0 := by
    simpa [a, g] using d.centered_against_lift d.center
  unfold physicalSq
  rw [hres, d.primeNormSq_add, d.primeNormSq_add,
    d.primeInner_add_left]
  dsimp only [y, z]
  rw [d.primeNormSq_smul, d.primeNormSq_smul,
    d.primeInner_smul_right, d.primeInner_smul_right,
    d.primeInner_smul_left, d.primeInner_smul_right,
    hxx, haa, hgg, hxa, hxg, hag]
  ring

theorem physicalMinimizer_normal (b : Band → ℝ)
    (hcoord : d.coordEnergy ≠ 0) :
    d.primeInner d.coord (d.residual b (d.physicalMinimizer b)) = 0 := by
  have hres : d.residual b (d.physicalMinimizer b) =
      fun p => d.lift b p +
        (-d.physicalMinimizer b) * d.coord p := by
    funext p
    simp only [residual]
    ring
  rw [hres, d.primeInner_add_right, d.primeInner_smul_right]
  have hE : d.primeInner d.coord d.coord ≠ 0 := by
    simpa [coordEnergy, primeNormSq] using hcoord
  unfold physicalMinimizer coordEnergy primeNormSq
  field_simp [hE]
  ring

theorem physical_completion (q : Band → ℝ) (lambda mu : ℝ)
    (hq : d.inGauge q) (hden : d.centerEnergy + d.cellVariance ≠ 0) :
    d.physicalSq (fun j => q j + lambda * d.center j) mu =
      d.bandNormSq q +
        lambda ^ 2 * (d.centerEnergy * d.cellVariance) /
          (d.centerEnergy + d.cellVariance) +
        (d.centerEnergy + d.cellVariance) *
          (mu - lambda * d.centerEnergy /
            (d.centerEnergy + d.cellVariance)) ^ 2 := by
  rw [d.physicalSq_expansion q lambda mu hq]
  field_simp
  ring

theorem physical_lower_bound (q : Band → ℝ) (lambda : ℝ)
    (hq : d.inGauge q) (hV : 0 ≤ d.cellVariance) :
    d.bandNormSq q ≤
      d.physicalSq (fun j => q j + lambda * d.center j)
        (d.physicalMinimizer (fun j => q j + lambda * d.center j)) := by
  rw [d.physicalSq_expansion q lambda _ hq]
  have hA : 0 ≤ d.centerEnergy := d.bandNormSq_nonneg d.center
  have hfirst :
      0 ≤ (lambda - d.physicalMinimizer
        (fun j => q j + lambda * d.center j)) ^ 2 * d.centerEnergy :=
    mul_nonneg (sq_nonneg _) hA
  have hsecond :
      0 ≤ d.physicalMinimizer
        (fun j => q j + lambda * d.center j) ^ 2 * d.cellVariance :=
    mul_nonneg (sq_nonneg _) hV
  linarith

theorem gaugePart_inGauge (b : Band → ℝ) (hA : d.centerEnergy ≠ 0) :
    d.inGauge (d.gaugePart b) := by
  have hE : d.bandInner d.center d.center ≠ 0 := by
    simpa [centerEnergy, bandNormSq] using hA
  have hfun : d.gaugePart b = fun j =>
      b j + (-d.gaugeCoefficient b) * d.center j := by
    funext j
    simp only [gaugePart]
    ring
  unfold inGauge
  rw [hfun, d.bandInner_add_right, d.bandInner_smul_right]
  unfold gaugeCoefficient centerEnergy bandNormSq
  field_simp [hE]
  ring

theorem gauge_decomposition (b : Band → ℝ) (j : Band) :
    d.gaugePart b j + d.gaugeCoefficient b * d.center j = b j := by
  simp only [gaugePart]
  ring

theorem band_distance_expansion (q : Band → ℝ) (lambda mu : ℝ)
    (hq : d.inGauge q) :
    d.bandNormSq (fun j => q j + (lambda - mu) * d.center j) =
      d.bandNormSq q + (lambda - mu) ^ 2 * d.centerEnergy := by
  rw [d.bandNormSq_add, d.bandNormSq_smul,
    d.bandInner_smul_right]
  have hcross : d.bandInner q d.center = 0 := by
    rw [d.bandInner_comm]
    exact hq
  rw [hcross]
  unfold centerEnergy
  ring

/-- The gauge part is the exact best weighted approximation modulo the
center direction. -/
theorem gaugePart_best_distance (b : Band → ℝ) (mu : ℝ)
    (hA : d.centerEnergy ≠ 0) :
    d.bandNormSq (d.gaugePart b) ≤
      d.bandNormSq (fun j => b j - mu * d.center j) := by
  let q : Band → ℝ := d.gaugePart b
  let lambda : ℝ := d.gaugeCoefficient b
  have hq : d.inGauge q := by
    simpa [q] using d.gaugePart_inGauge b hA
  have hrewrite : (fun j => b j - mu * d.center j) =
      fun j => q j + (lambda - mu) * d.center j := by
    funext j
    have hd := d.gauge_decomposition b j
    dsimp only [q, lambda]
    linarith
  rw [hrewrite, d.band_distance_expansion q lambda mu hq]
  have hcenter : 0 ≤ d.centerEnergy := d.bandNormSq_nonneg d.center
  have hterm : 0 ≤ (lambda - mu) ^ 2 * d.centerEnergy :=
    mul_nonneg (sq_nonneg _) hcenter
  linarith

/-!
## Conditional bridge

The next structure is the exact boundary between the finite argument and
the presently external analytic work.  Its fields are a leading
Poisson--Dickman/quadrature form, an actual marked covariance form, the
nuisance loss, and quantitative comparisons between them.  No field is
the desired quotient conclusion.
-/

structure BridgeInputs where
  leadingForm : (Prime → ℝ) → ℝ
  actualVariance : (Prime → ℝ) → ℝ
  nuisanceLoss : (Prime → ℝ) → ℝ
  schurForm : (Band → ℝ) → ℝ
  gapConstant : ℝ
  covarianceError : ℝ
  nuisanceError : ℝ
  gapConstant_nonneg : 0 ≤ gapConstant
  covarianceError_nonneg : 0 ≤ covarianceError
  nuisanceError_nonneg : 0 ≤ nuisanceError
  leading_gap : ∀ c,
    d.primeInner d.coord c = 0 →
      gapConstant * d.primeNormSq c ≤ leadingForm c
  covariance_comparison : ∀ c,
    |actualVariance c - leadingForm c| ≤
      covarianceError * d.primeNormSq c
  nuisance_bound : ∀ c,
    nuisanceLoss c ≤ nuisanceError * d.primeNormSq c
  exact_null_schur : ∀ b mu,
    schurForm b =
      actualVariance (d.residual b mu) -
        nuisanceLoss (d.residual b mu)

/-- Conditional finite bridge: analytic leading-gap/comparison estimates
imply the full quotient lower bound.  This is the formal counterpart of
the passage from the minimizing arithmetic residual to (8.25). -/
theorem full_quotient_gap_of_inputs
    (inputs : BridgeInputs d) (q : Band → ℝ) (lambda kappa : ℝ)
    (hq : d.inGauge q) (hcoord : d.coordEnergy ≠ 0)
    (hV : 0 ≤ d.cellVariance) (hkappa : 0 ≤ kappa)
    (hsmall : kappa + inputs.covarianceError + inputs.nuisanceError ≤
      inputs.gapConstant) :
    kappa * d.bandNormSq q ≤
      inputs.schurForm (fun j => q j + lambda * d.center j) := by
  let b : Band → ℝ := fun j => q j + lambda * d.center j
  let mu : ℝ := d.physicalMinimizer b
  let c : Prime → ℝ := d.residual b mu
  have hnormal : d.primeInner d.coord c = 0 := by
    simpa [c, mu, b] using d.physicalMinimizer_normal b hcoord
  have hlead :
      inputs.gapConstant * d.primeNormSq c ≤ inputs.leadingForm c :=
    inputs.leading_gap c hnormal
  have hcompare := inputs.covariance_comparison c
  have hactual :
      inputs.leadingForm c -
          inputs.covarianceError * d.primeNormSq c ≤
        inputs.actualVariance c := by
    have hleft :
        -(inputs.covarianceError * d.primeNormSq c) ≤
          inputs.actualVariance c - inputs.leadingForm c :=
      (abs_le.mp hcompare).1
    linarith
  have hnuisance :
      inputs.nuisanceLoss c ≤
        inputs.nuisanceError * d.primeNormSq c :=
    inputs.nuisance_bound c
  have hschur :
      inputs.schurForm b =
        inputs.actualVariance c - inputs.nuisanceLoss c := by
    simpa [b, c] using inputs.exact_null_schur b mu
  have hprimeLower : d.bandNormSq q ≤ d.primeNormSq c := by
    change d.bandNormSq q ≤ d.physicalSq b mu
    simpa [b, mu] using d.physical_lower_bound q lambda hq hV
  have hprimeNonneg : 0 ≤ d.primeNormSq c := d.primeNormSq_nonneg c
  have hkprime :
      kappa * d.bandNormSq q ≤ kappa * d.primeNormSq c :=
    mul_le_mul_of_nonneg_left hprimeLower hkappa
  rw [hschur]
  have hcoefficient :
      kappa ≤ inputs.gapConstant - inputs.covarianceError -
        inputs.nuisanceError := by
    linarith
  have hscaled :
      kappa * d.primeNormSq c ≤
        (inputs.gapConstant - inputs.covarianceError -
          inputs.nuisanceError) * d.primeNormSq c :=
    mul_le_mul_of_nonneg_right hcoefficient hprimeNonneg
  linarith

/-- The same quotient bound stated for an arbitrary band vector, using
its canonical weighted-gauge decomposition. -/
theorem full_quotient_gap_arbitrary
    (inputs : BridgeInputs d) (b : Band → ℝ) (kappa : ℝ)
    (hcenter : d.centerEnergy ≠ 0) (hcoord : d.coordEnergy ≠ 0)
    (hV : 0 ≤ d.cellVariance) (hkappa : 0 ≤ kappa)
    (hsmall : kappa + inputs.covarianceError + inputs.nuisanceError ≤
      inputs.gapConstant) :
    kappa * d.bandNormSq (d.gaugePart b) ≤ inputs.schurForm b := by
  let q : Band → ℝ := d.gaugePart b
  let lambda : ℝ := d.gaugeCoefficient b
  have hq : d.inGauge q := by
    simpa [q] using d.gaugePart_inGauge b hcenter
  have hdecomp : (fun j => q j + lambda * d.center j) = b := by
    funext j
    exact d.gauge_decomposition b j
  have hcore := d.full_quotient_gap_of_inputs inputs q lambda kappa hq
    hcoord hV hkappa hsmall
  rw [hdecomp] at hcore
  simpa [q] using hcore

/-- The sup norm on a nonempty finite band space. -/
def bandSupNorm [Nonempty Band] (x : Band → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun j => |x j|

/-- The projected inverse is intentionally a separate contract.  In the
paper it is supplied by the continuum `L∞` inverse, arithmetic transfer,
and the stable projected-Schur perturbation lemma; it is not inferred
from the quadratic quotient gap. -/
structure ProjectedInverseContract [Nonempty Band] where
  operator : (Band → ℝ) → (Band → ℝ)
  inverse : (Band → ℝ) → (Band → ℝ)
  boundConstant : ℝ
  boundConstant_nonneg : 0 ≤ boundConstant
  operator_maps_gauge : ∀ q, d.inGauge q → d.inGauge (operator q)
  inverse_maps_gauge : ∀ q, d.inGauge q → d.inGauge (inverse q)
  left_inverse_on_gauge : ∀ q, d.inGauge q → inverse (operator q) = q
  right_inverse_on_gauge : ∀ q, d.inGauge q → operator (inverse q) = q
  inverse_bound : ∀ q, d.inGauge q →
    bandSupNorm (inverse q) ≤ boundConstant * bandSupNorm q

/-- A small eliminator recording exactly what the projected inverse
contract provides, without using or assuming the full quotient bound. -/
theorem projected_inverse_bound_of_contract [Nonempty Band]
    (contract : ProjectedInverseContract d) (q : Band → ℝ)
    (hq : d.inGauge q) :
    bandSupNorm (contract.inverse q) ≤
      contract.boundConstant * bandSupNorm q :=
  contract.inverse_bound q hq

end WeightedBandData

end WeightedBands

end

end Erdos390.Lemma84
