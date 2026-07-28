import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Finite anchored Dirichlet quadratic forms

This file records the exact finite algebra needed in the slow-direction
part of paper Lemma 8.6.  A symmetric reference covariance is a graph
Dirichlet energy plus its (possibly nonzero) discrete row-sum residual.
A positive block of anchor vertices then controls the quotient distance to
the constant direction.  The statements are entirely finite; in
particular, no continuum limit or spectral-gap hypothesis is hidden in the
algebra.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteAnchoredDirichletQuadratic

variable {ι : Type*} [Fintype ι]

/-- The finite reference quadratic with vertex weight `weight`, diagonal
multiplier `diagonal`, and symmetric signed kernel `kernel`. -/
def referenceQuadratic
    (weight diagonal : ι → ℝ) (kernel : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, weight i * diagonal i * x i ^ 2) +
    ∑ i, ∑ j, weight i * weight j * kernel i j * x i * x j

/-- The positive-sign convention for the graph energy associated with the
signed kernel. -/
def dirichletEnergy
    (weight : ι → ℝ) (kernel : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ i, ∑ j,
      weight i * weight j * (-kernel i j) * (x i - x j) ^ 2

/-- The error in the discrete analogue of the continuum row-sum identity. -/
def rowResidual
    (weight diagonal : ι → ℝ) (kernel : ι → ι → ℝ) (i : ι) : ℝ :=
  diagonal i + ∑ j, weight j * kernel i j

/-- Exact finite Dirichlet decomposition.  This is the discrete identity
behind the passage from the squarefree reference covariance to the
quotient energy. -/
theorem referenceQuadratic_eq_dirichletEnergy_add_rowResidual
    (weight diagonal : ι → ℝ) (kernel : ι → ι → ℝ) (x : ι → ℝ)
    (hsymm : ∀ i j, kernel i j = kernel j i) :
    referenceQuadratic weight diagonal kernel x =
      dirichletEnergy weight kernel x +
        ∑ i, weight i * rowResidual weight diagonal kernel i * x i ^ 2 := by
  classical
  let D : ℝ := ∑ i, weight i * diagonal i * x i ^ 2
  let L : ℝ := ∑ i, ∑ j,
    weight i * weight j * kernel i j * x i ^ 2
  let R : ℝ := ∑ i, ∑ j,
    weight i * weight j * kernel i j * x j ^ 2
  let C : ℝ := ∑ i, ∑ j,
    weight i * weight j * kernel i j * x i * x j
  have hR : R = L := by
    calc
      R = ∑ i, ∑ j,
          weight j * weight i * kernel j i * x i ^ 2 := by
            dsimp only [R]
            rw [Finset.sum_comm]
      _ = L := by
        dsimp only [L]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsymm j i]
        ring
  have hCtwo :
      (∑ i, ∑ j,
        2 * (weight i * weight j * kernel i j * x i * x j)) = 2 * C := by
    dsimp only [C]
    symm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
  have henergy :
      dirichletEnergy weight kernel x =
        (-L + 2 * C - R) / 2 := by
    unfold dirichletEnergy
    rw [show (∑ i, ∑ j,
        weight i * weight j * (-kernel i j) * (x i - x j) ^ 2) =
          -L + 2 * C - R by
      dsimp only [L, C, R]
      simp_rw [show ∀ i j, weight i * weight j * (-kernel i j) *
          (x i - x j) ^ 2 =
            -(weight i * weight j * kernel i j * x i ^ 2) +
              2 * (weight i * weight j * kernel i j * x i * x j) -
              weight i * weight j * kernel i j * x j ^ 2 by
        intro i j
        ring]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        Finset.sum_neg_distrib]
      rw [hCtwo]]
    ring
  have hresidual :
      (∑ i, weight i * rowResidual weight diagonal kernel i * x i ^ 2) =
        D + L := by
    unfold rowResidual
    calc
      (∑ i, weight i *
          (diagonal i + ∑ j, weight j * kernel i j) * x i ^ 2) =
          (∑ i, weight i * diagonal i * x i ^ 2) +
            ∑ i, weight i * (∑ j, weight j * kernel i j) * x i ^ 2 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              ring
      _ = D + L := by
        apply congrArg₂ (fun a b : ℝ => a + b)
        · rfl
        · dsimp only [L]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
  unfold referenceQuadratic
  change D + C = _
  rw [henergy, hresidual, hR]
  ring

/-- Harmonic mass of a finite anchor set. -/
def anchorMass (weight : ι → ℝ) (anchor : Finset ι) : ℝ :=
  ∑ j ∈ anchor, weight j

/-- Weighted square distance to a scalar representative of the constant
direction. -/
def weightedDistance (metricWeight : ι → ℝ) (x : ι → ℝ) (mu : ℝ) : ℝ :=
  ∑ i, metricWeight i * (x i - mu) ^ 2

/-- Pair variation between every vertex and the anchor block. -/
def anchorPairVariation
    (metricWeight anchorWeight : ι → ℝ) (anchor : Finset ι)
    (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j ∈ anchor,
    metricWeight i * anchorWeight j * (x i - x j) ^ 2

/-- The weighted anchor mean gives an exact one-sided Poincare inequality.
The centering equation is stated explicitly so that applications may use a
literal finite arithmetic mean. -/
theorem anchorMass_mul_weightedDistance_le_anchorPairVariation
    (metricWeight anchorWeight : ι → ℝ) (anchor : Finset ι)
    (x : ι → ℝ) (mu : ℝ)
    (hmetric : ∀ i, 0 ≤ metricWeight i)
    (hanchor : ∀ j ∈ anchor, 0 ≤ anchorWeight j)
    (hcenter : ∑ j ∈ anchor, anchorWeight j * (x j - mu) = 0) :
    anchorMass anchorWeight anchor * weightedDistance metricWeight x mu ≤
      anchorPairVariation metricWeight anchorWeight anchor x := by
  classical
  have hinner (i : ι) :
      anchorMass anchorWeight anchor * (x i - mu) ^ 2 ≤
        ∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2 := by
    have hexact :
        (∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2) =
          anchorMass anchorWeight anchor * (x i - mu) ^ 2 +
            ∑ j ∈ anchor, anchorWeight j * (x j - mu) ^ 2 := by
      have hcross :
          ∑ j ∈ anchor,
              (2 * (x i - mu)) * (anchorWeight j * (x j - mu)) = 0 := by
        rw [← Finset.mul_sum, hcenter, mul_zero]
      unfold anchorMass
      calc
        (∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2) =
            ∑ j ∈ anchor,
              (anchorWeight j * (x i - mu) ^ 2 +
                anchorWeight j * (x j - mu) ^ 2 -
                (2 * (x i - mu)) * (anchorWeight j * (x j - mu))) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (∑ j ∈ anchor, anchorWeight j) * (x i - mu) ^ 2 +
              ∑ j ∈ anchor, anchorWeight j * (x j - mu) ^ 2 -
              ∑ j ∈ anchor,
                (2 * (x i - mu)) * (anchorWeight j * (x j - mu)) := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                Finset.sum_mul]
        _ = (∑ j ∈ anchor, anchorWeight j) * (x i - mu) ^ 2 +
              ∑ j ∈ anchor, anchorWeight j * (x j - mu) ^ 2 := by
              rw [hcross]
              ring
    rw [hexact]
    apply le_add_of_nonneg_right
    exact Finset.sum_nonneg fun j hj =>
      mul_nonneg (hanchor j hj) (sq_nonneg _)
  unfold weightedDistance anchorPairVariation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hright :
      (∑ j ∈ anchor,
        metricWeight i * anchorWeight j * (x i - x j) ^ 2) =
        metricWeight i *
          (∑ j ∈ anchor, anchorWeight j * (x i - x j) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hright]
  have hmul := mul_le_mul_of_nonneg_left (hinner i) (hmetric i)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- A nonnegative graph whose anchor edges dominate a product measure
controls the weighted quotient distance.  This is the exact finite
multi-anchor estimate used after the Dickman kernel gap. -/
theorem half_kappa_anchorMass_mul_weightedDistance_le_dirichletEnergy
    (weight metricWeight : ι → ℝ) (kernel : ι → ι → ℝ)
    (anchor : Finset ι) (x : ι → ℝ) (mu kappa : ℝ)
    (hkappa : 0 ≤ kappa)
    (hweight : ∀ i, 0 ≤ weight i)
    (hmetric : ∀ i, 0 ≤ metricWeight i)
    (hkernel : ∀ i j, kernel i j ≤ 0)
    (hanchorEdge : ∀ i, ∀ j ∈ anchor,
      kappa * metricWeight i * weight j ≤
        weight i * weight j * (-kernel i j))
    (hcenter : ∑ j ∈ anchor, weight j * (x j - mu) = 0) :
    (kappa / 2) * anchorMass weight anchor *
        weightedDistance metricWeight x mu ≤
      dirichletEnergy weight kernel x := by
  classical
  have hpair :=
    anchorMass_mul_weightedDistance_le_anchorPairVariation
      metricWeight weight anchor x mu hmetric
      (fun j hj => hweight j) hcenter
  have hkpair :
      kappa * anchorPairVariation metricWeight weight anchor x ≤
        ∑ i, ∑ j,
          weight i * weight j * (-kernel i j) * (x i - x j) ^ 2 := by
    unfold anchorPairVariation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    calc
      (∑ j ∈ anchor,
          kappa * (metricWeight i * weight j * (x i - x j) ^ 2)) ≤
          ∑ j ∈ anchor,
            weight i * weight j * (-kernel i j) * (x i - x j) ^ 2 := by
            apply Finset.sum_le_sum
            intro j hj
            have hedge := hanchorEdge i j hj
            nlinarith [sq_nonneg (x i - x j)]
      _ ≤ ∑ j,
          weight i * weight j * (-kernel i j) * (x i - x j) ^ 2 := by
            apply Finset.sum_le_univ_sum_of_nonneg
            intro j
            exact mul_nonneg
              (mul_nonneg (mul_nonneg (hweight i) (hweight j))
                (neg_nonneg.mpr (hkernel i j))) (sq_nonneg _)
  have hscaled :
      kappa * anchorMass weight anchor *
          weightedDistance metricWeight x mu ≤
        kappa * anchorPairVariation metricWeight weight anchor x := by
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hpair hkappa
  unfold dirichletEnergy
  calc
    (kappa / 2) * anchorMass weight anchor *
        weightedDistance metricWeight x mu =
        (1 / 2 : ℝ) *
          (kappa * anchorMass weight anchor *
            weightedDistance metricWeight x mu) := by ring
    _ ≤ (1 / 2 : ℝ) *
        (kappa * anchorPairVariation metricWeight weight anchor x) :=
      mul_le_mul_of_nonneg_left hscaled (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (∑ i, ∑ j,
          weight i * weight j * (-kernel i j) * (x i - x j) ^ 2) :=
      mul_le_mul_of_nonneg_left hkpair (by norm_num)

end Erdos390.Full.FiniteAnchoredDirichletQuadratic
