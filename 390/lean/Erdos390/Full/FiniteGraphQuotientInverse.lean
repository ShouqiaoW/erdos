import Mathlib

/-!
# Mesh-independent inverse for a finite nonlocal graph Laplacian

This is the finite compression of the maximum/minimum argument used by the
weighted Poisson--Dickman quotient inverse.  A common positive anchor measure
seen by every row gives an oscillation bound independent of the number or
shape of cells.  Projection to any positive weighted gauge then gives an
actual inverse bound on that gauge; no inverse is an input.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]

def graphOperator (edge : Band → Band → ℝ) (q : Band → ℝ) (i : Band) : ℝ :=
  ∑ j, edge i j * (q i - q j)

def weightTotal (omega : Band → ℝ) : ℝ :=
  ∑ i, omega i

def weightedMean (omega x : Band → ℝ) : ℝ :=
  (∑ i, omega i * x i) / weightTotal omega

def meanProjection (omega x : Band → ℝ) (i : Band) : ℝ :=
  x i - weightedMean omega x

def inWeightedGauge (omega q : Band → ℝ) : Prop :=
  ∑ i, omega i * q i = 0

omit [DecidableEq Band] in
lemma graphOperator_at_max_nonneg
    (edge : Band → Band → ℝ) (q : Band → ℝ) {imax : Band}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hmax : ∀ j, q imax ≥ q j) :
    0 ≤ graphOperator edge q imax := by
  unfold graphOperator
  exact Finset.sum_nonneg fun j hj =>
    mul_nonneg (hedge imax j) (sub_nonneg.mpr (hmax j))

omit [DecidableEq Band] in
lemma graphOperator_at_min_nonpos
    (edge : Band → Band → ℝ) (q : Band → ℝ) {imin : Band}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hmin : ∀ j, q imin ≤ q j) :
    graphOperator edge q imin ≤ 0 := by
  unfold graphOperator
  exact Finset.sum_nonpos fun j hj =>
    mul_nonpos_of_nonneg_of_nonpos (hedge imin j)
      (sub_nonpos.mpr (hmin j))

omit [DecidableEq Band] in
/-- Uniform edge domination by one anchor measure controls oscillation. -/
theorem exists_center_of_graphOperator_bound
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor q : Band → ℝ)
    {kappa G : ℝ}
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (hbound : ∀ i, |graphOperator edge q i| ≤ G) :
    ∃ mu : ℝ, ∀ i,
      |q i - mu| ≤ G / (kappa * ∑ j, anchor j) := by
  obtain ⟨imax, himax, hmax'⟩ :=
    Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  obtain ⟨imin, himin, hmin'⟩ :=
    Finset.exists_min_image Finset.univ q Finset.univ_nonempty
  have hmax (j : Band) : q j ≤ q imax := by
    exact hmax' j (Finset.mem_univ j)
  have hmin (j : Band) : q imin ≤ q j := by
    exact hmin' j (Finset.mem_univ j)
  have hmaxLower :
      kappa * ∑ j, anchor j * (q imax - q j) ≤
        graphOperator edge q imax := by
    unfold graphOperator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hdiff : 0 ≤ q imax - q j := sub_nonneg.mpr (hmax j)
    calc
      kappa * (anchor j * (q imax - q j)) =
          (kappa * anchor j) * (q imax - q j) := by ring
      _ ≤ edge imax j * (q imax - q j) :=
        mul_le_mul_of_nonneg_right (hdom imax j) hdiff
  have hminLower :
      kappa * ∑ j, anchor j * (q j - q imin) ≤
        -graphOperator edge q imin := by
    unfold graphOperator
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hdiff : 0 ≤ q j - q imin := sub_nonneg.mpr (hmin j)
    calc
      kappa * (anchor j * (q j - q imin)) =
          (kappa * anchor j) * (q j - q imin) := by ring
      _ ≤ edge imin j * (q j - q imin) :=
        mul_le_mul_of_nonneg_right (hdom imin j) hdiff
      _ = -(edge imin j * (q imin - q j)) := by ring
  have hoperatorUpper :
      graphOperator edge q imax + (-graphOperator edge q imin) ≤ 2 * G := by
    have hmaxBound := hbound imax
    have hminBound := hbound imin
    have h₁ : graphOperator edge q imax ≤ G :=
      (le_abs_self _).trans hmaxBound
    have h₂ : -graphOperator edge q imin ≤ G :=
      (neg_le_abs _).trans hminBound
    linarith
  have hsumIdentity :
      (∑ j, anchor j * (q imax - q j)) +
          (∑ j, anchor j * (q j - q imin)) =
        (∑ j, anchor j) * (q imax - q imin) := by
    rw [← Finset.sum_add_distrib, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hoscScaled :
      (kappa * ∑ j, anchor j) * (q imax - q imin) ≤ 2 * G := by
    calc
      (kappa * ∑ j, anchor j) * (q imax - q imin) =
          kappa * ((∑ j, anchor j * (q imax - q j)) +
            ∑ j, anchor j * (q j - q imin)) := by
        rw [hsumIdentity]
        ring
      _ = kappa * (∑ j, anchor j * (q imax - q j)) +
          kappa * (∑ j, anchor j * (q j - q imin)) := by ring
      _ ≤ graphOperator edge q imax + (-graphOperator edge q imin) :=
        add_le_add hmaxLower hminLower
      _ ≤ 2 * G := hoperatorUpper
  have hden : 0 < kappa * ∑ j, anchor j :=
    mul_pos hkappa hanchorTotal
  have hosc : q imax - q imin ≤
      2 * G / (kappa * ∑ j, anchor j) := by
    exact (le_div_iff₀ hden).2 (by
      simpa only [mul_comm] using hoscScaled)
  refine ⟨(q imax + q imin) / 2, ?_⟩
  intro i
  rw [abs_le]
  constructor
  · have hhalf : (q imax - q imin) / 2 ≤
        G / (kappa * ∑ j, anchor j) := by
      calc
        (q imax - q imin) / 2 ≤
            (2 * G / (kappa * ∑ j, anchor j)) / 2 := by linarith
        _ = G / (kappa * ∑ j, anchor j) := by ring
    linarith [hmin i]
  · have hhalf : (q imax - q imin) / 2 ≤
        G / (kappa * ∑ j, anchor j) := by
      calc
        (q imax - q imin) / 2 ≤
            (2 * G / (kappa * ∑ j, anchor j)) / 2 := by linarith
        _ = G / (kappa * ∑ j, anchor j) := by ring
    linarith [hmax i]

omit [DecidableEq Band] in
/-- Projecting the graph operator to an arbitrary positive weighted gauge
still has a uniform inverse bound.  This is a conclusion from the edge
geometry, not an inverse hypothesis. -/
theorem abs_le_of_gauge_projectedGraph_bound
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega q : Band → ℝ)
    {kappa G : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (hgauge : ∑ i, omega i * q i = 0)
    (hprojected : ∀ i,
      |meanProjection omega (graphOperator edge q) i| ≤ G) :
    ∀ i, |q i| ≤ 4 * G / (kappa * ∑ j, anchor j) := by
  let c := weightedMean omega (graphOperator edge q)
  obtain ⟨imax, himax, hmax'⟩ :=
    Finset.exists_max_image Finset.univ q Finset.univ_nonempty
  obtain ⟨imin, himin, hmin'⟩ :=
    Finset.exists_min_image Finset.univ q Finset.univ_nonempty
  have hmax (j : Band) : q j ≤ q imax :=
    hmax' j (Finset.mem_univ j)
  have hmin (j : Band) : q imin ≤ q j :=
    hmin' j (Finset.mem_univ j)
  have hgraphMax : 0 ≤ graphOperator edge q imax :=
    graphOperator_at_max_nonneg edge q hedge (fun j => hmax j)
  have hgraphMin : graphOperator edge q imin ≤ 0 :=
    graphOperator_at_min_nonpos edge q hedge (fun j => hmin j)
  have hprojMax := hprojected imax
  have hprojMin := hprojected imin
  have hcLower : -G ≤ c := by
    unfold meanProjection at hprojMax
    dsimp only [c]
    have := le_of_abs_le hprojMax
    linarith [hgraphMax]
  have hcUpper : c ≤ G := by
    unfold meanProjection at hprojMin
    dsimp only [c]
    have := neg_le_of_abs_le hprojMin
    linarith [hgraphMin]
  have hgraphBound (i : Band) : |graphOperator edge q i| ≤ 2 * G := by
    have hi := hprojected i
    unfold meanProjection at hi
    dsimp only [c] at hcLower hcUpper ⊢
    rw [abs_le] at hi ⊢
    constructor <;> linarith [hi.1, hi.2]
  obtain ⟨mu, hmu⟩ := exists_center_of_graphOperator_bound
    edge anchor q hdom hkappa hanchorTotal hgraphBound
  have hmuAbs : |mu| ≤ 2 * G / (kappa * ∑ j, anchor j) := by
    have htotal0 : (∑ i, omega i) ≠ 0 := ne_of_gt homegaTotal
    have hidentity :
        mu = (∑ i, omega i * (mu - q i)) /
          (∑ i, omega i) := by
      have hsum :
          (∑ i, omega i * (mu - q i)) = mu * (∑ i, omega i) := by
        calc
          (∑ i, omega i * (mu - q i)) =
              (∑ i, omega i * mu) - ∑ i, omega i * q i := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = mu * (∑ i, omega i) := by
            rw [hgauge, sub_zero]
            calc
              (∑ i, omega i * mu) = (∑ i, omega i) * mu :=
                (Finset.sum_mul Finset.univ omega mu).symm
              _ = mu * (∑ i, omega i) := by ring
      rw [hsum]
      apply (eq_div_iff htotal0).2
      ring
    rw [hidentity, abs_div, abs_of_pos homegaTotal]
    calc
      |∑ i, omega i * (mu - q i)| / (∑ i, omega i) ≤
          (∑ i, omega i *
            (2 * G / (kappa * ∑ j, anchor j))) /
              (∑ i, omega i) := by
        apply div_le_div_of_nonneg_right _ homegaTotal.le
        calc
          |∑ i, omega i * (mu - q i)| ≤
              ∑ i, |omega i * (mu - q i)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, omega i *
              (2 * G / (kappa * ∑ j, anchor j)) := by
            apply Finset.sum_le_sum
            intro i hi
            rw [abs_mul, abs_of_nonneg (homega i), abs_sub_comm]
            exact mul_le_mul_of_nonneg_left (hmu i) (homega i)
      _ = 2 * G / (kappa * ∑ j, anchor j) := by
        rw [← Finset.sum_mul]
        field_simp [htotal0]
  intro i
  calc
    |q i| = |(q i - mu) + mu| := by ring_nf
    _ ≤ |q i - mu| + |mu| := abs_add_le _ _
    _ ≤ 2 * G / (kappa * ∑ j, anchor j) +
        2 * G / (kappa * ∑ j, anchor j) :=
      add_le_add (hmu i) hmuAbs
    _ = 4 * G / (kappa * ∑ j, anchor j) := by ring

end Erdos390.Full.FiniteGraphQuotientInverse
