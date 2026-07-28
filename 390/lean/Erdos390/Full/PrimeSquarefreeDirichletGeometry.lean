import Erdos390.Full.FiniteAnchoredDirichletQuadratic
import Erdos390.Full.SquarefreeCovarianceReference
import Erdos390.Full.PoissonDickmanWeightedInverse
import Erdos390.Full.PaperPrimePowerRow

/-!
# Prime-level Dirichlet geometry for the squarefree reference covariance

The squarefree Dickman reference matrix is conjugated here on the literal
finite prime band.  The conjugating coordinate is `x_p = c_p / t_p`, the
vertex weight is `t_p / p`, and the quotient metric is `t_p^2 / p`.
Consequently the graph distance to a constant is exactly

`sum_p (c_p - mu * t_p)^2 / p`.

All identities are finite and exact.  The only analytic input in the final
anchor theorem is the already proved uniform negativity of the Dickman
kernel quotient on a fixed interior block.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.PrimeSquarefreeDirichletGeometry

open ArithmeticModel
open ConditionedPoissonLimit PoissonDickmanWeightedInverse
open PoissonDickmanDirichlet
open FiniteAnchoredDirichletQuadratic
open SquarefreeCovarianceReference

abbrev PrimeIndex (n W : ℕ) := {p : ℕ // p ∈ primeBand n W}

variable {n W : ℕ}

instance : Fintype (PrimeIndex n W) :=
  Fintype.ofFinset (primeBand n W) (fun _ ↦ Iff.rfl)

/-- The conjugated vertex measure `t_p / p`. -/
def primeWeight (n : ℕ) (p : PrimeIndex n W) : ℝ :=
  tPrime n p.1 / (p.1 : ℝ)

/-- The physical quotient metric `t_p^2 / p`. -/
def primeMetricWeight (n : ℕ) (p : PrimeIndex n W) : ℝ :=
  tPrime n p.1 ^ 2 / (p.1 : ℝ)

def primeDiagonal (n : ℕ) (p : PrimeIndex n W) : ℝ :=
  DickmanBasic.F (tPrime n p.1) * tPrime n p.1

def primeKernel (n : ℕ) (p q : PrimeIndex n W) : ℝ :=
  covarianceKernel (tPrime n p.1) (tPrime n q.1)

def dirichletCoordinate (n : ℕ)
    (c : PrimeIndex n W → ℝ) (p : PrimeIndex n W) : ℝ :=
  c p / tPrime n p.1

/-- The separated diagonal-plus-kernel form of the prime reference
quadratic. -/
def primeReferenceQuadratic (n : ℕ)
    (c : PrimeIndex n W → ℝ) : ℝ :=
  (∑ p, DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) * c p ^ 2) +
    ∑ p, ∑ q,
      covarianceKernel (tPrime n p.1) (tPrime n q.1) /
          ((p.1 : ℝ) * (q.1 : ℝ)) * c p * c q

/-- The same reference quadratic written with the literal primewise matrix
entry used by the signed squarefree comparison. -/
def primeReferenceEntryQuadratic (n : ℕ)
    (c : PrimeIndex n W → ℝ) : ℝ :=
  ∑ p, ∑ q, c p * c q * squarefreeReferenceEntry n p.1 q.1

/-- Literal prime quotient distance. -/
def primePhysicalDistance (n : ℕ)
    (c : PrimeIndex n W → ℝ) (mu : ℝ) : ℝ :=
  ∑ p, (1 / (p.1 : ℝ)) * (c p - mu * tPrime n p.1) ^ 2

/-- Literal reciprocal-weighted coefficient square norm. -/
def primeCoefficientL2Sq (c : PrimeIndex n W → ℝ) : ℝ :=
  ∑ p, (1 / (p.1 : ℝ)) * c p ^ 2

theorem tPrime_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < tPrime n p.1 := by
  have hp := prime_of_mem_primeBand p.2
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hlogy : 0 < Real.log (y n) := by
    rw [Scale.log_y hn0]
    exact mul_pos (by norm_num) (Scale.L_pos hn)
  unfold tPrime
  exact div_pos (Real.log_pos (by exact_mod_cast hp.one_lt)) hlogy

theorem primeWeight_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < primeWeight n p := by
  exact div_pos (tPrime_pos hn p) (by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos)

theorem primeMetricWeight_pos (hn : 1 < n) (p : PrimeIndex n W) :
    0 < primeMetricWeight n p := by
  exact div_pos (sq_pos_of_pos (tPrime_pos hn p)) (by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos)

theorem primeKernel_symm (p q : PrimeIndex n W) :
    primeKernel n p q = primeKernel n q p := by
  exact covarianceKernel_comm _ _

theorem tPrime_mem_unit (hn : 1 < n) (p : PrimeIndex n W) :
    tPrime n p.1 ∈ Icc (0 : ℝ) 1 :=
  ⟨(tPrime_pos hn p).le,
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn p.2⟩

/-- Exact conjugation of the separated prime reference quadratic. -/
theorem finiteReferenceQuadratic_eq_primeReferenceQuadratic
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) :
    referenceQuadratic (primeWeight n) (primeDiagonal n) (primeKernel n)
        (dirichletCoordinate n c) =
      primeReferenceQuadratic n c := by
  classical
  unfold referenceQuadratic primeReferenceQuadratic
  apply congrArg₂ (fun a b : ℝ ↦ a + b)
  · apply Finset.sum_congr rfl
    intro p hp
    unfold primeWeight primeDiagonal dirichletCoordinate
    have ht : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
    have hp0 : (p.1 : ℝ) ≠ 0 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
    field_simp [ht, hp0]
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    unfold primeWeight primeKernel dirichletCoordinate
    have htp : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
    have htq : tPrime n q.1 ≠ 0 := ne_of_gt (tPrime_pos hn q)
    have hp0 : (p.1 : ℝ) ≠ 0 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (prime_of_mem_primeBand q.2).ne_zero
    field_simp [htp, htq, hp0, hq0]

/-- Exact identification with the signed reference entries.  The extra
diagonal multiplier is counted once, while the kernel diagonal remains in
the full double sum. -/
theorem primeReferenceQuadratic_eq_entryQuadratic
    (c : PrimeIndex n W → ℝ) :
    primeReferenceQuadratic n c = primeReferenceEntryQuadratic n c := by
  classical
  have hentry (p q : PrimeIndex n W) :
      squarefreeReferenceEntry n p.1 q.1 =
        squarefreeKernelEntry n p.1 q.1 +
          if p = q then DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) else 0 := by
    by_cases hpq : p = q
    · subst q
      simp [squarefreeReferenceEntry]
      ring
    · have hpqVal : p.1 ≠ q.1 := by
        intro h
        exact hpq (Subtype.ext h)
      simp [squarefreeReferenceEntry, hpq, hpqVal]
  have hdiag (p : PrimeIndex n W) :
      (∑ q, c p * c q *
        (if p = q then DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) else 0)) =
          DickmanBasic.F (tPrime n p.1) / (p.1 : ℝ) * c p ^ 2 := by
    rw [Finset.sum_eq_single p]
    · simp
      ring
    · intro q hq hqp
      simp [Ne.symm hqp]
    · simp
  have hkernel :
      (∑ p, ∑ q,
        covarianceKernel (tPrime n p.1) (tPrime n q.1) /
            ((p.1 : ℝ) * (q.1 : ℝ)) * c p * c q) =
        ∑ p, ∑ q, c p * c q * squarefreeKernelEntry n p.1 q.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    unfold squarefreeKernelEntry
    ring
  unfold primeReferenceQuadratic primeReferenceEntryQuadratic
  simp_rw [hentry, mul_add, Finset.sum_add_distrib, hdiag]
  rw [hkernel, add_comm]

/-- Exact prime reference decomposition, including the literal finite
row-sum residual. -/
theorem primeReferenceQuadratic_eq_dirichlet_add_residual
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) :
    primeReferenceQuadratic n c =
      dirichletEnergy (primeWeight n) (primeKernel n)
          (dirichletCoordinate n c) +
        ∑ p, primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2 := by
  rw [← finiteReferenceQuadratic_eq_primeReferenceQuadratic hn c]
  exact referenceQuadratic_eq_dirichletEnergy_add_rowResidual
    (primeWeight n) (primeDiagonal n) (primeKernel n)
    (dirichletCoordinate n c) primeKernel_symm

/-- A row residual of relative size `epsilon * t_p` contributes at most
`epsilon` times the literal reciprocal coefficient square norm.  This is
the exact moving-low scaling: an additive `o(1)` row bound would not be
sufficient here. -/
theorem abs_rowResidualContribution_le
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) {epsilon : ℝ}
    (hresidual : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        epsilon * tPrime n p.1) :
    |∑ p, primeWeight n p *
        rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
          (dirichletCoordinate n c p) ^ 2| ≤
      epsilon * primeCoefficientL2Sq c := by
  classical
  have hterm (p : PrimeIndex n W) :
      |primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| ≤
        epsilon * ((1 / (p.1 : ℝ)) * c p ^ 2) := by
    have hw : 0 ≤ primeWeight n p := (primeWeight_pos hn p).le
    have hx : 0 ≤ (dirichletCoordinate n c p) ^ 2 := sq_nonneg _
    have hmul := mul_le_mul_of_nonneg_left (hresidual p)
      (mul_nonneg hw hx)
    calc
      |primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| =
          (primeWeight n p * (dirichletCoordinate n c p) ^ 2) *
            |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hx]
              ring
      _ ≤ (primeWeight n p * (dirichletCoordinate n c p) ^ 2) *
          (epsilon * tPrime n p.1) := hmul
      _ = epsilon * ((1 / (p.1 : ℝ)) * c p ^ 2) := by
        unfold primeWeight dirichletCoordinate
        have ht : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
        have hp0 : (p.1 : ℝ) ≠ 0 := by
          exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
        field_simp [ht, hp0]
  calc
    |∑ p, primeWeight n p *
        rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
          (dirichletCoordinate n c p) ^ 2| ≤
        ∑ p, |primeWeight n p *
          rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p *
            (dirichletCoordinate n c p) ^ 2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, epsilon * ((1 / (p.1 : ℝ)) * c p ^ 2) :=
      Finset.sum_le_sum fun p hp ↦ hterm p
    _ = epsilon * primeCoefficientL2Sq c := by
      unfold primeCoefficientL2Sq
      rw [Finset.mul_sum]

/-- Direct lower transfer from the anchored Dirichlet energy to the
reference quadratic after paying the sharp relative row residual. -/
theorem primeReferenceQuadratic_lower_of_dirichlet_and_residual
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) (mu gamma : ℝ)
    {epsilon : ℝ}
    (hdirichlet : gamma * primePhysicalDistance n c mu ≤
      dirichletEnergy (primeWeight n) (primeKernel n)
        (dirichletCoordinate n c))
    (hresidual : ∀ p : PrimeIndex n W,
      |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
        epsilon * tPrime n p.1) :
    gamma * primePhysicalDistance n c mu -
        epsilon * primeCoefficientL2Sq c ≤
      primeReferenceQuadratic n c := by
  have hdecomp := primeReferenceQuadratic_eq_dirichlet_add_residual hn c
  have herror := abs_rowResidualContribution_le hn c hresidual
  have hlower := neg_le_of_abs_le herror
  linarith

/-- The conjugated metric is exactly the physical prime distance. -/
theorem weightedDistance_eq_primePhysicalDistance
    (hn : 1 < n) (c : PrimeIndex n W → ℝ) (mu : ℝ) :
    weightedDistance (primeMetricWeight n) (dirichletCoordinate n c) mu =
      primePhysicalDistance n c mu := by
  classical
  unfold weightedDistance primePhysicalDistance
  apply Finset.sum_congr rfl
  intro p hp
  unfold primeMetricWeight dirichletCoordinate
  have ht : tPrime n p.1 ≠ 0 := ne_of_gt (tPrime_pos hn p)
  have hp0 : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
  field_simp [ht, hp0]

/-- Weighted mean on a nonempty positive-mass anchor block. -/
def anchorMean (n : ℕ) (anchor : Finset (PrimeIndex n W))
    (c : PrimeIndex n W → ℝ) : ℝ :=
  (∑ p ∈ anchor, primeWeight n p * dirichletCoordinate n c p) /
    anchorMass (primeWeight n) anchor

theorem anchor_centered
    (anchor : Finset (PrimeIndex n W))
    (c : PrimeIndex n W → ℝ)
    (hmass : anchorMass (primeWeight n) anchor ≠ 0) :
    ∑ p ∈ anchor, primeWeight n p *
        (dirichletCoordinate n c p - anchorMean n anchor c) = 0 := by
  classical
  have hmass' : (∑ p ∈ anchor, primeWeight n p) ≠ 0 := by
    simpa only [anchorMass] using hmass
  unfold anchorMean anchorMass
  rw [show (∑ p ∈ anchor, primeWeight n p *
      (dirichletCoordinate n c p -
        (∑ q ∈ anchor, primeWeight n q * dirichletCoordinate n c q) /
          ∑ q ∈ anchor, primeWeight n q)) =
      ∑ p ∈ anchor,
        (primeWeight n p * dirichletCoordinate n c p -
          ((∑ q ∈ anchor,
              primeWeight n q * dirichletCoordinate n c q) /
            ∑ q ∈ anchor, primeWeight n q) * primeWeight n p) by
    apply Finset.sum_congr rfl
    intro p hp
    ring]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  field_simp [hmass']
  ring

/-- A prime in an interior anchor block supplies the exact edge domination
needed by the finite multi-anchor theorem. -/
theorem anchor_edge_domination
    (hn : 1 < n) {epsilon kappa : ℝ}
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ q ∈ anchor,
      tPrime n q.1 ∈ Icc epsilon (1 - epsilon))
    (p : PrimeIndex n W) (q : PrimeIndex n W) (hq : q ∈ anchor) :
    kappa * primeMetricWeight n p * primeWeight n q ≤
      primeWeight n p * primeWeight n q * (-primeKernel n p q) := by
  have hqgap := hgap (tPrime n p.1) (tPrime_mem_unit hn p)
    (tPrime n q.1) (hinterior q hq)
  have hmul := mul_covarianceKernelQuotient_eq_kernel
    (s := tPrime n q.1) (t := tPrime n p.1)
    (tPrime_mem_unit hn q) (tPrime_mem_unit hn p)
  have hedge : kappa * tPrime n p.1 ≤
      -covarianceKernel (tPrime n p.1) (tPrime n q.1) := by
    rw [covarianceKernel_comm (tPrime n p.1) (tPrime n q.1)]
    nlinarith [tPrime_pos hn p]
  have hfactor : 0 ≤ primeWeight n p * primeWeight n q :=
    mul_nonneg (primeWeight_pos hn p).le (primeWeight_pos hn q).le
  calc
    kappa * primeMetricWeight n p * primeWeight n q =
        (primeWeight n p * primeWeight n q) *
          (kappa * tPrime n p.1) := by
      unfold primeMetricWeight primeWeight
      have hp0 : (p.1 : ℝ) ≠ 0 := by
        exact_mod_cast (prime_of_mem_primeBand p.2).ne_zero
      have hq0 : (q.1 : ℝ) ≠ 0 := by
        exact_mod_cast (prime_of_mem_primeBand q.2).ne_zero
      field_simp [hp0, hq0]
    _ ≤ (primeWeight n p * primeWeight n q) *
        (-covarianceKernel (tPrime n p.1) (tPrime n q.1)) :=
      mul_le_mul_of_nonneg_left hedge hfactor
    _ = primeWeight n p * primeWeight n q * (-primeKernel n p q) := by
      rfl

/-- Exact prime-band quotient lower bound from a positive interior anchor
block.  No continuum-to-arithmetic operator convergence is an assumption:
the continuum input is only the pointwise Dickman kernel quotient gap. -/
theorem exists_primeDirichlet_anchor_lower
    (hn : 1 < n) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchor : Finset (PrimeIndex n W))
    (hinterior : ∀ q ∈ anchor,
      tPrime n q.1 ∈ Icc epsilon (1 - epsilon))
    (hmass : 0 < anchorMass (primeWeight n) anchor) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ c : PrimeIndex n W → ℝ,
        (kappa / 2) * anchorMass (primeWeight n) anchor *
            primePhysicalDistance n c (anchorMean n anchor c) ≤
          dirichletEnergy (primeWeight n) (primeKernel n)
            (dirichletCoordinate n c) := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap hepsilon hhalf
  refine ⟨kappa, hkappa, ?_⟩
  intro c
  rw [← weightedDistance_eq_primePhysicalDistance hn c]
  exact half_kappa_anchorMass_mul_weightedDistance_le_dirichletEnergy
    (primeWeight n) (primeMetricWeight n) (primeKernel n) anchor
    (dirichletCoordinate n c) (anchorMean n anchor c) kappa hkappa.le
    (fun p ↦ (primeWeight_pos hn p).le)
    (fun p ↦ (primeMetricWeight_pos hn p).le)
    (fun p q ↦ covarianceKernel_nonpos (tPrime_mem_unit hn p)
      (tPrime_mem_unit hn q))
    (anchor_edge_domination hn hgap anchor hinterior)
    (anchor_centered anchor c hmass.ne')

end Erdos390.Full.PrimeSquarefreeDirichletGeometry
