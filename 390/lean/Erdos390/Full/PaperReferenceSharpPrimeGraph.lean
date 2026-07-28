import Erdos390.Full.PaperActualSlowRightRowFinite
import Erdos390.Full.FiniteGraphStableInverse
import Erdos390.Full.PaperCanonicalSlowKappa

/-!
# Prime-graph model for the literal sharp reference band operator

The endpoint double-quadrature route loses a factor depending on the first
cell width.  This file instead performs the comparison before band
quadrature.  A band coefficient `alpha_j x_j` is split exactly as

`t_p x_j + (alpha_j - t_p) x_j`.

The first term is a compression of the literal finite prime graph.  The
second is controlled by exact arithmetic centering.  Consequently the
constants below do not involve a least band centre, the number of bands, or
the low-cell width.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic FiniteGraphQuotientInverse
open ConditionedPoissonLimit DickmanBasic
open PoissonDickmanDirichlet
open PaperCanonicalSlowKappa

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Compression of the literal prime Dirichlet graph to band-constant
quotient coordinates.  The normalization is exactly
`H_i alpha_i = sum_{p in i} t_p/p`. -/
def compressedPrimeGraphEdge (i j : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q ∈ B.partition.data.fiber j,
        (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
          (-primeKernel B.sampleData.n p q)

/-- Band average of the exact finite prime-row null defect. -/
def compressedPrimeResidual (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) *
        rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p

/-- The residual-row contribution with the band coefficient kept inside
the finite sum.  This syntactic form makes the exact decomposition literal;
it is subsequently bounded by the scalar residual estimate. -/
def referenceResidualError (x : Band → ℝ) (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) *
        rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p * x i

/-- The part left after replacing each arithmetic band centre by the
literal prime coordinate in the diagonal term. -/
def referenceCenteringDiagonal (x : Band → ℝ) (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
        B.primeDeviation p * x i

/-- The corresponding centred kernel term. -/
def referenceCenteringKernel (x : Band → ℝ) (i : Band) : ℝ :=
  (1 / (B.harmonicMass i * B.bandCenter i)) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q * x (B.partition.band q) *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))

/-- Exact first-moment identity on an actual arithmetic fiber. -/
theorem fiber_primeWeight_sum_eq_mass_mul_center (i : Band) :
    (∑ p ∈ B.partition.data.fiber i,
      primeWeight B.sampleData.n p) =
        B.harmonicMass i * B.bandCenter i := by
  change (∑ p ∈ B.partition.data.fiber i,
      tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = _
  have h : (∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        B.harmonicMass i * B.bandCenter i := by
    unfold harmonicMass bandCenter
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass i *
        ((∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass i)
    field_simp [ne_of_gt (B.partition.data.mass_pos i)]
  calc
    (∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 / (p.1 : ℝ)) =
        ∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = B.harmonicMass i * B.bandCenter i := h

/-- Exact decomposition of the literal signed reference sharp row into the
compressed prime graph, its finite row defect, and the two arithmetic
centering errors. -/
theorem referenceSharpRow_eq_primeGraph_add_errors
    (x : Band → ℝ) (i : Band) :
    referenceSharpRow B.partition x i =
      graphOperator B.compressedPrimeGraphEdge x i +
        B.referenceResidualError x i +
        B.referenceCenteringDiagonal x i +
        B.referenceCenteringKernel x i := by
  let H := B.harmonicMass i
  let alpha := B.bandCenter i
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have hband (p : BandPrime B.sampleData.n B.sampleData.W)
      (hp : p ∈ B.partition.data.fiber i) : B.partition.band p = i := by
    simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
  have hcenter (q : BandPrime B.sampleData.n B.sampleData.W) :
      B.bandCenter (B.partition.band q) =
        tPrime B.sampleData.n q.1 + B.primeDeviation q := by
    unfold primeDeviation
    ring
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W)
      (hp : p ∈ B.partition.data.fiber i) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1) =
        (1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i +
          (1 / (p.1 : ℝ)) *
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (-(primeWeight B.sampleData.n q *
                    primeKernel B.sampleData.n p q)) *
                (x i - x (B.partition.band q))) +
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p * x i +
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
    have hdiag :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
            (if p.1 = q.1 then
              F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
            else 0)) =
          (B.bandCenter (B.partition.band p) * x (B.partition.band p)) *
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q hq hqp
        have hpqVal : p.1 ≠ q.1 := by
          intro hpq
          exact hqp (Subtype.ext hpq.symm)
        simp [hpqVal]
      · simp
    let a : BandPrime B.sampleData.n B.sampleData.W → ℝ :=
      fun q ↦ primeWeight B.sampleData.n q *
        primeKernel B.sampleData.n p q
    have hkernelT :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (tPrime B.sampleData.n q.1 * x (B.partition.band q)) *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          (1 / (p.1 : ℝ)) *
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              a q * x (B.partition.band q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      unfold a primeWeight primeKernel squarefreeKernelEntry
      ring
    have hkernelG :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.primeDeviation q * x (B.partition.band q)) *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold squarefreeKernelEntry
      ring
    have hkernelSplit :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          (1 / (p.1 : ℝ)) *
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                a q * x (B.partition.band q) +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * x (B.partition.band q) *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) /
                    ((p.1 : ℝ) * (q.1 : ℝ)) := by
      calc
        _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            ((tPrime B.sampleData.n q.1 + B.primeDeviation q) *
              x (B.partition.band q)) *
                squarefreeKernelEntry B.sampleData.n p.1 q.1 := by
              apply Finset.sum_congr rfl
              intro q hq
              rw [← hcenter q]
        _ = (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (tPrime B.sampleData.n q.1 * x (B.partition.band q)) *
                squarefreeKernelEntry B.sampleData.n p.1 q.1) +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (B.primeDeviation q * x (B.partition.band q)) *
                squarefreeKernelEntry B.sampleData.n p.1 q.1 := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro q hq
              ring
        _ = _ := by rw [hkernelT, hkernelG]
    have hdiagSplit :
        (B.bandCenter (B.partition.band p) * x (B.partition.band p)) *
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) =
          (1 / (p.1 : ℝ)) *
              (F (tPrime B.sampleData.n p.1) *
                tPrime B.sampleData.n p.1) * x i +
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
              B.primeDeviation p * x i := by
      rw [hcenter p, hband p hp]
      ring
    have hgraphExpand :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(a q)) * (x i - x (B.partition.band q))) =
          -(∑ q : BandPrime B.sampleData.n B.sampleData.W, a q) * x i +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              a q * x (B.partition.band q) := by
      calc
        _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            ((-(a q)) * x i + a q * x (B.partition.band q)) := by
              apply Finset.sum_congr rfl
              intro q hq
              ring
        _ = (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (-(a q)) * x i) +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              a q * x (B.partition.band q) := Finset.sum_add_distrib
        _ = _ := by
              rw [← Finset.sum_mul, Finset.sum_neg_distrib]
    simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal, mul_add]
    rw [Finset.sum_add_distrib, hdiag, hkernelSplit, hdiagSplit]
    unfold rowResidual primeDiagonal
    have hgraphExpand' :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) *
            (x i - x (B.partition.band q))) =
          -(∑ q : BandPrime B.sampleData.n B.sampleData.W,
              primeWeight B.sampleData.n q *
                primeKernel B.sampleData.n p q) * x i +
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (primeWeight B.sampleData.n q *
                primeKernel B.sampleData.n p q) *
                  x (B.partition.band q) := by
      simpa only [a] using hgraphExpand
    rw [hgraphExpand']
    ring
  unfold referenceSharpRow referenceBandRow
    compressedPrimeGraphEdge referenceResidualError
    referenceCenteringDiagonal referenceCenteringKernel graphOperator
  simp only
  change ((1 / B.harmonicMass i) *
      (∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
            squarefreeReferenceEntry B.sampleData.n p.1 q.1)) /
      B.bandCenter i = _
  rw [show (∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        (B.bandCenter (B.partition.band q) * x (B.partition.band q)) *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1) =
      ∑ p ∈ B.partition.data.fiber i,
        ((1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i +
          (1 / (p.1 : ℝ)) *
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (-(primeWeight B.sampleData.n q *
                    primeKernel B.sampleData.n p q)) *
                (x i - x (B.partition.band q))) +
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p * x i +
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))) by
    apply Finset.sum_congr rfl
    intro p hp
    exact hinner p hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hqsplit (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) *
            (x i - x (B.partition.band q))) =
        ∑ j : Band, ∑ q ∈ B.partition.data.fiber j,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) * (x i - x j) := by
    rw [← Finset.sum_fiberwise Finset.univ B.partition.band
      (fun q : BandPrime B.sampleData.n B.sampleData.W ↦
        (-(primeWeight B.sampleData.n q *
            primeKernel B.sampleData.n p q)) *
          (x i - x (B.partition.band q)))]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro q hq
    have hqj : B.partition.band q = j := by
      simpa [Erdos390.Lemma84.WeightedBandData.fiber] using hq
    rw [hqj]
  rw [show (∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) *
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (-(primeWeight B.sampleData.n q *
              primeKernel B.sampleData.n p q)) *
            (x i - x (B.partition.band q)))) =
      ∑ j : Band,
        (∑ p ∈ B.partition.data.fiber i,
          ∑ q ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
              (-primeKernel B.sampleData.n p q)) *
          (x i - x j) by
    simp_rw [hqsplit, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    symm
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    ring]
  have hgraphScale :
      (∑ j : Band,
        ((1 / (B.harmonicMass i * B.bandCenter i)) *
          (∑ p ∈ B.partition.data.fiber i,
            ∑ q ∈ B.partition.data.fiber j,
              (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
                (-primeKernel B.sampleData.n p q))) * (x i - x j)) =
        (1 / (B.harmonicMass i * B.bandCenter i)) *
          ∑ j : Band,
            (∑ p ∈ B.partition.data.fiber i,
              ∑ q ∈ B.partition.data.fiber j,
                (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
                  (-primeKernel B.sampleData.n p q)) * (x i - x j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hgraphScale]
  simp only [div_eq_mul_inv]
  ring

/-- Literal prime-anchor mass compressed to the arithmetic bands. -/
def compressedPrimeAnchor
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (j : Band) : ℝ :=
  ∑ q ∈ B.partition.data.fiber j,
    if q ∈ anchor then primeWeight B.sampleData.n q else 0

theorem compressedPrimeAnchor_nonneg
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (j : Band) :
    0 ≤ B.compressedPrimeAnchor anchor j := by
  unfold compressedPrimeAnchor
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact (primeWeight_pos B.n_gt_one q).le
  · exact le_rfl

/-- Compression preserves the whole literal prime-anchor mass exactly. -/
theorem sum_compressedPrimeAnchor_eq_anchorMass
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W)) :
    (∑ j : Band, B.compressedPrimeAnchor anchor j) =
      anchorMass (primeWeight B.sampleData.n) anchor := by
  classical
  unfold compressedPrimeAnchor anchorMass
  change (∑ j : Band,
      ∑ q ∈ Finset.univ.filter (fun q : BandPrime B.sampleData.n
        B.sampleData.W ↦ B.partition.band q = j),
        if q ∈ anchor then primeWeight B.sampleData.n q else 0) = _
  rw [Finset.sum_fiberwise Finset.univ B.partition.band
    (fun q : BandPrime B.sampleData.n B.sampleData.W ↦
      if q ∈ anchor then primeWeight B.sampleData.n q else 0)]
  simp
  rw [show (primeBand B.sampleData.n B.sampleData.W).attach =
      (Finset.univ : Finset
        (BandPrime B.sampleData.n B.sampleData.W)) by rfl,
    Finset.univ_inter]

/-- Every compressed prime-graph edge is nonnegative. -/
theorem compressedPrimeGraphEdge_nonneg (i j : Band) :
    0 ≤ B.compressedPrimeGraphEdge i j := by
  have hnorm : 0 ≤
      1 / (B.harmonicMass i * B.bandCenter i) :=
    (one_div_pos.mpr
      (mul_pos (B.harmonicMass_pos i) (B.bandCenter_pos i))).le
  unfold compressedPrimeGraphEdge
  apply mul_nonneg hnorm
  apply Finset.sum_nonneg
  intro p hp
  apply Finset.sum_nonneg
  intro q hq
  have hpcast : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hkernel : 0 ≤ -primeKernel B.sampleData.n p q := by
    exact neg_nonneg.mpr
      (covarianceKernel_nonpos
        (tPrime_mem_unit B.n_gt_one p)
        (tPrime_mem_unit B.n_gt_one q))
  exact mul_nonneg
    (mul_nonneg (one_div_nonneg.mpr hpcast.le)
      (primeWeight_pos B.n_gt_one q).le) hkernel

/-- The fixed continuum quotient gap gives an exact primewise edge gap
against every literal prime in the compact anchor block. -/
theorem canonicalSlowKappa_mul_tPrime_le_neg_primeKernel
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ q ∈ anchor,
      tPrime B.sampleData.n q.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (p : BandPrime B.sampleData.n B.sampleData.W)
    (q : BandPrime B.sampleData.n B.sampleData.W) (hq : q ∈ anchor) :
    canonicalSlowKappa * tPrime B.sampleData.n p.1 ≤
      -primeKernel B.sampleData.n p q := by
  have hgap := canonicalSlowKappa_gap
    (tPrime B.sampleData.n p.1) (tPrime_mem_unit B.n_gt_one p)
    (tPrime B.sampleData.n q.1) (hinterior q hq)
  have hmul := mul_covarianceKernelQuotient_eq_kernel
    (s := tPrime B.sampleData.n q.1)
    (t := tPrime B.sampleData.n p.1)
    (tPrime_mem_unit B.n_gt_one q)
    (tPrime_mem_unit B.n_gt_one p)
  unfold primeKernel
  rw [covarianceKernel_comm]
  nlinarith [B.bandPrime_tPrime_pos p]

/-- The compressed finite prime graph sees the compressed anchor with the
same fixed gap.  No mesh width or minimum band centre occurs. -/
theorem canonicalSlowKappa_mul_compressedPrimeAnchor_le_edge
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ q ∈ anchor,
      tPrime B.sampleData.n q.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    (i j : Band) :
    canonicalSlowKappa * B.compressedPrimeAnchor anchor j ≤
      B.compressedPrimeGraphEdge i j := by
  let A : ℝ := B.harmonicMass i * B.bandCenter i
  have hA : 0 < A := by
    exact mul_pos (B.harmonicMass_pos i) (B.bandCenter_pos i)
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W)
      (hp : p ∈ B.partition.data.fiber i) :
      canonicalSlowKappa * primeWeight B.sampleData.n p *
          B.compressedPrimeAnchor anchor j ≤
        ∑ q ∈ B.partition.data.fiber j,
          (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
            (-primeKernel B.sampleData.n p q) := by
    unfold compressedPrimeAnchor
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    by_cases hqa : q ∈ anchor
    · rw [if_pos hqa]
      have hgap := B.canonicalSlowKappa_mul_tPrime_le_neg_primeKernel
        anchor hinterior p q hqa
      have hfactor : 0 ≤
          (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q := by
        exact mul_nonneg (by positivity) (primeWeight_pos B.n_gt_one q).le
      have hscaled := mul_le_mul_of_nonneg_left hgap hfactor
      unfold primeWeight at hscaled ⊢
      ring_nf at hscaled ⊢
      exact hscaled
    · rw [if_neg hqa]
      have hkernel : 0 ≤ -primeKernel B.sampleData.n p q := by
        exact neg_nonneg.mpr
          (covarianceKernel_nonpos
            (tPrime_mem_unit B.n_gt_one p)
            (tPrime_mem_unit B.n_gt_one q))
      simp only [mul_zero]
      exact mul_nonneg
        (mul_nonneg (by positivity) (primeWeight_pos B.n_gt_one q).le)
        hkernel
  have hsum :
      canonicalSlowKappa * A * B.compressedPrimeAnchor anchor j ≤
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
              (-primeKernel B.sampleData.n p q) := by
    calc
      canonicalSlowKappa * A * B.compressedPrimeAnchor anchor j =
          ∑ p ∈ B.partition.data.fiber i,
            canonicalSlowKappa * primeWeight B.sampleData.n p *
              B.compressedPrimeAnchor anchor j := by
        rw [← Finset.sum_mul]
        rw [← Finset.mul_sum]
        rw [B.fiber_primeWeight_sum_eq_mass_mul_center]
      _ ≤ _ := Finset.sum_le_sum fun p hp ↦ hinner p hp
  unfold compressedPrimeGraphEdge
  calc
    canonicalSlowKappa * B.compressedPrimeAnchor anchor j =
        (1 / A) *
          (canonicalSlowKappa * A * B.compressedPrimeAnchor anchor j) := by
      field_simp [ne_of_gt hA]
    _ ≤ (1 / A) *
        (∑ p ∈ B.partition.data.fiber i,
          ∑ q ∈ B.partition.data.fiber j,
            (1 / (p.1 : ℝ)) * primeWeight B.sampleData.n q *
              (-primeKernel B.sampleData.n p q)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rfl

/-- A relative literal prime-row defect remains relative after sharp band
compression, including in the moving low band. -/
theorem abs_referenceResidualError_le
    {rowError R : ℝ} (hrowError : 0 ≤ rowError)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |B.referenceResidualError x i| ≤ rowError * R := by
  let A : ℝ := B.harmonicMass i * B.bandCenter i
  have hA : 0 < A :=
    mul_pos (B.harmonicMass_pos i) (B.bandCenter_pos i)
  have hterm (p : BandPrime B.sampleData.n B.sampleData.W) :
      |(1 / (p.1 : ℝ)) *
          rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p * x i| ≤
        (rowError * R) * primeWeight B.sampleData.n p := by
    have hp : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    have hinv : 0 ≤ 1 / (p.1 : ℝ) := one_div_nonneg.mpr hp.le
    have hfirst := mul_le_mul_of_nonneg_left (hrow p) hinv
    have hfirstUpperNonneg : 0 ≤
        (1 / (p.1 : ℝ)) *
          (rowError * tPrime B.sampleData.n p.1) :=
      mul_nonneg hinv
        (mul_nonneg hrowError (B.bandPrime_tPrime_pos p).le)
    have hscaled := mul_le_mul hfirst (hx i) (abs_nonneg _)
      hfirstUpperNonneg
    unfold primeWeight
    calc
      |(1 / (p.1 : ℝ)) *
          rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p * x i| =
        (1 / (p.1 : ℝ)) *
          |rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p| * |x i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hinv]
      _ ≤
        ((1 / (p.1 : ℝ)) *
          (rowError * tPrime B.sampleData.n p.1)) * R := hscaled
      _ = (rowError * R) *
          (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) := by ring
  unfold referenceResidualError
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hA)]
  calc
    (1 / A) *
        |∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i| ≤
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          |(1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p * x i| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (one_div_nonneg.mpr hA.le)
    _ ≤ (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          (rowError * R) * primeWeight B.sampleData.n p := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
      exact Finset.sum_le_sum fun p hp ↦ hterm p
    _ = rowError * R := by
      rw [← Finset.mul_sum, B.fiber_primeWeight_sum_eq_mass_mul_center]
      dsimp only [A]
      field_simp [ne_of_gt (B.harmonicMass_pos i),
        ne_of_gt (B.bandCenter_pos i)]

/-- Exact fiber centering keeps the diagonal replacement error relative in
the sharp norm. -/
theorem abs_referenceCenteringDiagonal_le
    {w CF R : ℝ} (hw : 0 ≤ w) (hCF : 0 ≤ CF) (hR : 0 ≤ R)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |B.referenceCenteringDiagonal x i| ≤ 2 * CF * w * R := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let A : ℝ := H * alpha
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have hA : 0 < A := mul_pos hH halpha
  have hcentered :
      (∑ p ∈ B.partition.data.fiber i,
        (F alpha / (p.1 : ℝ)) * B.primeDeviation p * x i) = 0 := by
    calc
      _ = (F alpha * x i) *
          ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) * B.primeDeviation p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ = 0 := by rw [B.primeDeviation_fiber_sum]; ring
  have hrewrite : B.referenceCenteringDiagonal x i =
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          ((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p * x i := by
    unfold referenceCenteringDiagonal
    change (1 / A) *
        (∑ p ∈ B.partition.data.fiber i,
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p * x i) = _
    rw [show (∑ p ∈ B.partition.data.fiber i,
        (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
          B.primeDeviation p * x i) =
      (∑ p ∈ B.partition.data.fiber i,
        ((F (tPrime B.sampleData.n p.1) - F alpha) /
            (p.1 : ℝ)) * B.primeDeviation p * x i) +
      ∑ p ∈ B.partition.data.fiber i,
        (F alpha / (p.1 : ℝ)) * B.primeDeviation p * x i by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      ring,
      hcentered, add_zero]
  have hterm (p : BandPrime B.sampleData.n B.sampleData.W)
      (hpFiber : p ∈ B.partition.data.fiber i) :
      |((F (tPrime B.sampleData.n p.1) - F alpha) /
          (p.1 : ℝ)) * B.primeDeviation p * x i| ≤
        (CF * w * R) *
          ((1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
    have hpBand : B.partition.band p = i :=
      (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
        B.partition.data).mp hpFiber
    have hpcast : (0 : ℝ) < p.1 := by
      exact_mod_cast (prime_of_mem_primeBand p.2).pos
    let d : ℝ := |B.primeDeviation p|
    have hd : 0 ≤ d := abs_nonneg _
    have hdw : d ≤ w := hdevSup p
    have hF : |F (tPrime B.sampleData.n p.1) - F alpha| ≤ CF * d := by
      simpa only [alpha, hpBand, d] using hFdiff p
    have hFd :
        |F (tPrime B.sampleData.n p.1) - F alpha| * d ≤
          (CF * d) * d := mul_le_mul_of_nonneg_right hF hd
    have hCFdw : CF * d ≤ CF * w :=
      mul_le_mul_of_nonneg_left hdw hCF
    have hquad :
        |F (tPrime B.sampleData.n p.1) - F alpha| * d ≤
          (CF * w) * d :=
      hFd.trans (mul_le_mul_of_nonneg_right hCFdw hd)
    have hinv : 0 ≤ 1 / (p.1 : ℝ) := one_div_nonneg.mpr hpcast.le
    have hcoef := mul_le_mul_of_nonneg_left hquad hinv
    have hcoefNonneg : 0 ≤ (1 / (p.1 : ℝ)) * ((CF * w) * d) :=
      mul_nonneg hinv (mul_nonneg (mul_nonneg hCF hw) hd)
    have hscaled := mul_le_mul hcoef (hx i) (abs_nonneg _) hcoefNonneg
    calc
      |((F (tPrime B.sampleData.n p.1) - F alpha) /
          (p.1 : ℝ)) * B.primeDeviation p * x i| =
        ((1 / (p.1 : ℝ)) *
          (|F (tPrime B.sampleData.n p.1) - F alpha| * d)) *
            |x i| := by
          dsimp only [d]
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hpcast]
          ring
      _ ≤ ((1 / (p.1 : ℝ)) * ((CF * w) * d)) * R := hscaled
      _ = (CF * w * R) * ((1 / (p.1 : ℝ)) * d) := by ring
  rw [hrewrite, abs_mul, abs_of_pos (one_div_pos.mpr hA)]
  calc
    (1 / A) *
        |∑ p ∈ B.partition.data.fiber i,
          ((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p * x i| ≤
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          |((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p * x i| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (one_div_nonneg.mpr hA.le)
    _ ≤ (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          (CF * w * R) *
            ((1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
      exact Finset.sum_le_sum fun p hp ↦ hterm p hp
    _ = (1 / A) * (CF * w * R) *
        (∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ (1 / A) * (CF * w * R) * (2 * H * alpha) := by
      exact mul_le_mul_of_nonneg_left
        (B.bandDeviationL1_le_two_mul_mass_mul_center i)
        (mul_nonneg (one_div_nonneg.mpr hA.le)
          (mul_nonneg (mul_nonneg hCF hw) hR))
    _ = 2 * CF * w * R := by
      dsimp only [A]
      field_simp [ne_of_gt hH, ne_of_gt halpha]

/-- The product bound for the Dickman kernel and the global arithmetic
deviation ledger give the remaining mesh-independent centering error. -/
theorem abs_referenceCenteringKernel_le
    {w CKernel R : ℝ} (hCKernel : 0 ≤ CKernel)
    (hR : 0 ≤ R)
    (hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |B.referenceCenteringKernel x i| ≤ 7 * CKernel * w * R := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let A : ℝ := H * alpha
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have hA : 0 < A := mul_pos hH halpha
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |B.primeDeviation q * x (B.partition.band q) *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))|) ≤
        (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
          (CKernel * R * B.primeDeviationL1) := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
            (CKernel * R *
              ((1 / (q.1 : ℝ)) * |B.primeDeviation q|)) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [abs_div,
          abs_of_pos (mul_pos (hpPos p) (hpPos q)), abs_mul, abs_mul]
        have hK := hKernelFirst p q
        have hxq := hx (B.partition.band q)
        have hdev : 0 ≤ |B.primeDeviation q| := abs_nonneg _
        have hKnonneg : 0 ≤
            |covarianceKernel
              (tPrime B.sampleData.n p.1)
              (tPrime B.sampleData.n q.1)| := abs_nonneg _
        have hdx :
            |B.primeDeviation q| * |x (B.partition.band q)| ≤
              |B.primeDeviation q| * R :=
          mul_le_mul_of_nonneg_left hxq hdev
        have hbaseNonneg : 0 ≤ |B.primeDeviation q| * R :=
          mul_nonneg hdev hR
        have hfirst := mul_le_mul hdx hK hKnonneg hbaseNonneg
        exact (div_le_div_of_nonneg_right hfirst
          (mul_pos (hpPos p) (hpPos q)).le).trans_eq (by ring)
      _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
          (CKernel * R * B.primeDeviationL1) := by
        unfold primeDeviationL1
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  unfold referenceCenteringKernel
  change |(1 / A) *
      (∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * x (B.partition.band q) *
            covarianceKernel
              (tPrime B.sampleData.n p.1)
              (tPrime B.sampleData.n q.1) /
                ((p.1 : ℝ) * (q.1 : ℝ)))| ≤ _
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hA)]
  calc
    (1 / A) *
        |∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))| ≤
      (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q * x (B.partition.band q) *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))| := by
        apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p hp ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (1 / A) *
        ∑ p ∈ B.partition.data.fiber i,
          (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
            (CKernel * R * B.primeDeviationL1) := by
      apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr hA.le)
      exact Finset.sum_le_sum fun p hp ↦ hinner p
    _ = CKernel * R * B.primeDeviationL1 := by
      rw [← Finset.sum_mul]
      rw [show (∑ p ∈ B.partition.data.fiber i,
          tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = A by
        simpa only [A] using B.fiber_primeWeight_sum_eq_mass_mul_center i]
      field_simp [ne_of_gt hA]
    _ ≤ CKernel * R * (7 * w) :=
      mul_le_mul_of_nonneg_left hdevL1 (mul_nonneg hCKernel hR)
    _ = 7 * CKernel * w * R := by ring

/-- The literal reference sharp row is uniformly close, in the sharp row
normalization, to the compressed prime graph.  Crucially, the right-hand
side contains no inverse power of the moving low-band center. -/
theorem abs_referenceSharpRow_sub_primeGraph_le
    {rowError w CF CKernel R : ℝ}
    (hrowError : 0 ≤ rowError) (hw : 0 ≤ w)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel) (hR : 0 ≤ R)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (x : Band → ℝ) (hx : ∀ j, |x j| ≤ R) (i : Band) :
    |referenceSharpRow B.partition x i -
        graphOperator B.compressedPrimeGraphEdge x i| ≤
      (rowError + (2 * CF + 7 * CKernel) * w) * R := by
  have hres := B.abs_referenceResidualError_le
    hrowError hrow x hx i
  have hdiag := B.abs_referenceCenteringDiagonal_le
    hw hCF hR hFdiff hdevSup x hx i
  have hkernel := B.abs_referenceCenteringKernel_le
    hCKernel hR hKernelFirst hdevL1 x hx i
  rw [B.referenceSharpRow_eq_primeGraph_add_errors]
  calc
    |graphOperator B.compressedPrimeGraphEdge x i +
          B.referenceResidualError x i +
          B.referenceCenteringDiagonal x i +
          B.referenceCenteringKernel x i -
        graphOperator B.compressedPrimeGraphEdge x i| =
        |B.referenceResidualError x i +
          B.referenceCenteringDiagonal x i +
          B.referenceCenteringKernel x i| := by
            congr 1
            ring
    _ ≤ |B.referenceResidualError x i| +
          |B.referenceCenteringDiagonal x i| +
          |B.referenceCenteringKernel x i| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ rowError * R + 2 * CF * w * R + 7 * CKernel * w * R :=
      add_le_add (add_le_add hres hdiag) hkernel
    _ = (rowError + (2 * CF + 7 * CKernel) * w) * R := by ring

/-- Stable inversion of the literal arithmetic reference sharp operator by
the compressed prime graph.  The error and inverse constants depend only on
the prime-row residual and the two structural continuum constants; neither
the number of bands nor the least arithmetic centre occurs. -/
theorem exists_referenceSharpProjectedEquiv_of_primeGraph
    (cert : PositiveCellTransfer.IntervalCertificate B.partition)
    (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W))
    (hinterior : ∀ q ∈ anchor,
      tPrime B.sampleData.n q.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8))
    {rowError w CF CKernel : ℝ}
    (hrowError : 0 ≤ rowError) (hw : 0 ≤ w)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (hanchorMass : 0 <
      anchorMass (primeWeight B.sampleData.n) anchor)
    (hsmall :
      (4 / (canonicalSlowKappa *
          anchorMass (primeWeight B.sampleData.n) anchor)) *
        (2 * (rowError + (2 * CF + 7 * CKernel) * w)) < 1) :
    ∃ referenceEquiv :
        PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center ≃L[ℝ]
          PaperWeightedInverseExport.SharpGaugeSpace
            B.partition.mass B.partition.center,
      (∀ q, referenceEquiv q =
        ArithmeticGaugeStableInverse.projectedSharpCLM
          (CompressedArithmeticOperator.arithmeticDiagonal
            (y B.sampleData.n) cert.lower cert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (y B.sampleData.n) cert.lower cert.upper)
          B.partition.center
          (MovingLowGaugeTransfer.sharpWeight
            B.partition.mass B.partition.center)
          (ne_of_gt B.actualSharpWeightTotal_pos) q) ∧
      ∀ v, ‖referenceEquiv.symm v‖ ≤
        ((4 / (canonicalSlowKappa *
            anchorMass (primeWeight B.sampleData.n) anchor)) /
          (1 - (4 / (canonicalSlowKappa *
              anchorMass (primeWeight B.sampleData.n) anchor)) *
            (2 * (rowError + (2 * CF + 7 * CKernel) * w)))) * ‖v‖ := by
  letI : Nonempty Band := ⟨B.lowBand⟩
  let omega : Band → ℝ := MovingLowGaugeTransfer.sharpWeight
    B.partition.mass B.partition.center
  let err : ℝ := rowError + (2 * CF + 7 * CKernel) * w
  let delta : ℝ := 2 * err
  let actual : FiniteGraphStableInverse.GaugeSpace omega →L[ℝ]
      FiniteGraphStableInverse.GaugeSpace omega :=
    ArithmeticGaugeStableInverse.projectedSharpCLM
      (CompressedArithmeticOperator.arithmeticDiagonal
        (y B.sampleData.n) cert.lower cert.upper)
      (CompressedArithmeticOperator.arithmeticKernel
        (y B.sampleData.n) cert.lower cert.upper)
      B.partition.center omega (ne_of_gt B.actualSharpWeightTotal_pos)
  have homega : ∀ i, 0 ≤ omega i := fun i ↦
    MovingLowGaugeTransfer.sharpWeight_nonneg_of_mass_nonneg
      B.partition.mass B.partition.center
      (fun j ↦ (B.partition.data.mass_pos j).le) i
  have homegaTotal : 0 < ∑ i, omega i := by
    simpa only [omega, MovingLowGaugeTransfer.sharpWeightTotal] using
      B.actualSharpWeightTotal_pos
  have hedge : ∀ i j, 0 ≤ B.compressedPrimeGraphEdge i j :=
    B.compressedPrimeGraphEdge_nonneg
  have hdom : ∀ i j,
      canonicalSlowKappa * B.compressedPrimeAnchor anchor j ≤
        B.compressedPrimeGraphEdge i j :=
    B.canonicalSlowKappa_mul_compressedPrimeAnchor_le_edge anchor hinterior
  have hanchorTotal :
      0 < ∑ j, B.compressedPrimeAnchor anchor j := by
    rw [B.sum_compressedPrimeAnchor_eq_anchorMass]
    exact hanchorMass
  have herrNonneg : 0 ≤ err := by
    dsimp only [err]
    positivity
  have hdeltaNonneg : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hstableSmall :
      (4 / (canonicalSlowKappa *
          ∑ j, B.compressedPrimeAnchor anchor j)) * delta < 1 := by
    simpa only [delta, err, B.sum_compressedPrimeAnchor_eq_anchorMass]
      using hsmall
  have herror : ∀ q,
      ‖(actual - FiniteGraphStableInverse.referenceGraphCLM
        B.compressedPrimeGraphEdge (B.compressedPrimeAnchor anchor) omega
        hedge hdom canonicalSlowKappa_pos hanchorTotal homega
          homegaTotal) q‖ ≤ delta * ‖q‖ := by
    intro q
    have hraw (i : Band) :
        |CompressedArithmeticOperator.arithmeticSharpOperator
              (y B.sampleData.n) cert.lower cert.upper
              B.partition.center (q : Band → ℝ) i -
            graphOperator B.compressedPrimeGraphEdge
              (q : Band → ℝ) i| ≤ err * ‖q‖ := by
      have href := B.abs_referenceSharpRow_sub_primeGraph_le
        hrowError hw hCF hCKernel (norm_nonneg q) hrow hFdiff
        hKernelFirst hdevSup hdevL1 (q : Band → ℝ)
        (fun j ↦ by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm (q : Band → ℝ) j) i
      rw [referenceSharpRow_eq_arithmeticSharpOperator cert
        (q : Band → ℝ) i
        (ne_of_gt (B.partition.center_pos B.n_gt_one i))] at href
      simpa only [err] using href
    have hprojected (i : Band) :
        |meanProjection omega
              (fun j ↦ CompressedArithmeticOperator.arithmeticSharpOperator
                (y B.sampleData.n) cert.lower cert.upper
                B.partition.center (q : Band → ℝ) j) i -
            meanProjection omega
              (graphOperator B.compressedPrimeGraphEdge
                (q : Band → ℝ)) i| ≤
          2 * (err * ‖q‖) :=
      CompressedArithmeticOperator.abs_meanProjection_sub_le omega
        (fun j ↦ CompressedArithmeticOperator.arithmeticSharpOperator
          (y B.sampleData.n) cert.lower cert.upper
          B.partition.center (q : Band → ℝ) j)
        (graphOperator B.compressedPrimeGraphEdge (q : Band → ℝ))
        (err * ‖q‖) homega homegaTotal hraw i
    have hnonneg : 0 ≤ delta * ‖q‖ :=
      mul_nonneg hdeltaNonneg (norm_nonneg q)
    change ‖(((actual - FiniteGraphStableInverse.referenceGraphCLM
        B.compressedPrimeGraphEdge (B.compressedPrimeAnchor anchor) omega
        hedge hdom canonicalSlowKappa_pos hanchorTotal homega
          homegaTotal) q :
        FiniteGraphStableInverse.GaugeSpace omega) : Band → ℝ)‖ ≤
      delta * ‖q‖
    rw [pi_norm_le_iff_of_nonneg hnonneg]
    intro i
    rw [Real.norm_eq_abs]
    change |meanProjection omega
          (fun j ↦ CompressedArithmeticOperator.arithmeticSharpOperator
            (y B.sampleData.n) cert.lower cert.upper
            B.partition.center (q : Band → ℝ) j) i -
        meanProjection omega
          (graphOperator B.compressedPrimeGraphEdge
            (q : Band → ℝ)) i| ≤ delta * ‖q‖
    exact (hprojected i).trans_eq (by simp only [delta]; ring)
  obtain ⟨referenceEquiv, hreference, hinv⟩ :=
    FiniteGraphStableInverse.exists_actualGaugeEquiv_of_graph_error
      B.compressedPrimeGraphEdge (B.compressedPrimeAnchor anchor) omega
      hedge hdom canonicalSlowKappa_pos hanchorTotal homega homegaTotal
      actual hstableSmall herror
  refine ⟨referenceEquiv, ?_, ?_⟩
  · intro q
    simpa only [actual, omega] using hreference q
  · intro v
    simpa only [delta, err, B.sum_compressedPrimeAnchor_eq_anchorMass]
      using hinv v

/-- Structural version of the prime-graph inverse.  The row tolerance,
mesh tolerance, and final inverse constant are selected before the
arithmetic partition.  The only later hypotheses are literal finite row,
deviation, and anchor estimates. -/
theorem exists_structural_referenceSharpProjected_inverse_constants :
    ∃ rowTarget : ℝ, 0 < rowTarget ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cref : ℝ, 0 < Cref ∧
      ∀ (cert : PositiveCellTransfer.IntervalCertificate B.partition)
        (anchor : Finset (BandPrime B.sampleData.n B.sampleData.W)),
        (∀ q ∈ anchor,
          tPrime B.sampleData.n q.1 ∈
            Set.Icc (1 / 8 : ℝ) (1 - 1 / 8)) →
        (1 / 8 : ℝ) ≤
          anchorMass (primeWeight B.sampleData.n) anchor →
        (∀ p : BandPrime B.sampleData.n B.sampleData.W,
          |rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p| ≤
            rowTarget * tPrime B.sampleData.n p.1) →
        (∀ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation p| ≤ meshTol) →
        B.primeDeviationL1 ≤ 7 * meshTol →
        ∃ referenceEquiv :
            PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center ≃L[ℝ]
              PaperWeightedInverseExport.SharpGaugeSpace
                B.partition.mass B.partition.center,
          (∀ q, referenceEquiv q =
            ArithmeticGaugeStableInverse.projectedSharpCLM
              (CompressedArithmeticOperator.arithmeticDiagonal
                (y B.sampleData.n) cert.lower cert.upper)
              (CompressedArithmeticOperator.arithmeticKernel
                (y B.sampleData.n) cert.lower cert.upper)
              B.partition.center
              (MovingLowGaugeTransfer.sharpWeight
                B.partition.mass B.partition.center)
              (ne_of_gt B.actualSharpWeightTotal_pos) q) ∧
          ∀ v, ‖referenceEquiv.symm v‖ ≤ Cref * ‖v‖ := by
  obtain ⟨CF, hCF, hF⟩ :=
    PaperActualSlowRightRowFinite.exists_F_lipschitz_unit
  obtain ⟨CKernel, hCKernel, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_first
  let kappa : ℝ := canonicalSlowKappa
  let anchorFloor : ℝ := 1 / 8
  let A : ℝ := 2 * CF + 7 * CKernel
  let radius : ℝ := kappa * anchorFloor / 16
  let meshTol : ℝ := radius / (2 * (A + 1))
  let rowTarget : ℝ := radius - A * meshTol
  let Cref : ℝ := 8 / (kappa * anchorFloor)
  have hkappa : 0 < kappa := by
    simpa only [kappa] using canonicalSlowKappa_pos
  have hfloor : 0 < anchorFloor := by
    dsimp only [anchorFloor]
    norm_num
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hAone : 0 < A + 1 := by linarith
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    positivity
  have hmeshIdentity : meshTol * (2 * (A + 1)) = radius := by
    dsimp only [meshTol]
    field_simp [ne_of_gt hAone]
  have hAmLt : A * meshTol < radius := by
    nlinarith [mul_nonneg hA hmeshTol.le]
  have hrowTarget : 0 < rowTarget := by
    dsimp only [rowTarget]
    linarith
  have hCref : 0 < Cref := by
    dsimp only [Cref]
    positivity
  refine ⟨rowTarget, hrowTarget, meshTol, hmeshTol,
    Cref, hCref, ?_⟩
  intro cert anchor hinterior hmassFloor hrow hdevSup hdevL1
  let mass : ℝ := anchorMass (primeWeight B.sampleData.n) anchor
  let base : ℝ := 4 / (kappa * mass)
  let loss : ℝ := base * (2 * radius)
  have hmassFloor' : anchorFloor ≤ mass := by
    simpa only [anchorFloor, mass] using hmassFloor
  have hmass : 0 < mass := by
    exact hfloor.trans_le hmassFloor'
  have hkMass : 0 < kappa * mass := mul_pos hkappa hmass
  have hkFloor : 0 < kappa * anchorFloor := mul_pos hkappa hfloor
  have hlossId : loss = anchorFloor / (2 * mass) := by
    dsimp only [loss, base, radius]
    field_simp [ne_of_gt hkappa, ne_of_gt hmass]
    ring
  have hlossLe : loss ≤ 1 / 2 := by
    rw [hlossId]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmass)).2
    dsimp only [mass, anchorFloor] at hmassFloor ⊢
    nlinarith
  have hsmallLoss : loss < 1 := hlossLe.trans_lt (by norm_num)
  have hbasePos : 0 < base := by
    dsimp only [base]
    exact div_pos (by norm_num) hkMass
  have hdenHalf : 1 / 2 ≤ 1 - loss := by linarith
  have hbaseBound : base ≤ 4 / (kappa * anchorFloor) := by
    dsimp only [base]
    apply (div_le_div_iff₀ hkMass hkFloor).2
    have hkorder := mul_le_mul_of_nonneg_left hmassFloor' hkappa.le
    nlinarith
  have hconstantBound : base / (1 - loss) ≤ Cref := by
    calc
      base / (1 - loss) ≤ base / (1 / 2) :=
        div_le_div_of_nonneg_left hbasePos.le (by norm_num) hdenHalf
      _ = 2 * base := by ring
      _ ≤ 2 * (4 / (kappa * anchorFloor)) :=
        mul_le_mul_of_nonneg_left hbaseBound (by norm_num)
      _ = Cref := by
        dsimp only [Cref]
        ring
  have hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p| := by
    intro p
    simpa only [bandCenter, primeDeviation, abs_sub_comm] using
      hF _ (tPrime_mem_unit B.n_gt_one p) _
        (B.partition.center_mem_zero_one B.n_gt_one
          (B.partition.band p))
  have hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 := by
    intro p q
    exact hKernel _ (tPrime_mem_unit B.n_gt_one p) _
      (tPrime_mem_unit B.n_gt_one q)
  have herrorIdentity :
      rowTarget + (2 * CF + 7 * CKernel) * meshTol = radius := by
    dsimp only [rowTarget, A]
    ring
  have hsmall :
      (4 / (canonicalSlowKappa *
          anchorMass (primeWeight B.sampleData.n) anchor)) *
        (2 * (rowTarget + (2 * CF + 7 * CKernel) * meshTol)) < 1 := by
    simpa only [kappa, mass, base, loss, herrorIdentity] using hsmallLoss
  obtain ⟨referenceEquiv, hreference, hinv⟩ :=
    B.exists_referenceSharpProjectedEquiv_of_primeGraph cert anchor
      hinterior hrowTarget.le hmeshTol.le hCF.le hCKernel
      hrow hFdiff hKernelFirst hdevSup hdevL1
      (hfloor.trans_le hmassFloor) hsmall
  refine ⟨referenceEquiv, hreference, ?_⟩
  intro v
  exact (hinv v).trans
    (mul_le_mul_of_nonneg_right (by
      simpa only [kappa, mass, base, loss, herrorIdentity] using
        hconstantBound) (norm_nonneg v))

end BridgeData
end
end Erdos390.Full.PaperBridgeFit
