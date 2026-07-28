import Erdos390.Full.SquarefreeSharpBandTransfer
import Erdos390.Full.CompressedArithmeticOperator
import Erdos390.Full.PositiveCellTransfer

/-!
# Exact identification of the signed squarefree reference operator

The signed reference covariance used in the arithmetic part of paper
Lemma 8.4 is defined prime by prime in
`SquarefreeCovarianceReference`.  The moving-low inverse, on the other
hand, is proved for the endpoint matrix called `arithmeticDiagonal` plus
`arithmeticKernel`.  This file proves that these are literally the same
finite operator for every certified prime partition.  No limit, row bound,
covariance estimate, or inverse is assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.SquarefreeReferenceOperatorIdentification

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PositiveCellTransfer
open DoubleKernelPrimeQuadrature DiagonalPrimeQuadrature
open CompressedArithmeticOperator
open ConditionedPoissonLimit DickmanBasic

variable {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {P : Partition n W Band}

/-- A certified band fiber and its natural-number prime cell have identical
weighted sums.  This is the reusable bijection behind both the diagonal and
the two-index identifications below. -/
theorem sum_fiber_eq_sum_cell
    (E : IntervalCertificate P) (j : Band) (f : ℕ → ℝ) :
    (∑ p ∈ P.data.fiber j, f p.1) =
      ∑ q ∈ E.cellPrimes j, f q := by
  apply Finset.sum_bij (fun p _hp ↦ p.1)
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
        ⟨hqData.1, (E.cutoff_le_lower j).trans_lt hqData.2.1,
          hqData.2.2.trans (E.upper_le_yNat j)⟩
    let p : BandPrime n W := ⟨q, hqBand⟩
    have hpFiber : p ∈ P.data.fiber j := by
      simp only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
      exact (E.band_eq_iff p j).mpr hqData.2
    exact ⟨p, hpFiber, rfl⟩
  · intro p hp
    rfl

/-- The diagonal `F(t_p)/p` part of the signed reference is exactly the
prime-cell diagonal numerator used in the canonical arithmetic matrix. -/
theorem diagonal_fiber_sum_eq_diagonalPrimeCell
    (E : IntervalCertificate P) (i : Band) :
    (∑ p ∈ P.data.fiber i,
        F (tPrime n p.1) / (p.1 : ℝ)) =
      diagonalPrimeCell (y n) (E.lower i) (E.upper i) := by
  rw [diagonalPrimeCell,
    primeCellOperator_eq_sum (y n) (E.lower_le_upper i)]
  rw [sum_fiber_eq_sum_cell E i
    (fun p ↦ F (tPrime n p) / (p : ℝ))]
  apply Finset.sum_congr
  · rfl
  · intro p hp
    unfold tPrime KernelPrimeQuadrature.realLogCoordinate
    rfl

/-- On two certified fibers the signed kernel entries sum to the exact
double-prime kernel cell. -/
theorem kernel_fiber_sum_eq_doublePrimeKernelCell
    (E : IntervalCertificate P) (i j : Band) :
    (∑ p ∈ P.data.fiber i,
        ∑ q ∈ P.data.fiber j,
          squarefreeKernelEntry n p.1 q.1) =
      doublePrimeKernelCell (y n)
        (E.lower i) (E.upper i) (E.lower j) (E.upper j) := by
  rw [doublePrimeKernelCell,
    primeCellOperator_eq_sum (y n) (E.lower_le_upper i)]
  rw [sum_fiber_eq_sum_cell E i (fun p ↦
    ∑ q ∈ P.data.fiber j, squarefreeKernelEntry n p q.1)]
  apply Finset.sum_congr
  · rfl
  · intro p hp
    rw [primeCellOperator_eq_sum (y n) (E.lower_le_upper j)]
    rw [sum_fiber_eq_sum_cell E j
      (fun q ↦ squarefreeKernelEntry n p q)]
    rw [show E.cellPrimes j =
        intervalPrimes (E.lower j) (E.upper j) by rfl]
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr
    · rfl
    · intro q hq
      unfold squarefreeKernelEntry tPrime
        KernelPrimeQuadrature.realLogCoordinate
      ring

/-- The reference entry is the kernel entry plus a Kronecker diagonal
multiplier. -/
theorem squarefreeReferenceEntry_eq_kernel_add_diagonal
    (p q : ℕ) :
    squarefreeReferenceEntry n p q =
      squarefreeKernelEntry n p q +
        if p = q then F (tPrime n p) / (p : ℝ) else 0 := by
  by_cases hpq : p = q
  · subst q
    simp [squarefreeReferenceEntry]
    ring
  · simp [squarefreeReferenceEntry, hpq]

/-- The normalized reference block entry is exactly the canonical arithmetic
kernel entry, with the diagonal multiplier added when the two bands agree. -/
theorem reference_block_eq_arithmetic
    (E : IntervalCertificate P) (i j : Band) :
    (1 / P.mass i) *
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            squarefreeReferenceEntry n p.1 q.1) =
      arithmeticKernel (y n) E.lower E.upper i j +
        if i = j then arithmeticDiagonal (y n) E.lower E.upper i else 0 := by
  have hmass : P.mass i ≠ 0 := ne_of_gt (P.data.mass_pos i)
  have hmassCell :
      DoubleKernelPrimeQuadrature.actualCellMass (E.lower i) (E.upper i) =
        P.mass i := by
    unfold DoubleKernelPrimeQuadrature.actualCellMass
    exact (E.mass_eq_fullReciprocalSum_sub i).symm
  have hkernel :
      (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeKernelEntry n p.1 q.1) =
        arithmeticKernel (y n) E.lower E.upper i j := by
    rw [kernel_fiber_sum_eq_doublePrimeKernelCell E i j]
    unfold arithmeticKernel normalizedDoublePrimeKernelCell
    rw [hmassCell]
    ring
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    have hdiagInner (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
        (∑ q ∈ P.data.fiber i,
          if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) =
          F (tPrime n p.1) / (p.1 : ℝ) := by
      calc
        (∑ q ∈ P.data.fiber i,
          if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) =
            ∑ q ∈ P.data.fiber i,
              if q = p then F (tPrime n p.1) / (p.1 : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro q hq
                by_cases hqp : q = p
                · subst q; simp
                · have hv : q.1 ≠ p.1 := by
                    intro hv
                    exact hqp (Subtype.ext hv)
                  simp [hqp, Ne.symm hv]
        _ = F (tPrime n p.1) / (p.1 : ℝ) := by
          simp [hp]
    have hsplit :
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber i,
            squarefreeReferenceEntry n p.1 q.1) =
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber i,
              squarefreeKernelEntry n p.1 q.1) +
          ∑ p ∈ P.data.fiber i,
            F (tPrime n p.1) / (p.1 : ℝ) := by
      simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal,
        Finset.sum_add_distrib]
      apply congrArg₂ (fun x y : ℝ ↦ x + y) rfl
      apply Finset.sum_congr rfl
      intro p hp
      exact hdiagInner p hp
    rw [hsplit, mul_add, hkernel,
      diagonal_fiber_sum_eq_diagonalPrimeCell E i]
    unfold arithmeticDiagonal normalizedDiagonalPrimeCell
    rw [hmassCell]
    ring
  · rw [if_neg hij]
    have hdiagZero (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
        (∑ q ∈ P.data.fiber j,
          if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hpi : P.band p = i := by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
      have hqj : P.band q = j := by
        simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hq
      have hpq : p.1 ≠ q.1 := by
        intro hpq
        have hpqSub : p = q := Subtype.ext hpq
        subst q
        exact hij (hpi.symm.trans hqj)
      simp [hpq]
    have hsplit :
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            squarefreeReferenceEntry n p.1 q.1) =
          ∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeKernelEntry n p.1 q.1 := by
      simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal,
        Finset.sum_add_distrib]
      rw [show (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            if p.1 = q.1 then F (tPrime n p.1) / (p.1 : ℝ) else 0) = 0 by
        apply Finset.sum_eq_zero
        intro p hp
        exact hdiagZero p hp]
      ring
    rw [hsplit, hkernel]
    ring

/-- Exact row-level identification. -/
theorem referenceBandRow_eq_rawOperator
    (E : IntervalCertificate P) (b : Band → ℝ) (i : Band) :
    referenceBandRow P b i =
      PaperWeightedInverseExport.rawOperator
        (arithmeticDiagonal (y n) E.lower E.upper)
        (arithmeticKernel (y n) E.lower E.upper) b i := by
  unfold referenceBandRow
  rw [show (∑ p ∈ P.data.fiber i,
      ∑ q : BandPrime n W,
        b (P.band q) * squarefreeReferenceEntry n p.1 q.1) =
      ∑ j : Band, b j *
        (∑ p ∈ P.data.fiber i,
          ∑ q ∈ P.data.fiber j,
            squarefreeReferenceEntry n p.1 q.1) by
    calc
      (∑ p ∈ P.data.fiber i,
          ∑ q : BandPrime n W,
            b (P.band q) * squarefreeReferenceEntry n p.1 q.1) =
        ∑ q : BandPrime n W,
          b (P.band q) *
            (∑ p ∈ P.data.fiber i,
              squarefreeReferenceEntry n p.1 q.1) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
      _ = ∑ j : Band,
          ∑ q ∈ P.data.fiber j,
            b (P.band q) *
              (∑ p ∈ P.data.fiber i,
                squarefreeReferenceEntry n p.1 q.1) := by
          rw [← Finset.sum_fiberwise Finset.univ P.band
            (fun q : BandPrime n W ↦
              b (P.band q) *
                (∑ p ∈ P.data.fiber i,
                  squarefreeReferenceEntry n p.1 q.1))]
          rfl
      _ = ∑ j : Band, b j *
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeReferenceEntry n p.1 q.1) := by
          apply Finset.sum_congr rfl
          intro j hj
          calc
            (∑ q ∈ P.data.fiber j,
                b (P.band q) *
                  (∑ p ∈ P.data.fiber i,
                    squarefreeReferenceEntry n p.1 q.1)) =
              ∑ q ∈ P.data.fiber j,
                b j *
                  (∑ p ∈ P.data.fiber i,
                    squarefreeReferenceEntry n p.1 q.1) := by
                apply Finset.sum_congr rfl
                intro q hq
                have hqj : P.band q = j := by
                  simpa only
                    [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
                    using hq
                rw [hqj]
            _ = b j *
                (∑ q ∈ P.data.fiber j,
                  ∑ p ∈ P.data.fiber i,
                    squarefreeReferenceEntry n p.1 q.1) := by
                rw [Finset.mul_sum]
            _ = b j *
                (∑ p ∈ P.data.fiber i,
                  ∑ q ∈ P.data.fiber j,
                    squarefreeReferenceEntry n p.1 q.1) := by
                rw [Finset.sum_comm]]
  unfold PaperWeightedInverseExport.rawOperator
  have hmass : P.mass i ≠ 0 := ne_of_gt (P.data.mass_pos i)
  rw [Finset.mul_sum]
  have hblocks (j : Band) := reference_block_eq_arithmetic E i j
  calc
    ∑ j : Band, (1 / P.mass i) *
        (b j *
          (∑ p ∈ P.data.fiber i,
            ∑ q ∈ P.data.fiber j,
              squarefreeReferenceEntry n p.1 q.1)) =
      ∑ j : Band, b j *
        (arithmeticKernel (y n) E.lower E.upper i j +
          if i = j then arithmeticDiagonal (y n) E.lower E.upper i else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show (1 / P.mass i) *
          (b j *
            (∑ p ∈ P.data.fiber i,
              ∑ q ∈ P.data.fiber j,
                squarefreeReferenceEntry n p.1 q.1)) =
          b j * ((1 / P.mass i) *
            (∑ p ∈ P.data.fiber i,
              ∑ q ∈ P.data.fiber j,
                squarefreeReferenceEntry n p.1 q.1)) by ring,
        hblocks]
    _ = arithmeticDiagonal (y n) E.lower E.upper i * b i +
        ∑ j : Band, arithmeticKernel (y n) E.lower E.upper i j * b j := by
      rw [show (∑ j : Band, b j *
          (arithmeticKernel (y n) E.lower E.upper i j +
            if i = j then arithmeticDiagonal (y n) E.lower E.upper i else 0)) =
        (∑ j : Band, arithmeticKernel (y n) E.lower E.upper i j * b j) +
          ∑ j : Band,
            if j = i then arithmeticDiagonal (y n) E.lower E.upper i * b j
            else 0 by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hji : j = i
              · subst j; simp; ring
              · have hij : i ≠ j := Ne.symm hji
                simp [hji, hij]
                ring]
      rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ i)]
      ring

/-- After the exact centre conjugation, the reference sharp row is exactly
the canonical arithmetic sharp operator used by the inverse theorem. -/
theorem referenceSharpRow_eq_arithmeticSharpOperator
    (E : IntervalCertificate P) (q : Band → ℝ) (i : Band)
    (hcenter : P.center i ≠ 0) :
    referenceSharpRow P q i =
      arithmeticSharpOperator (y n) E.lower E.upper P.center q i := by
  unfold referenceSharpRow arithmeticSharpOperator
  rw [referenceBandRow_eq_rawOperator E]
  unfold PaperWeightedInverseExport.rawOperator sharpOperator
  apply (div_eq_iff hcenter).2
  simp only
  rw [add_mul, Finset.sum_mul]
  apply congrArg₂ (fun x y : ℝ ↦ x + y)
  · ring
  · apply Finset.sum_congr rfl
    intro j hj
    field_simp [hcenter]

section MarkedProfileApplication

variable {Cell : Type*} [Fintype Cell]
variable {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
variable {M : ℕ}

/-- The common marked one- and two-divisor profiles, including the exact
between-cell covariance of the reweighted sigma mixture, feed directly into
the canonical arithmetic sharp operator.  This theorem is the assumption-free
connector between the signed probability comparison and the deterministic
moving-low inverse: its hypotheses are precisely the local marked-profile
estimates, not an operator comparison or inverse bound. -/
theorem abs_sigmaMixture_squarefreeSharpRow_sub_arithmeticSharpOperator_le
    (cert : IntervalCertificate P)
    {Eprofile CKernel : ℝ} (hEprofile : 0 ≤ Eprofile)
    (weight : FiniteProbability Cell)
    (law : ∀ c, PrimePowerCovariance.BoundedValuationLaw (Omega c) M)
    (hn : 1 < n) (hW : 1 < W)
    (hpair : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p →
      |(law c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p q 1 1)
            ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (OmittedTiltPairChamber.pairPower p q 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p q 1 1)
    (hsingle : ∀ c p, p ∈ primeBand n W →
      |(law c).probability.expect
          (fun omega ↦ divInd p ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hKernel : ∀ p ∈ primeBand n W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime n p) (tPrime n p)| ≤ CKernel)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    let mix := PrimePowerCovariance.BoundedValuationLaw.sigmaMixture weight law
    |squarefreeSharpRow mix P q i -
        arithmeticSharpOperator (y n) cert.lower cert.upper P.center q i| ≤
      (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          PrimeSums.bandTReciprocalSum n W / P.center i +
        2 * Eprofile +
        ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
            CKernel) * (1 / (W : ℝ)) := by
  dsimp only
  let mix := PrimePowerCovariance.BoundedValuationLaw.sigmaMixture weight law
  have hentry :=
    SquarefreeCovarianceReference.sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight law hn hpair hsingle hKernel
  have hCKernel : 0 ≤ CKernel := by
    obtain ⟨p, hpband⟩ := P.fiber_nonempty i
    exact (abs_nonneg
      (ConditionedPoissonLimit.covarianceKernel
        (tPrime n p.1) (tPrime n p.1))).trans
          (hKernel p.1 p.2)
  have hCdiag :
      0 ≤ (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
        CKernel := add_nonneg (sq_nonneg _) hCKernel
  have hsharp :=
    SquarefreeSharpBandTransfer.abs_squarefreeSharpRow_sub_referenceSharpRow_le
      mix P hn hW hCdiag hentry q hq i
  rw [referenceSharpRow_eq_arithmeticSharpOperator cert q i
    (ne_of_gt (P.center_pos hn i))] at hsharp
  simpa only [mix, mul_assoc] using hsharp

end MarkedProfileApplication

end Erdos390.Full.SquarefreeReferenceOperatorIdentification
