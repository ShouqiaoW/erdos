import Erdos390.Full.CanonicalEndpointMultiAnchorCoverage
import Erdos390.Full.CanonicalEndpointRelativeCenterEventually
import Erdos390.Full.PrimeSquarefreeDirichletGeometry
import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# Literal prime anchors for a fixed regular-mesh block

The continuum anchor used by the transferred inverse is not, by itself, the
prime anchor required by the finite Dirichlet argument.  This file constructs
the latter as the union of the literal prime fibers belonging to the selected
positive cells.  It proves both facts needed later:

* every selected prime stays in the prescribed compact subinterval of
  logarithmic coordinates; and
* its `t_p / p` mass is bounded below uniformly in the mesh, provided the
  selected ideal cells have a fixed total-width floor.

The mass comparison is an unconditional two-endpoint PNT estimate.  In
particular, no arithmetic centre is identified with a continuum centre.
-/

open Filter Set
open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer MovingLowMomentQuadrature
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The literal primes whose canonical band belongs to the selected positive
anchor block. -/
def canonicalPrimeAnchorSet {n W : ℕ}
    (P : Partition n W (Fin (M.cellCount + 1)))
    (anchors : Finset (Fin M.cellCount)) :
    Finset (BandPrime n W) :=
  Finset.univ.filter (fun p ↦
    P.band p ∈ anchors.map (positiveBandEmbedding M))

theorem mem_canonicalPrimeAnchorSet_iff
    {n W : ℕ} {P : Partition n W (Fin (M.cellCount + 1))}
    {anchors : Finset (Fin M.cellCount)} {p : BandPrime n W} :
    p ∈ canonicalPrimeAnchorSet M P anchors ↔
      ∃ k ∈ anchors, P.band p = positiveBand M k := by
  classical
  simp only [canonicalPrimeAnchorSet, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_map]
  constructor
  · rintro ⟨k, hk, hkp⟩
    exact ⟨k, hk, hkp.symm⟩
  · rintro ⟨k, hk, hpk⟩
    exact ⟨k, hk, hpk.symm⟩

/-- The `t_p/p` mass of one literal fiber is exactly `H_j alpha_j`.
This is finite arithmetic centering, with no limiting object involved. -/
theorem sum_primeWeight_fiber_eq_mass_mul_center
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (j : Fin (M.cellCount + 1)) :
    (∑ p ∈ P.data.fiber j, primeWeight n p) =
      P.mass j * P.center j := by
  have hrewrite : (∑ p ∈ P.data.fiber j, primeWeight n p) =
      ∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1 := by
    apply Finset.sum_congr rfl
    intro p hp
    unfold primeWeight
    ring
  rw [hrewrite]
  change (∑ p ∈ P.data.fiber j,
      (1 / (p.1 : ℝ)) * tPrime n p.1) =
    P.data.mass j *
      ((∑ p ∈ P.data.fiber j,
        (1 / (p.1 : ℝ)) * tPrime n p.1) / P.data.mass j)
  field_simp [ne_of_gt (P.data.mass_pos j)]

/-- Exact mass identity for the whole selected prime block. -/
theorem anchorMass_canonicalPrimeAnchorSet_eq
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (anchors : Finset (Fin M.cellCount)) :
    anchorMass (primeWeight n) (canonicalPrimeAnchorSet M P anchors) =
      ∑ k ∈ anchors,
        P.mass (positiveBand M k) * P.center (positiveBand M k) := by
  classical
  unfold anchorMass canonicalPrimeAnchorSet
  rw [← Finset.sum_fiberwise_eq_sum_filter Finset.univ
    (anchors.map (positiveBandEmbedding M)) P.band (primeWeight n)]
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro k hk
  exact sum_primeWeight_fiber_eq_mass_mul_center M P (positiveBand M k)

/-- The interior prime mass controls the literal arithmetic centre energy.
This is an exact finite inequality; it does not pass through continuum
centres. -/
theorem epsilon_mul_anchorMass_le_centerEnergy
    {n W : ℕ} (P : Partition n W (Fin (M.cellCount + 1)))
    (hn : 1 < n)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) :
    epsilon * anchorMass (primeWeight n)
        (canonicalPrimeAnchorSet M P anchors) ≤ P.centerEnergy := by
  classical
  have hCenterLower (k : Fin M.cellCount) (hk : k ∈ anchors) :
      epsilon ≤ P.center (positiveBand M k) := by
    exact (P.center_mem_of_coord_bounds (positiveBand M k) (fun p hp ↦ by
      apply hinterior p
      exact (mem_canonicalPrimeAnchorSet_iff M).mpr
        ⟨k, hk,
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp⟩)).1
  rw [anchorMass_canonicalPrimeAnchorSet_eq M]
  have hSelected :
      epsilon * (∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k)) ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) *
            P.center (positiveBand M k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hmass := (P.data.mass_pos (positiveBand M k)).le
    have hcenter : 0 ≤ P.center (positiveBand M k) :=
      hepsilon.trans (hCenterLower k hk)
    have hdiff : 0 ≤ P.center (positiveBand M k) - epsilon :=
      sub_nonneg.mpr (hCenterLower k hk)
    nlinarith [mul_nonneg (mul_nonneg hmass hcenter) hdiff]
  calc
    epsilon * (∑ k ∈ anchors,
        P.mass (positiveBand M k) * P.center (positiveBand M k)) ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) *
            P.center (positiveBand M k) := hSelected
    _ = ∑ j ∈ anchors.map (positiveBandEmbedding M),
          P.mass j * P.center j * P.center j := by
      rw [Finset.sum_map]
      rfl
    _ ≤ ∑ j,
          P.mass j * P.center j * P.center j := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro j
      exact mul_nonneg
        (mul_nonneg (P.data.mass_pos j).le
          (P.center_mem_zero_one hn j).1)
        (P.center_mem_zero_one hn j).1
    _ = P.centerEnergy := by
      rfl

/-- A selected literal prime lies between the actual endpoint coordinates
of its selected cell. -/
theorem canonicalPrimeAnchorSet_mem_Icc
    {n W : ℕ} {P : Partition n W (Fin (M.cellCount + 1))}
    (E : IntervalCertificate P) (hn : 1 < n) (hWTwo : 2 ≤ W)
    {epsilon : ℝ} (anchors : Finset (Fin M.cellCount))
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n) (E.lower (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n) (E.upper (positiveBand M k) : ℝ) ≤
        1 - epsilon) :
    ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon) := by
  intro p hp
  obtain ⟨k, hk, hpk⟩ := (mem_canonicalPrimeAnchorSet_iff M).mp hp
  have hpInterval := (E.band_eq_iff p (positiveBand M k)).mp hpk
  have hy : 1 < y n := by
    rw [← Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hn)).le]
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hLowerTwo : 2 ≤ E.lower (positiveBand M k) :=
    hWTwo.trans (E.cutoff_le_lower (positiveBand M k))
  have hLowerPrime : E.lower (positiveBand M k) ≤ p.1 :=
    hpInterval.1.le
  have hCoordLower := realLogCoordinate_mono_nat hy hLowerTwo hLowerPrime
  have hPrimeTwo : 2 ≤ p.1 := hLowerTwo.trans hLowerPrime
  have hCoordUpper := realLogCoordinate_mono_nat hy hPrimeTwo hpInterval.2
  change realLogCoordinate (y n) (p.1 : ℝ) ∈ Icc epsilon (1 - epsilon)
  exact ⟨(hInteriorLower k hk).trans hCoordLower,
    hCoordUpper.trans (hInteriorUpper k hk)⟩

/-- First-moment quadrature for a canonical endpoint cell, stated as a
standalone reusable bound. -/
theorem abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W)
    {Cmoment : ℝ} {Xmoment : ℕ}
    (hMoment : ∀ A Y : ℕ, Xmoment ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
        PrimeSums.fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cmoment / Real.log (A : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (A : ℝ) ^ 2))
    (hXmoment : Xmoment ≤ W)
    (j : Fin (M.cellCount + 1)) :
    let P := canonicalPartition M hdelta hn hW S
    |P.mass j * P.center j - endpointContinuumMoment M n W j| ≤
      endpointMomentError M Cmoment n W j := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  dsimp only
  have hLowerThreshold : Xmoment ≤ E.lower j :=
    hXmoment.trans (E.cutoff_le_lower j)
  have h := hMoment (E.lower j) (E.upper j) hLowerThreshold
    (E.lower_le_upper j)
  rw [E.mass_mul_center_eq_fullLogReciprocalSum_sub]
  have hlog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hNorm :
      |(PrimeSums.fullLogReciprocalSum (E.upper j) -
            PrimeSums.fullLogReciprocalSum (E.lower j)) /
            Real.log (y n) - E.continuumMoment j| ≤
        (2 * Cmoment / Real.log (E.lower j : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (E.lower j : ℝ) ^ 2)) /
            Real.log (y n) := by
    unfold IntervalCertificate.continuumMoment
    rw [show
      (PrimeSums.fullLogReciprocalSum (E.upper j) -
            PrimeSums.fullLogReciprocalSum (E.lower j)) /
            Real.log (y n) -
          (Real.log (E.upper j : ℝ) - Real.log (E.lower j : ℝ)) /
            Real.log (y n) =
        ((PrimeSums.fullLogReciprocalSum (E.upper j) -
            PrimeSums.fullLogReciprocalSum (E.lower j)) -
          (Real.log (E.upper j : ℝ) - Real.log (E.lower j : ℝ))) /
            Real.log (y n) by ring]
    rw [abs_div, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right h hlog.le
  simpa only [P, E, canonicalCertificate_lower,
    endpointMomentError] using hNorm

/-- The structural anchor cutoff.  It is defined before, and is independent
of, every later mesh and selected anchor block. -/
noncomputable def canonicalPrimeAnchorCutoff : ℕ :=
  max 2 MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff

/-- Uniform literal prime-anchor package for every fixed permitted mesh,
using the preceding named cutoff.  The order in the type is the order used
by the paper: the cutoff can be selected before `M`. -/
theorem canonicalPrimeAnchorCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {epsilon : ℝ}
        (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
        (∀ k ∈ anchors, epsilon < M.lower k) →
        (∀ k ∈ anchors, M.upper k ≤ 1 - epsilon) →
        ((1 : ℝ) / 8 ≤ (∑ k ∈ anchors, M.width k) / 2) →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let anchor := canonicalPrimeAnchorSet M P anchors
          (∀ p ∈ anchor, tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) ∧
            (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor := by
  let Cmoment : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xmoment : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  have hCmoment : 0 < Cmoment := by
    simpa only [Cmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant_pos
  have hMoment : ∀ A Y : ℕ, Xmoment ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cmoment / Real.log (A : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cmoment, Xmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  intro W hW epsilon anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hWTwo : 2 ≤ W := (le_max_left 2 Xmoment).trans hW
  have hWne : W ≠ 0 := by omega
  have hXmoment : Xmoment ≤ W := (le_max_right 2 Xmoment).trans hW
  have hCoverage := eventually_canonical_anchorBlock_coverage M hdelta
    hWne hWTwo anchors hAnchors hIdealLower hIdealUpper hIdealMass
  let e : ℝ := 1 / (32 * (anchors.card : ℝ))
  have hCardPosNat : 0 < anchors.card := Finset.card_pos.mpr hAnchors
  have hCardPos : (0 : ℝ) < anchors.card := by exact_mod_cast hCardPosNat
  have he : 0 < e := by
    dsimp only [e]
    positivity
  have hApprox : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        |endpointContinuumMoment M n W (positiveBand M k) - M.width k| ≤ e ∧
          endpointMomentError M Cmoment n W (positiveBand M k) ≤ e := by
    rw [Filter.eventually_all]
    intro k
    have hMain := tendsto_positive_endpointContinuumMoment M hdelta W k
    have hMainSmall := hMain.eventually
      (Metric.eventually_nhds_iff.mpr ⟨e, he, fun x hx ↦ by
        simpa only [Real.dist_eq] using hx⟩)
    have hError := tendsto_positive_endpointMomentError_zero
      M hdelta Cmoment W k
    have hErrorSmall := hError.eventually (eventually_le_nhds he)
    filter_upwards [hMainSmall, hErrorSmall] with n hnMain hnError
    exact ⟨hnMain.le, hnError⟩
  filter_upwards [hCoverage, hApprox] with n hCoverageN hApproxN
  obtain ⟨hn, hCoverageAll⟩ := hCoverageN
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hInteriorLower, hInteriorUpper, _hContinuumMass⟩ :=
    hCoverageAll S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  let anchor := canonicalPrimeAnchorSet M P anchors
  have hInterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Icc epsilon (1 - epsilon) := by
    exact canonicalPrimeAnchorSet_mem_Icc M E hn hWTwo anchors
      hInteriorLower hInteriorUpper
  have hCellApprox (k : Fin M.cellCount) :
      |P.mass (positiveBand M k) * P.center (positiveBand M k) -
          M.width k| ≤ 2 * e := by
    have hPNT := abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
      M hdelta hn hWne S hMoment hXmoment (positiveBand M k)
    calc
      |P.mass (positiveBand M k) * P.center (positiveBand M k) -
          M.width k| ≤
          |P.mass (positiveBand M k) * P.center (positiveBand M k) -
            endpointContinuumMoment M n W (positiveBand M k)| +
          |endpointContinuumMoment M n W (positiveBand M k) -
            M.width k| := abs_sub_le _ _ _
      _ ≤ e + e := add_le_add (hPNT.trans (hApproxN k).2)
        (hApproxN k).1
      _ = 2 * e := by ring
  have hSumLower :
      (∑ k ∈ anchors, M.width k) - (1 : ℝ) / 16 ≤
        ∑ k ∈ anchors,
          P.mass (positiveBand M k) * P.center (positiveBand M k) := by
    have hEach (k : Fin M.cellCount) (hk : k ∈ anchors) :
        M.width k - 2 * e ≤
          P.mass (positiveBand M k) * P.center (positiveBand M k) := by
      have hleft := neg_le_of_abs_le (hCellApprox k)
      linarith
    have hsum := Finset.sum_le_sum hEach
    calc
      (∑ k ∈ anchors, M.width k) - (1 : ℝ) / 16 =
          ∑ k ∈ anchors, (M.width k - 2 * e) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const]
        dsimp only [e]
        have hcardInv : (anchors.card : ℝ) * (anchors.card : ℝ)⁻¹ = 1 :=
          mul_inv_cancel₀ (ne_of_gt hCardPos)
        have hconst : anchors.card •
            (2 * (1 / (32 * (anchors.card : ℝ)))) = (1 : ℝ) / 16 := by
          rw [nsmul_eq_mul]
          change (anchors.card : ℝ) *
            (2 * (1 / (32 * (anchors.card : ℝ)))) = 1 / 16
          calc
            (anchors.card : ℝ) *
                (2 * (1 / (32 * (anchors.card : ℝ)))) =
                ((anchors.card : ℝ) * (anchors.card : ℝ)⁻¹) *
                  (2 * 32⁻¹) := by ring
            _ = 1 / 16 := by rw [hcardInv]; norm_num
        rw [hconst]
      _ ≤ _ := hsum
  have hWidth : (1 : ℝ) / 4 ≤ ∑ k ∈ anchors, M.width k := by
    linarith
  have hMassLower : (1 : ℝ) / 8 ≤
      anchorMass (primeWeight n) anchor := by
    rw [anchorMass_canonicalPrimeAnchorSet_eq M]
    exact le_trans (by linarith : (1 : ℝ) / 8 ≤
      (∑ k ∈ anchors, M.width k) - (1 : ℝ) / 16) hSumLower
  exact ⟨hInterior, hMassLower⟩

/-- Existential compatibility wrapper.  Its witness is the named structural
cutoff, so no mesh dependence is hidden by the existential. -/
theorem exists_cutoff_eventually_canonicalPrimeAnchor
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {epsilon : ℝ}
        (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
        (∀ k ∈ anchors, epsilon < M.lower k) →
        (∀ k ∈ anchors, M.upper k ≤ 1 - epsilon) →
        ((1 : ℝ) / 8 ≤ (∑ k ∈ anchors, M.width k) / 2) →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let anchor := canonicalPrimeAnchorSet M P anchors
          (∀ p ∈ anchor, tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) ∧
            (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor := by
  exact ⟨canonicalPrimeAnchorCutoff,
    canonicalPrimeAnchorCutoff_eventually M hdelta⟩

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
