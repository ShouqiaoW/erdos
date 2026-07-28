import Erdos390.Full.RegularMeshActualMomentBoundsEventually
import Erdos390.Full.PaperCanonicalPrimeAnchorEventually
import Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

/-!
# Canonical actual-prime moment bounds, uniformly in the separation proof

`RegularMeshActualMomentBoundsEventually` constructs a partition
existentially.  For the paper-facing bridge we need the same estimates on
the literal canonical partition appearing in the bridge hypothesis, and we
need them for every proof of the scale-separation inequalities.  Proof
irrelevance is not used as an analytic input here: the endpoint inequalities
are established first and the canonical partition is then constructed from
any supplied separation proof.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer KernelPrimeQuadrature PrimeBandQuadrature
open PrimeCoordinateSecondMoment MovingLowMomentQuadrature

/-- Named global witnesses for reciprocal-mass quadrature. -/
noncomputable def canonicalMassQuadratureConstant : ℝ :=
  Classical.choose
    PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound

noncomputable def canonicalMassQuadratureCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound).2

theorem canonicalMassQuadratureBound
    (A Y : ℕ) (hA : canonicalMassQuadratureCutoff ≤ A)
    (hAY : A ≤ Y) :
    |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * canonicalMassQuadratureConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeBandQuadrature.exists_fullReciprocalSum_interval_error_bound).2)
    A Y hA hAY

/-- Named global witnesses for the square-coordinate quadrature. -/
noncomputable def canonicalSecondMomentConstant : ℝ :=
  Classical.choose
    PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound

noncomputable def canonicalSecondMomentCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound).2

theorem canonicalSecondMomentBound
    (z : ℝ) (hz : 1 < z) (A Y : ℕ)
    (hA : canonicalSecondMomentCutoff ≤ A) (hAY : A ≤ Y) :
    |KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z Y -
        KernelPrimeQuadrature.fullWeightedReciprocalSum
          PrimeCoordinateSecondMoment.squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
      3 * canonicalSecondMomentConstant /
        (Real.log z ^ 2 * Real.log (A : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      PrimeCoordinateSecondMoment.exists_uniform_squarePrimeCell_error_bound).2)
    z hz A Y hA hAY

/-- One mesh-independent cutoff for all three moment quadratures. -/
noncomputable def canonicalActualMomentCutoff : ℕ :=
  max 8 (max canonicalMassQuadratureCutoff
    (max MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
      canonicalSecondMomentCutoff))

namespace Mesh

section DiagonalMomentMesh

variable {delta : ℝ} (M : Mesh delta delta)

/-- Canonical form of the unconditional actual-prime moment theorem.  The
cutoff precedes `n`, and after that choice the conclusion holds for every
literal canonical partition obtained from a scale-separation proof. -/
theorem canonicalActualMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            (delta + M.ratio) ^ 2 / 16 ≤ P.variance ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 ∧
            P.totalL1 / (delta + M.ratio) ≤ 7 ∧
            (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
            P.variance / (delta + M.ratio) ^ 2 ≤ 4 := by
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Xmass : ℕ := canonicalMassQuadratureCutoff
  let Cfirst : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : ℝ := canonicalSecondMomentConstant
  let Xsecond : ℕ := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : ℝ) ^ 2 -
            realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
    intro z hz A Y hA hAY
    simpa only [Csecond, Xsecond] using
      canonicalSecondMomentBound z hz A Y hA hAY
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint := eventually_endpointMomentBounds M hdelta W
    Cmass Cfirst Csecond (by omega : 1 < W)
  filter_upwards [hEndpoint] with n R
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hReady := momentReady_of_endpointMomentBounds M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hW8 hXmass hXfirst hXsecond
      hMass hFirst hSecond R
  obtain ⟨hL1, hVarLower, hVarUpper⟩ :=
    actual_moment_bounds_of_ready M P E (fun j ↦ rfl) (fun j ↦ rfl)
      hdelta M.ratio_le_eta hn hReady
  obtain ⟨hRelL1, hRelInv, hRelVar⟩ :=
    relative_row_inputs_of_actual_moment_bounds M P hdelta hL1
      hVarLower hVarUpper
  have hSup := actual_deviation_sup_le_scale M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn
  exact ⟨hSup, hL1, hVarLower, hVarUpper, hRelL1, hRelInv, hRelVar⟩

/-- Existential compatibility wrapper whose witness is explicitly the
mesh-independent structural cutoff above. -/
theorem exists_cutoff_eventually_canonical_actual_moment_bounds
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            (delta + M.ratio) ^ 2 / 16 ≤ P.variance ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 ∧
            P.totalL1 / (delta + M.ratio) ≤ 7 ∧
            (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
            P.variance / (delta + M.ratio) ^ 2 ≤ 4 := by
  exact ⟨canonicalActualMomentCutoff,
    canonicalActualMomentCutoff_eventually M hdelta⟩

end DiagonalMomentMesh

section GenericFirstMomentMesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The deviation, first-moment, and variance-upper estimates are uniform
for independent mesh parameters `delta` and `eta`.  No variance lower bound,
and hence no comparison `M.ratio ≤ delta`, is used here. -/
theorem canonicalActualPreliminaryMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            delta ^ 2 / 4 ≤ P.bandVariance 0 ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Xmass : ℕ := canonicalMassQuadratureCutoff
  let Cfirst : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : ℕ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : ℝ := canonicalSecondMomentConstant
  let Xsecond : ℕ := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : ℕ, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : ℕ, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cfirst / Real.log (A : ℝ) ^ 3 +
          Cfirst / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : ℝ) ^ 2 -
            realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
    intro z hz A Y hA hAY
    simpa only [Csecond, Xsecond] using
      canonicalSecondMomentBound z hz A Y hA hAY
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint := eventually_endpointMomentBounds M hdelta W
    Cmass Cfirst Csecond (by omega : 1 < W)
  filter_upwards [hEndpoint] with n R
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hReady := momentReady_of_endpointMomentBounds M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hW8 hXmass hXfirst hXsecond
      hMass hFirst hSecond R
  have hL1 := actual_L1_bound_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hVarUpper := actual_variance_upper_of_ready M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn hReady
  have hLow := actual_low_bandVariance_lower_of_ready M P E
    (fun j ↦ rfl) hdelta hn hReady
  have hSup := actual_deviation_sup_le_scale M P E
    (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn
  exact ⟨hSup, hL1, hLow, hVarUpper⟩

/-- Generic actual-scale upper-moment interface. -/
theorem canonicalActualUpperMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 := by
  intro W hW
  have hPreliminary :=
    canonicalActualPreliminaryMomentCutoff_eventually M hdelta W hW
  filter_upwards [hPreliminary] with n hAt
  obtain ⟨hWne, hn, hAll⟩ := hAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hSup, hL1, _hLow, hVarUpper⟩ := hAll S
  exact ⟨hSup, hL1, hVarUpper⟩

/-- The smaller first-moment interface retained for the prime-graph
reference argument. -/
theorem canonicalActualFirstMomentCutoff_eventually
    (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) := by
  intro W hW
  have hUpper := canonicalActualUpperMomentCutoff_eventually M hdelta W hW
  filter_upwards [hUpper] with n hAt
  obtain ⟨hWne, hn, hAll⟩ := hAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hSup, hL1, _hVarUpper⟩ := hAll S
  exact ⟨hSup, hL1⟩

/-- Existential compatibility wrapper for the full generic upper-moment
package, with the named cutoff exposed before the mesh and ambient integer. -/
theorem exists_cutoff_eventually_canonical_actual_upper_moment_bounds
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 :=
  ⟨canonicalActualMomentCutoff,
    canonicalActualUpperMomentCutoff_eventually M hdelta⟩

/-- Existential compatibility wrapper with the same named global cutoff. -/
theorem exists_cutoff_eventually_canonical_actual_first_moment_bounds
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) :=
  ⟨canonicalActualMomentCutoff,
    canonicalActualFirstMomentCutoff_eventually M hdelta⟩

end GenericFirstMomentMesh

section DiagonalMesh

variable {delta : ℝ} (M : Mesh delta delta)

/-- On a sufficiently fine paper mesh, the literal interior anchor mass
forces the centre energy to dominate the within-cell variance.  Both sides
are finite arithmetic quantities. -/
theorem variance_le_centerEnergy_of_canonical_anchor
    {n W : ℕ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ (1 : ℝ) / 32)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W)
    (anchors : Finset (Fin M.cellCount))
    (hinterior : ∀ p ∈ canonicalPrimeAnchorSet M
        (canonicalPartition M hdelta hn hWne S) anchors,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8))
    (hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M
          (canonicalPartition M hdelta hn hWne S) anchors))
    (hVarUpper :
      (canonicalPartition M hdelta hn hWne S).variance ≤
        4 * (delta + M.ratio) ^ 2) :
    (canonicalPartition M hdelta hn hWne S).variance ≤
      (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  let P := canonicalPartition M hdelta hn hWne S
  have hEnergy := epsilon_mul_anchorMass_le_centerEnergy M P hn
    (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hinterior
  have hEnergyFloor : (1 : ℝ) / 64 ≤ P.centerEnergy := by
    calc
      (1 : ℝ) / 64 = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
      _ ≤ (1 / 8 : ℝ) *
          FiniteAnchoredDirichletQuadratic.anchorMass
            (PrimeSquarefreeDirichletGeometry.primeWeight n)
            (canonicalPrimeAnchorSet M P anchors) := by
        exact mul_le_mul_of_nonneg_left hAnchorMass (by norm_num)
      _ ≤ P.centerEnergy := hEnergy
  have hratio : M.ratio ≤ delta := M.ratio_le_eta
  have hw : delta + M.ratio ≤ (1 : ℝ) / 16 := by linarith
  have hwNonneg : 0 ≤ delta + M.ratio :=
    (add_pos hdelta M.ratio_pos).le
  have hSmallVar : 4 * (delta + M.ratio) ^ 2 ≤ (1 : ℝ) / 64 := by
    nlinarith
  exact hVarUpper.trans (hSmallVar.trans hEnergyFloor)

/-- Complete geometric/moment input package for Lemma 8.6 on every fixed
permitted regular mesh.  The row tolerance and cutoff are chosen before the
ambient integer.  No signed-profile, prime-power, or nuisance estimate is
included here; those are independent probabilistic inputs. -/
theorem exists_cutoff_eventually_canonical_lemma86_geometric_inputs
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ (1 : ℝ) / 32)
    {rowTarget : ℝ} (hrowTarget : 0 < rowTarget)
    (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
    (hIdealLower : ∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k)
    (hIdealUpper : ∀ k ∈ anchors,
      M.upper k ≤ 1 - (1 / 8 : ℝ))
    (hIdealMass : (1 / 8 : ℝ) ≤
      (∑ k ∈ anchors, M.width k) / 2) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            let anchor := canonicalPrimeAnchorSet M P anchors
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            (delta + M.ratio) ^ 2 / 16 ≤ P.variance ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 ∧
            P.totalL1 / (delta + M.ratio) ≤ 7 ∧
            (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
            P.variance / (delta + M.ratio) ^ 2 ≤ 4 ∧
            P.variance ≤ P.centerEnergy ∧
            (∀ p ∈ anchor,
              tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8)) ∧
            (1 : ℝ) / 8 ≤
              FiniteAnchoredDirichletQuadratic.anchorMass
                (PrimeSquarefreeDirichletGeometry.primeWeight n) anchor ∧
            (∀ p : PrimeSquarefreeDirichletGeometry.PrimeIndex n W,
              |FiniteAnchoredDirichletQuadratic.rowResidual
                  (PrimeSquarefreeDirichletGeometry.primeWeight n)
                  (PrimeSquarefreeDirichletGeometry.primeDiagonal n)
                  (PrimeSquarefreeDirichletGeometry.primeKernel n) p| ≤
                rowTarget * tPrime n p.1) := by
  obtain ⟨Wmoment, hMomentEvent⟩ :=
    exists_cutoff_eventually_canonical_actual_moment_bounds M hdelta
  obtain ⟨Wanchor, hAnchorEvent⟩ :=
    exists_cutoff_eventually_canonicalPrimeAnchor M hdelta
  obtain ⟨Wrow, hRowEvent⟩ :=
    _root_.Erdos390.Full.PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hrowTarget
  let W₀ := max Wmoment (max Wanchor Wrow)
  refine ⟨W₀, ?_⟩
  intro W hW
  have hWmoment : Wmoment ≤ W :=
    (le_max_left Wmoment (max Wanchor Wrow)).trans hW
  have hWanchor : Wanchor ≤ W :=
    ((le_max_left Wanchor Wrow).trans
      (le_max_right Wmoment (max Wanchor Wrow))).trans hW
  have hWrow : Wrow ≤ W :=
    ((le_max_right Wanchor Wrow).trans
      (le_max_right Wmoment (max Wanchor Wrow))).trans hW
  have hMomentN := hMomentEvent W hWmoment
  have hAnchorN := hAnchorEvent W hWanchor anchors hAnchors
    hIdealLower hIdealUpper hIdealMass
  have hRowN := hRowEvent W hWrow
  filter_upwards [hMomentN, hAnchorN, hRowN] with
      n hMomentAt hAnchorAt hRowAt
  obtain ⟨hWm, hnm, hMomentAll⟩ := hMomentAt
  obtain ⟨hWa, hna, hAnchorAll⟩ := hAnchorAt
  refine ⟨hWm, hnm, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hnm hWm S
  let anchor := canonicalPrimeAnchorSet M P anchors
  obtain ⟨hSup, hL1, hVarLower, hVarUpper, hRelL1, hRelInv, hRelVar⟩ :=
    hMomentAll S
  obtain ⟨hInteriorRaw, hMassRaw⟩ := hAnchorAll S
  have hInterior : ∀ p ∈ anchor,
      tPrime n p.1 ∈ Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8) := by
    simpa only [anchor, P, Subsingleton.elim hna hnm,
      Subsingleton.elim hWa hWm] using hInteriorRaw
  have hMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n) anchor := by
    simpa only [anchor, P, Subsingleton.elim hna hnm,
      Subsingleton.elim hWa hWm] using hMassRaw
  have hVariance := variance_le_centerEnergy_of_canonical_anchor M hdelta
    hdeltaSmall hnm hWm S anchors hInterior hMass hVarUpper
  exact ⟨hSup, hL1, hVarLower, hVarUpper, hRelL1, hRelInv, hRelVar,
    hVariance, hInterior, hMass, hRowAt⟩

end DiagonalMesh

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
