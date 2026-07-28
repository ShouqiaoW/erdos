import Erdos390.Full.PaperNonstepLocalDiagonal
import Erdos390.Full.CanonicalEndpointDiagonalEventually
import Erdos390.Full.PaperCanonicalPrimeAnchorEventually
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# Canonical relative decay of the literal non-step local diagonal

For the moving low cell one must not replace the local `p^{-2}` term by an
additive `O(1/W)`: its centre tends to zero.  We instead retain the exact
decomposition into `alpha_0 * sum p^{-2}` and `sum t_p p^{-2}`.  The first
term is divided by the diverging low-cell mass, while the second vanishes
and is divided only by `H_0 alpha_0 -> delta`.

For every positive cell the lower endpoint tends to infinity, giving the
direct estimate `D_i <= w/A_i`.  The result is uniform over the finite band
set and uses the actual scale `w = delta + M.ratio`; `eta` is independent.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeSums MovingLowMomentQuadrature
open KernelPrimeQuadrature

/-- The cutoff contains only the two global prime-sum thresholds used in
the low-cell mass and first-moment arguments.  It is independent of every
later mesh, tolerance, tilt box, and head pattern. -/
def canonicalNonstepLocalDiagonalCutoff : ℕ :=
  max 2 (max canonicalMassQuadratureCutoff
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

set_option maxHeartbeats 2000000 in
/-- The literal reciprocal-square deviation diagonal is `o(w alpha_i)` in
every canonical arithmetic band.  The quantification over `hn`, `hWne`,
and `S` makes proof irrelevance unnecessary at the statement boundary. -/
theorem canonicalNonstepLocalDiagonalCutoff_eventually
    (hdelta : 0 < delta) (W : ℕ)
    (hWcut : canonicalNonstepLocalDiagonalCutoff ≤ W)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
      (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
      let P := canonicalPartition M hdelta hn hWne S
      P.normalizedDeviationReciprocalSquare i ≤
        r * (delta + M.ratio) * P.center i := by
  let w : ℝ := delta + M.ratio
  have hw : 0 < w := add_pos hdelta M.ratio_pos
  have hW2 : 2 ≤ W :=
    (le_max_left 2 (max canonicalMassQuadratureCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff)).trans hWcut
  have hXmass : canonicalMassQuadratureCutoff ≤ W :=
    ((le_max_left canonicalMassQuadratureCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2 (max canonicalMassQuadratureCutoff
        MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hWcut
  have hXmoment :
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ W :=
    ((le_max_right canonicalMassQuadratureCutoff
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff).trans
      (le_max_right 2 (max canonicalMassQuadratureCutoff
        MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff))).trans hWcut
  let Cmass : ℝ := canonicalMassQuadratureConstant
  let Cmoment : ℝ :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  have hMassQ : ∀ A Y : ℕ, canonicalMassQuadratureCutoff ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
        5 * Cmass / Real.log (A : ℝ) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass] using canonicalMassQuadratureBound A Y hA hAY
  have hMomentQ : ∀ A Y : ℕ,
      MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff ≤ A →
      A ≤ Y →
      |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        2 * Cmoment / Real.log (A : ℝ) ^ 3 +
          Cmoment / (2 * Real.log (A : ℝ) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cmoment] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound
        A Y hA hAY
  have hLowMassTop := tendsto_low_endpointActualMass_atTop M hdelta
    hXmass Cmass hMassQ
  have hLowSquareMajorant : Tendsto (fun n : ℕ ↦
      (1 / (W : ℝ)) / endpointActualMass M n W (lowBand M))
      atTop (nhds 0) := by
    simpa only [zero_div] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ 1 / (W : ℝ))
        atTop (nhds (1 / (W : ℝ)))).div_atTop hLowMassTop
  have hLowSquareSmall : ∀ᶠ n : ℕ in atTop,
      (1 / (W : ℝ)) / endpointActualMass M n W (lowBand M) <
        r * w / 2 :=
    hLowSquareMajorant.eventually
      (eventually_lt_nhds (div_pos (mul_pos hr hw) (by norm_num)))
  have hLowMomentMain : ∀ᶠ n : ℕ in atTop,
      3 * delta / 4 ≤ endpointContinuumMoment M n W (lowBand M) :=
    (tendsto_low_endpointContinuumMoment M hdelta W).eventually
      (eventually_ge_nhds (by linarith : 3 * delta / 4 < delta))
  have hLowMomentError : ∀ᶠ n : ℕ in atTop,
      endpointMomentError M Cmoment n W (lowBand M) ≤ delta / 4 :=
    (tendsto_low_endpointMomentError_zero M Cmoment W).eventually
      (eventually_le_nhds (by linarith : 0 < delta / 4))
  have hT2Small : ∀ᶠ n : ℕ in atTop,
      bandTReciprocalSquareSum n W < r * w * delta / 4 :=
    (tendsto_bandTReciprocalSquareSum_zero W).eventually
      (eventually_lt_nhds (by positivity : 0 < r * w * delta / 4))
  have hPositiveInv : ∀ᶠ n : ℕ in atTop,
      ∀ k : Fin M.cellCount,
        1 / (fullCutoff M n W (k.1 + 1) : ℝ) < r * delta := by
    rw [Filter.eventually_all]
    intro k
    have hAReal : Tendsto (fun n : ℕ ↦
        (fullCutoff M n W (k.1 + 1) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp
        (tendsto_general_positive_lowerCutoff_atTop M hdelta W k)
    have hInv := tendsto_inv_atTop_zero.comp hAReal
    simpa only [one_div] using
      hInv.eventually (eventually_lt_nhds (mul_pos hr hdelta))
  filter_upwards [hLowSquareSmall, hLowMomentMain, hLowMomentError,
    hT2Small, hPositiveInv] with n hSqSmall hMomentMain hMomentErr
      hT2 hPosInv
  intro hn hWne S i
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hMassEq (j : Fin (M.cellCount + 1)) :
      P.mass j = endpointActualMass M n W j := by
    rw [endpointActualMass_eq_fullReciprocalSum_sub]
    simpa only [P, E, canonicalCertificate_lower,
      canonicalCertificate_upper] using E.mass_eq_fullReciprocalSum_sub j
  let motive := fun j : Fin (M.cellCount + 1) ↦
    P.normalizedDeviationReciprocalSquare j ≤
      r * w * P.center j
  apply (Fin.cases (motive := motive) ?_ ?_ i)
  · have hH : 0 < P.mass (lowBand M) := P.data.mass_pos (lowBand M)
    have halpha : 0 < P.center (lowBand M) :=
      P.center_pos hn (lowBand M)
    have hS2 := bandReciprocalSquareSum_le n W (by omega : 1 ≤ W)
    have hSratio :
        (1 / P.mass (lowBand M)) * bandReciprocalSquareSum n W ≤
          r * w / 2 := by
      calc
        (1 / P.mass (lowBand M)) * bandReciprocalSquareSum n W =
            bandReciprocalSquareSum n W / P.mass (lowBand M) := by ring
        _ ≤ (1 / (W : ℝ)) / P.mass (lowBand M) :=
          div_le_div_of_nonneg_right hS2 hH.le
        _ = (1 / (W : ℝ)) /
            endpointActualMass M n W (lowBand M) := by rw [← hMassEq]
        _ ≤ r * w / 2 := hSqSmall.le
    have hPNT :=
      abs_canonical_mass_mul_center_sub_endpointContinuumMoment_le
        M hdelta hn hWne S hMomentQ hXmoment (lowBand M)
    have hHalpha : delta / 2 ≤
        P.mass (lowBand M) * P.center (lowBand M) := by
      have hleft := (abs_le.mp hPNT).1
      linarith
    have hT2nonneg : 0 ≤ bandTReciprocalSquareSum n W :=
      bandTReciprocalSquareSum_nonneg hn
    have hTtarget : bandTReciprocalSquareSum n W ≤
        (r * w / 2) *
          (P.mass (lowBand M) * P.center (lowBand M)) := by
      have hsmall : bandTReciprocalSquareSum n W ≤ r * w * delta / 4 :=
        hT2.le
      have hcoef : 0 ≤ r * w / 2 := (div_pos (mul_pos hr hw) (by norm_num)).le
      calc
        bandTReciprocalSquareSum n W ≤ r * w * delta / 4 := hsmall
        _ = (r * w / 2) * (delta / 2) := by ring
        _ ≤ (r * w / 2) *
            (P.mass (lowBand M) * P.center (lowBand M)) :=
          mul_le_mul_of_nonneg_left hHalpha hcoef
    have hTterm :
        (1 / P.mass (lowBand M)) * bandTReciprocalSquareSum n W ≤
          (r * w / 2) * P.center (lowBand M) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hH).2
      nlinarith
    have hraw :=
      P.normalizedDeviationReciprocalSquare_le_global_moments hn (lowBand M)
    calc
      P.normalizedDeviationReciprocalSquare (lowBand M) ≤
          (1 / P.mass (lowBand M)) *
            (P.center (lowBand M) * bandReciprocalSquareSum n W +
              bandTReciprocalSquareSum n W) := hraw
      _ = P.center (lowBand M) *
            ((1 / P.mass (lowBand M)) * bandReciprocalSquareSum n W) +
          (1 / P.mass (lowBand M)) * bandTReciprocalSquareSum n W := by ring
      _ ≤ P.center (lowBand M) * (r * w / 2) +
          (r * w / 2) * P.center (lowBand M) :=
        add_le_add (mul_le_mul_of_nonneg_left hSratio halpha.le) hTterm
      _ = r * w * P.center (lowBand M) := by ring
  · intro k
    let j : Fin (M.cellCount + 1) := k.succ
    let A : ℝ := fullCutoff M n W (k.1 + 1)
    have hANat : 0 < fullCutoff M n W (k.1 + 1) := by
      have hcut : W ≤ E.lower j := E.cutoff_le_lower j
      have hident : E.lower j = fullCutoff M n W (k.1 + 1) := by rfl
      rw [hident] at hcut
      omega
    have hA : 0 < A := by
      dsimp only [A]
      exact_mod_cast hANat
    have hlower : ∀ p ∈ P.data.fiber j, A < (p.1 : ℝ) := by
      intro p hp
      have hpBand : P.band p = j :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      have hpInterval := (E.band_eq_iff p j).mp hpBand
      dsimp only [A]
      have hpNat : fullCutoff M n W (k.1 + 1) < p.1 := by
        simpa only [E, j, canonicalCertificate_lower] using hpInterval.1
      exact_mod_cast hpNat
    have hdevAll : ∀ p : BandPrime n W,
        |P.deviation p| ≤ w := by
      intro p
      simpa only [w] using actual_deviation_sup_le_scale M P E
        (fun j ↦ rfl) (fun j ↦ rfl) hdelta hn p
    have hdiag := P.normalizedDeviationReciprocalSquare_le_scale_div_lower
      hA (fun p hp ↦ hlower p hp) (fun p _hp ↦ hdevAll p) hw.le
    have hInv : 1 / A ≤ r * delta := by
      exact (hPosInv k).le
    have hcoord : ∀ p ∈ P.data.fiber j,
        tPrime n p.1 ∈ Set.Icc (M.lower k) (M.upper k) := by
      simpa only [j] using positive_coord_bounds M P E
        (fun j ↦ rfl) (fun j ↦ rfl) hn k
    have hcenterLower : M.lower k ≤ P.center j :=
      (P.center_mem_of_coord_bounds j hcoord).1
    have hdeltaLower : delta ≤ M.lower k := by
      unfold RegularRelativeMesh.Mesh.lower RegularRelativeMesh.Mesh.endpoint
      have hbase : 1 ≤ 1 + M.ratio := by linarith [M.ratio_pos]
      have hpow : 1 ≤ (1 + M.ratio) ^ k.1 := one_le_pow₀ hbase
      nlinarith
    have hdeltaCenter : delta ≤ P.center j :=
      hdeltaLower.trans hcenterLower
    calc
      P.normalizedDeviationReciprocalSquare j ≤ w / A := hdiag
      _ = w * (1 / A) := by ring
      _ ≤ w * (r * delta) := mul_le_mul_of_nonneg_left hInv hw.le
      _ ≤ w * (r * P.center j) := by
        apply mul_le_mul_of_nonneg_left _ hw.le
        exact mul_le_mul_of_nonneg_left hdeltaCenter hr.le
      _ = r * w * P.center j := by ring

/-- Quantifier-order wrapper: the structural cutoff is chosen before the
independent upper mesh request `eta`, the actual mesh, and the requested
relative accuracy. -/
theorem exists_cutoff_eventually_canonical_nonstepLocalDiagonal
    (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {eta : ℝ} (M : Mesh delta eta), ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
          (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
          let P := canonicalPartition M hdelta hn hWne S
          P.normalizedDeviationReciprocalSquare i ≤
            r * (delta + M.ratio) * P.center i :=
  ⟨canonicalNonstepLocalDiagonalCutoff,
    fun W hW _eta M _r hr ↦
      canonicalNonstepLocalDiagonalCutoff_eventually M hdelta W hW hr⟩

/-- Final global quantifier order.  The witness is chosen before both fine
mesh parameters; only the ambient threshold is allowed to depend on the
later fixed mesh and requested relative accuracy. -/
theorem exists_global_cutoff_eventually_canonical_nonstepLocalDiagonal :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta), ∀ (hdelta : 0 < delta),
        ∀ r : ℝ, 0 < r →
          ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
            (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
            let P := canonicalPartition M hdelta hn hWne S
            P.normalizedDeviationReciprocalSquare i ≤
              r * (delta + M.ratio) * P.center i := by
  refine ⟨canonicalNonstepLocalDiagonalCutoff, ?_⟩
  intro W hW delta _eta M hdelta _r hr
  exact canonicalNonstepLocalDiagonalCutoff_eventually M hdelta W hW hr

end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs
