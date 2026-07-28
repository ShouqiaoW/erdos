import Erdos390.Full.CanonicalEndpointRelativeCenterEventually
import Erdos390.Full.CanonicalEndpointDoubleKernelRowEventually
import Erdos390.Full.RegularMeshActualMomentBounds

/-!
# The canonical moving-low centre has the sharp reciprocal envelope

This file records the quantitative fact needed when an `o(1)` prime-profile
error is divided by the centre of the moving low cell.  The loss is exactly
`O(log log n)`: uniformly in every proof of scale separation and in every
canonical band,

`1 / center i <= C * log (log n)`.

The proof does not identify the low centre with a fixed continuum centre.
It uses the already proved *relative* endpoint-centre convergence, the
literal endpoint continuum first moment, and an elementary upper bound for
the literal endpoint continuum harmonic mass.  Thus it remains valid for the
moving low endpoint and has the quantifier order required in Sections 8.4--8.6.
-/

open Filter Topology

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PositiveCellTransfer PrimeBandQuadrature MovingLowMomentQuadrature
open MovingLowGaugeTransfer KernelPrimeQuadrature

/- A mesh-independent cutoff for the sharp moving-low centre envelope. -/
noncomputable def canonicalCenterEnvelopeCutoff : ℕ :=
  max 3 canonicalRelativeCenterCutoff

/-- The explicit reciprocal-centre constant used throughout the later sharp
row and Schur estimates. -/
def canonicalCenterEnvelopeConstant (delta : ℝ) : ℝ := 4 / delta

theorem canonicalCenterEnvelopeConstant_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < canonicalCenterEnvelopeConstant delta :=
  div_pos (by norm_num) hdelta

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- The literal continuum mass of the canonical low endpoint cell is positive
and is at most `log L`.  The proof uses the actual floored upper endpoint; no
replacement of that endpoint by `y` occurs in the definition. -/
theorem low_endpointContinuumMass_pos_le_logL
    {n W : ℕ} (hdelta : 0 < delta) (hW3 : 3 ≤ W)
    (hn : 1 < n) (hWne : W ≠ 0) (S : ScaleSeparation M n W) :
    0 < endpointContinuumMass M n W (lowBand M) ∧
      endpointContinuumMass M n W (lowBand M) ≤
        Real.log (Scale.L n) := by
  let A := fullCutoff M n W 1
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    every_fullCutoff_cell_has_prime M hWne S (lowBand M)
  have hWA : W < A := by
    dsimp only [A]
    simpa only [lowBand, Fin.val_mk, Nat.zero_add] using
      hpLower.trans_le hpUpper
  have hWpos : (0 : ℝ) < (W : ℝ) := by positivity
  have hApos : (0 : ℝ) < (A : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < W) hWA.le)
  have hWone : (1 : ℝ) < Real.log (W : ℝ) := by
    rw [Real.lt_log_iff_exp_lt hWpos]
    exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hW3)
  have hLogWnonneg : 0 ≤ Real.log (Real.log (W : ℝ)) :=
    Real.log_nonneg hWone.le
  have hLogWltLogA : Real.log (W : ℝ) < Real.log (A : ℝ) :=
    Real.strictMonoOn_log hWpos hApos (by exact_mod_cast hWA)
  have hMassPos : 0 < endpointContinuumMass M n W (lowBand M) := by
    unfold endpointContinuumMass lowBand
    simp only [Nat.zero_add, fullCutoff_zero]
    change 0 < Real.log (Real.log (A : ℝ)) -
      Real.log (Real.log (W : ℝ))
    exact sub_pos.mpr
      (Real.strictMonoOn_log (zero_lt_one.trans hWone)
        (zero_lt_one.trans (hWone.trans hLogWltLogA)) hLogWltLogA)
  have hALast : A ≤ fullCutoff M n W (M.cellCount + 1) := by
    exact hmono (by omega)
  have hAyNat : A ≤ yNat n := by
    simpa only [fullCutoff_last M (Nat.zero_lt_of_lt hn)] using hALast
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hAY : (A : ℝ) ≤ y n :=
    (by exact_mod_cast hAyNat : (A : ℝ) ≤ (yNat n : ℝ)).trans hyNatY
  have hLogALeLogY : Real.log (A : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hApos hAY
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hLogALeL : Real.log (A : ℝ) ≤ Scale.L n := by
    calc
      Real.log (A : ℝ) ≤ Real.log (y n) := hLogALeLogY
      _ = (2 / 9 : ℝ) * Scale.L n :=
        Scale.log_y (Nat.zero_lt_of_lt hn)
      _ ≤ Scale.L n := by nlinarith
  have hLogLogALeLogL :
      Real.log (Real.log (A : ℝ)) ≤ Real.log (Scale.L n) :=
    Real.log_le_log
      (zero_lt_one.trans (hWone.trans hLogWltLogA)) hLogALeL
  constructor
  · exact hMassPos
  · unfold endpointContinuumMass lowBand
    simp only [Nat.zero_add, fullCutoff_zero]
    change Real.log (Real.log (A : ℝ)) -
      Real.log (Real.log (W : ℝ)) ≤ Real.log (Scale.L n)
    linarith

/-- Uniform sharp reciprocal-centre envelope for the literal canonical
partition, with its mesh-independent cutoff and explicit constant exposed.
Only the ambient `n` threshold may depend on the later mesh. -/
theorem canonicalCenterEnvelopeCutoff_eventually_inverse
    (hdelta : 0 < delta) (W : ℕ)
    (hW : canonicalCenterEnvelopeCutoff ≤ W) :
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
        1 / (canonicalPartition M hdelta hn hWne S).center i ≤
          canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) := by
  have hW3 : 3 ≤ W := (le_max_left 3 canonicalRelativeCenterCutoff).trans hW
  have hWr : canonicalRelativeCenterCutoff ≤ W :=
    (le_max_right 3 canonicalRelativeCenterCutoff).trans hW
  have hRelative := canonicalRelativeCenterCutoff_eventually M hdelta W hWr
    (1 / 2 : ℝ) (by norm_num)
  have hLowMoment :=
    (tendsto_low_endpointContinuumMoment M hdelta W).eventually
      (eventually_ge_nhds (by linarith : delta / 2 < delta))
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogLTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  have hLogL := hLogLTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [hRelative, hLowMoment, hLogL] with n hrel hmoment hlogL
  obtain ⟨hWne₀, hn₀, S₀, hratio⟩ := hrel
  intro hn hWne S i
  let P := canonicalPartition M hdelta hn hWne S
  let E := canonicalCertificate M hdelta hn hWne S
  have hLlogPos : 0 < Real.log (Scale.L n) := zero_lt_one.trans_le hlogL
  refine Fin.cases ?_ (fun k ↦ ?_) i
  · have hmass :=
      low_endpointContinuumMass_pos_le_logL M hdelta hW3 hn hWne S
    let c : ℝ := endpointContinuumCenter M n W (lowBand M)
    have hcId : c = E.continuumCenter (lowBand M) := by rfl
    have hcPos : 0 < c := by
      dsimp only [c, endpointContinuumCenter]
      exact div_pos ((div_pos hdelta (by norm_num)).trans_le hmoment) hmass.1
    have hcLower : delta / (2 * Real.log (Scale.L n)) ≤ c := by
      dsimp only [c, endpointContinuumCenter]
      calc
        delta / (2 * Real.log (Scale.L n)) =
            (delta / 2) / Real.log (Scale.L n) := by ring
        _ ≤ (delta / 2) /
              endpointContinuumMass M n W (lowBand M) :=
          div_le_div_of_nonneg_left (by positivity) hmass.1 hmass.2
        _ ≤ endpointContinuumMoment M n W (lowBand M) /
              endpointContinuumMass M n W (lowBand M) :=
          div_le_div_of_nonneg_right hmoment hmass.1.le
    have hratio' :
        |P.center (lowBand M) / c - 1| ≤ (1 / 2 : ℝ) := by
      simpa only [P, E, hcId] using hratio (lowBand M)
    have hhalfRatio : (1 / 2 : ℝ) ≤ P.center (lowBand M) / c := by
      have hleft := (abs_le.mp hratio').1
      linarith
    have hcenterLower :
        delta / (4 * Real.log (Scale.L n)) ≤ P.center (lowBand M) := by
      have hhalfCenter : (1 / 2 : ℝ) * c ≤ P.center (lowBand M) :=
        (le_div_iff₀ hcPos).mp hhalfRatio
      calc
        delta / (4 * Real.log (Scale.L n)) =
            (1 / 2 : ℝ) * (delta / (2 * Real.log (Scale.L n))) := by ring
        _ ≤ (1 / 2 : ℝ) * c :=
          mul_le_mul_of_nonneg_left hcLower (by norm_num)
        _ ≤ P.center (lowBand M) := hhalfCenter
    have hcenterPos : 0 < P.center (lowBand M) :=
      (div_pos hdelta (mul_pos (by norm_num) hLlogPos)).trans_le hcenterLower
    have hinv := one_div_le_one_div_of_le
      (div_pos hdelta (mul_pos (by norm_num) hLlogPos)) hcenterLower
    change 1 / P.center (lowBand M) ≤
      canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)
    calc
      1 / P.center (lowBand M) ≤
          1 / (delta / (4 * Real.log (Scale.L n))) := hinv
      _ = canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) := by
        unfold canonicalCenterEnvelopeConstant
        field_simp [hdelta.ne', hLlogPos.ne']
  · have hcoord (p : BandPrime n W)
        (hp : p ∈ P.data.fiber (positiveBand M k)) :
        tPrime n p.1 ∈ Set.Icc (M.lower k) (M.upper k) := by
      have hpBand : P.band p = positiveBand M k :=
        (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff P.data).mp hp
      have hpInterval :=
        (PositiveCellTransfer.IntervalCertificate.band_eq_iff E p
          (positiveBand M k)).mp hpBand
      have hpLower := hpInterval.1
      have hpUpper := hpInterval.2
      change fullCutoff M n W (k.1 + 1) < p.1 at hpLower
      change p.1 ≤ fullCutoff M n W (k.1 + 1 + 1) at hpUpper
      simp only [fullCutoff] at hpLower hpUpper
      exact ⟨(realLogCoordinate_floorScale_lt_prime hn hpLower).le,
        prime_logCoordinate_le_of_le_floorScale hn
          (prime_of_mem_primeBand p.2).pos hpUpper⟩
    have hcenterLowerCell : M.lower k ≤ P.center (positiveBand M k) :=
      (P.center_mem_of_coord_bounds (positiveBand M k) hcoord).1
    have hdeltaLower : delta ≤ M.lower k := by
      unfold RegularRelativeMesh.Mesh.lower RegularRelativeMesh.Mesh.endpoint
      have hbase : 1 ≤ 1 + M.ratio := by linarith [M.ratio_pos]
      have hpow : 1 ≤ (1 + M.ratio) ^ k.1 := one_le_pow₀ hbase
      nlinarith
    have hdeltaCenter : delta ≤ P.center (positiveBand M k) :=
      hdeltaLower.trans hcenterLowerCell
    have hinv : 1 / P.center (positiveBand M k) ≤ 1 / delta :=
      one_div_le_one_div_of_le hdelta hdeltaCenter
    change 1 / P.center (positiveBand M k) ≤
      canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)
    calc
      1 / P.center (positiveBand M k) ≤ 1 / delta := hinv
      _ ≤ canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) := by
        unfold canonicalCenterEnvelopeConstant
        have hdeltaInvPos : 0 < 1 / delta := one_div_pos.mpr hdelta
        calc
          1 / delta ≤ 4 * (1 / delta) * Real.log (Scale.L n) := by
            nlinarith
          _ = (4 / delta) * Real.log (Scale.L n) := by ring

/-- Existential compatibility form.  Both witnesses are the named global
objects above, rather than choices made after seeing the mesh. -/
theorem exists_cutoff_eventually_canonical_center_inverse_logL
    (hdelta : 0 < delta) :
    ∃ Calpha : ℝ, 0 < Calpha ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
        1 / (canonicalPartition M hdelta hn hWne S).center i ≤
          Calpha * Real.log (Scale.L n) :=
  ⟨canonicalCenterEnvelopeConstant delta,
    canonicalCenterEnvelopeConstant_pos hdelta,
    canonicalCenterEnvelopeCutoff,
    fun W hW ↦ canonicalCenterEnvelopeCutoff_eventually_inverse M hdelta W hW⟩

/-- Exact all-band lower form with the same global cutoff. -/
theorem canonicalCenterEnvelopeCutoff_eventually_lower
    (hdelta : 0 < delta) (W : ℕ)
    (hW : canonicalCenterEnvelopeCutoff ≤ W) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
      (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
      (1 / canonicalCenterEnvelopeConstant delta) /
          Real.log (Scale.L n) ≤
        (canonicalPartition M hdelta hn hWne S).center i := by
  have hCalpha := canonicalCenterEnvelopeConstant_pos hdelta
  have hmain := canonicalCenterEnvelopeCutoff_eventually_inverse M hdelta W hW
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogLTop : Tendsto (fun n : ℕ ↦ Real.log (Scale.L n))
      atTop atTop := Real.tendsto_log_atTop.comp hLTop
  have hLogL := hLogLTop.eventually (eventually_gt_atTop (0 : ℝ))
  filter_upwards [hmain, hLogL] with n hinv hlog
  intro hn hWne S i
  let P := canonicalPartition M hdelta hn hWne S
  have hcenter : 0 < P.center i := P.center_pos hn i
  have hprod : 1 ≤
      (canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)) *
        P.center i :=
    (div_le_iff₀ hcenter).mp (hinv hn hWne S i)
  have hquot :
      1 / (canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n)) ≤
        P.center i :=
    (div_le_iff₀ (mul_pos hCalpha hlog)).mpr (by
      simpa only [mul_comm] using hprod)
  change (1 / canonicalCenterEnvelopeConstant delta) /
      Real.log (Scale.L n) ≤ P.center i
  convert hquot using 1
  field_simp [hCalpha.ne', hlog.ne']

/-- Equivalent all-band lower-scale form.  The sharp nuisance, marked-row,
and guard estimates consume a uniform lower bound `c / log L <= alpha_i`,
whereas projected-row perturbations consume the reciprocal form above. -/
theorem exists_cutoff_eventually_canonical_center_lower_logL
    (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
        c / Real.log (Scale.L n) ≤
          (canonicalPartition M hdelta hn hWne S).center i := by
  exact ⟨1 / canonicalCenterEnvelopeConstant delta,
    one_div_pos.mpr (canonicalCenterEnvelopeConstant_pos hdelta),
    canonicalCenterEnvelopeCutoff,
    fun W hW ↦ canonicalCenterEnvelopeCutoff_eventually_lower M hdelta W hW⟩

/-- Low-cell projection of the preceding all-band envelope. -/
theorem exists_cutoff_eventually_canonical_low_center_lower_logL
    (hdelta : 0 < delta) :
    ∃ c : ℝ, 0 < c ∧ ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W),
        c / Real.log (Scale.L n) ≤
          (canonicalPartition M hdelta hn hWne S).center (lowBand M) := by
  obtain ⟨c, hc, W₀, hmain⟩ :=
    exists_cutoff_eventually_canonical_center_lower_logL M hdelta
  exact ⟨c, hc, W₀, fun W hW ↦ (hmain W hW).mono fun n hn hn' hWne S ↦
    hn hn' hWne S (lowBand M)⟩

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
