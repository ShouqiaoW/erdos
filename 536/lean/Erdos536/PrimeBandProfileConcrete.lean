import Erdos536.PrimeBandProfile
import Erdos536.UniformLocalPrimeBand
import Erdos536.BernoulliSquarefree
import Erdos536.QuadraticPrimeBand

/-!
# Concrete growing prime-band prefix profiles

This file instantiates the finite categorical profile estimate on the broad
prime band

`T < p ≤ ceil (exp T)`.

The analytic point is uniform in the checked depth.  If the lower endpoint
at depth `d` is still at least `T`, then Mertens' two-endpoint error is
controlled by the single cutoff `T`.  Rounding the exponential endpoint
costs only `O(1 / log T)`, again independently of `d`.
-/

open scoped BigOperators
open Finset Filter Topology Set

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- The copy of a depth band inside the broad-band subtype. -/
def broadDepthBandCarrier (T : ℕ) (b d : ℝ) :
    Finset ↥(broadPrimeBand T 1) :=
  Finset.univ.filter fun p ↦ p.1 ∈ depthPrimeBand T b d

@[simp]
theorem mem_broadDepthBandCarrier
    {T : ℕ} {b d : ℝ} {p : ↥(broadPrimeBand T 1)} :
    p ∈ broadDepthBandCarrier T b d ↔
      p.1 ∈ depthPrimeBand T b d := by
  simp [broadDepthBandCarrier]

private theorem depthPrimeBand_subset_broad_of_lower
    {T : ℕ} {b d : ℝ}
    (hb : 0 ≤ b)
    (hlower : T ≤ expEndpoint (depthCoordinate d) T) :
    depthPrimeBand T b d ⊆ broadPrimeBand T 1 := by
  intro p hp
  have hp' := mem_depthPrimeBand.mp hp
  apply mem_broadPrimeBand.mpr
  refine ⟨hp'.1, hlower.trans_lt hp'.2.1, ?_⟩
  have hcoord : depthCoordinate b ≤ 1 := by
    unfold depthCoordinate
    rw [Real.exp_le_one_iff]
    linarith
  exact hp'.2.2.trans (expEndpoint_mono hcoord T)

/-- Every point of a rounded depth band belongs to the corresponding
normalized-depth prefix.  Only the lower endpoint is used, so the harmless
rounded upper endpoint causes no problem here. -/
theorem broadDepthBandCarrier_subset_depthPrefix
    {T : ℕ} {b d : ℝ}
    (hT : 0 < T) :
    broadDepthBandCarrier T b d ⊆
      fiveDepthPrefixCarrier (broadPrimeBand T 1)
        (normalizedLogDepth (T : ℝ)) d := by
  intro p hp
  have hpBand := mem_broadDepthBandCarrier.mp hp
  have hp' := mem_depthPrimeBand.mp hpBand
  rw [mem_fiveDepthPrefixCarrier]
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hEndpointPos :
      (0 : ℝ) < expEndpoint (depthCoordinate d) T := by
    exact_mod_cast
      (Nat.ceil_pos.mpr
        (Real.exp_pos ((T : ℝ) * depthCoordinate d)))
  have hEndpointLt :
      (expEndpoint (depthCoordinate d) T : ℝ) < (p.1 : ℝ) := by
    exact_mod_cast hp'.2.1
  have hlogEndpointLt :
      Real.log (expEndpoint (depthCoordinate d) T : ℝ) <
        Real.log (p.1 : ℝ) :=
    Real.log_lt_log hEndpointPos hEndpointLt
  have hlogEndpointLower :
      (T : ℝ) * depthCoordinate d ≤
        Real.log (expEndpoint (depthCoordinate d) T : ℝ) := by
    simpa only [LocalPrimeBand.localLowerEndpoint] using
      LocalPrimeBand.localLowerEndpoint_log_lower
        T (depthCoordinate d)
  have hcoord :
      depthCoordinate d <
        normalizedLogWeight (T : ℝ) p.1 := by
    rw [normalizedLogWeight]
    apply (lt_div_iff₀ hTR).2
    nlinarith
  have hlogcoord :
      Real.log (depthCoordinate d) <
        Real.log (normalizedLogWeight (T : ℝ) p.1) :=
    Real.log_lt_log (depthCoordinate_pos d) hcoord
  unfold normalizedLogDepth
  unfold depthCoordinate at hlogcoord
  rw [Real.log_exp] at hlogcoord
  linarith

private theorem subtypeSupportVal_broadDepthBandCarrier
    {T : ℕ} {b d : ℝ}
    (hb : 0 ≤ b)
    (hlower : T ≤ expEndpoint (depthCoordinate d) T) :
    subtypeSupportVal (broadDepthBandCarrier T b d) =
      depthPrimeBand T b d := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpBroad, hpCarrier⟩ :=
      mem_subtypeSupportVal.mp hp
    exact mem_broadDepthBandCarrier.mp hpCarrier
  · intro hp
    have hpBroad :=
      depthPrimeBand_subset_broad_of_lower hb hlower hp
    exact mem_subtypeSupportVal.mpr
      ⟨hpBroad, mem_broadDepthBandCarrier.mpr hp⟩

/-- The subtype sum on the broad band is exactly the shifted harmonic mass
of the underlying depth band. -/
theorem broadDepthBandCarrier_intensity_eq
    {T : ℕ} {b d : ℝ}
    (hb : 0 ≤ b) (hbd : b ≤ d)
    (hlower : T ≤ expEndpoint (depthCoordinate d) T) :
    (∑ p ∈ broadDepthBandCarrier T b d,
        reciprocalBernoulli p.1 / 3) =
      depthBandOneThirdIntensity T b d := by
  have hval :=
    subtypeSupportVal_broadDepthBandCarrier hb hlower
  have hsum :
      (∑ p ∈ broadDepthBandCarrier T b d,
          1 / ((p.1 : ℝ) + 1)) =
        ∑ p ∈ depthPrimeBand T b d,
          1 / ((p : ℝ) + 1) := by
    rw [← hval, subtypeSupportVal, Finset.sum_map]
    rfl
  rw [depthBandOneThirdIntensity,
    depthBandShiftedMass_eq_sum hbd]
  simp only [reciprocalBernoulli]
  rw [← Finset.sum_div]
  exact congrArg (fun x : ℝ ↦ x / 3) hsum

/-- Uniform lower bound for the logarithmic-logarithmic span of a rounded
depth interval.  The hypothesis says that the lower rounded endpoint has
not yet passed below the independent cutoff `L`. -/
theorem depthEndpointLogLogSpan_lower
    {N L n : ℕ} {b : ℝ}
    (hN : 0 < N) (hL : 3 ≤ L)
    (hlower :
      L ≤ expEndpoint
        (depthCoordinate (b + (n : ℝ))) N) :
    (n : ℝ) -
        1 / Real.log ((L : ℝ) - 1) ≤
      Real.log
          (Real.log
            (expEndpoint (depthCoordinate b) N : ℝ)) -
        Real.log
          (Real.log
            (expEndpoint
              (depthCoordinate (b + (n : ℝ))) N : ℝ)) := by
  let x : ℝ :=
    (N : ℝ) * depthCoordinate (b + (n : ℝ))
  let A : ℕ :=
    expEndpoint (depthCoordinate (b + (n : ℝ))) N
  let Y : ℕ := expEndpoint (depthCoordinate b) N
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLm1 : (1 : ℝ) < (L : ℝ) - 1 := by
    have hLR3 : (3 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hlogLm1 : 0 < Real.log ((L : ℝ) - 1) :=
    Real.log_pos hLm1
  have hAposN : 0 < A := by
    dsimp [A]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hYposN : 0 < Y := by
    dsimp [Y]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAposN
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast hYposN
  have hLA : (L : ℝ) ≤ (A : ℝ) := by
    exact_mod_cast hlower
  have hlogLpos : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogApos : 0 < Real.log (A : ℝ) := by
    have hLR : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    exact hlogLpos.trans_le (Real.log_le_log hLR hLA)
  have hcoordb : 0 < depthCoordinate b :=
    depthCoordinate_pos b
  have hcoordd : 0 < depthCoordinate (b + (n : ℝ)) :=
    depthCoordinate_pos _
  have hxpos : 0 < x := mul_pos hNR hcoordd
  have hlogYlower :
      Real.log ((N : ℝ) * depthCoordinate b) ≤
        Real.log (Real.log (Y : ℝ)) := by
    have hraw :
        (N : ℝ) * depthCoordinate b ≤
          Real.log (Y : ℝ) := by
      dsimp [Y]
      simpa only [LocalPrimeBand.localLowerEndpoint] using
        LocalPrimeBand.localLowerEndpoint_log_lower
          N (depthCoordinate b)
    exact Real.log_le_log (mul_pos hNR hcoordb) hraw
  have hlogAupper :
      Real.log (A : ℝ) <
        x + 1 := by
    dsimp [A, x]
    simpa only [LocalPrimeBand.localLowerEndpoint] using
      LocalPrimeBand.localLowerEndpoint_log_upper
        N (show 0 ≤ depthCoordinate (b + (n : ℝ)) by
          exact hcoordd.le)
  have houterA :
      Real.log (Real.log (A : ℝ)) ≤
        Real.log (x + 1) := by
    exact (Real.log_lt_log hlogApos hlogAupper).le
  have hceil :
      (A : ℝ) < Real.exp x + 1 := by
    dsimp [A, x]
    exact_mod_cast
      (Nat.ceil_lt_add_one
        (Real.exp_nonneg
          ((N : ℝ) *
            depthCoordinate (b + (n : ℝ)))))
  have hExpLower :
      (L : ℝ) - 1 < Real.exp x := by
    linarith
  have hxLower :
      Real.log ((L : ℝ) - 1) < x := by
    have hlog := Real.log_lt_log (by linarith [hLm1]) hExpLower
    rw [Real.log_exp] at hlog
    exact hlog
  have hround :
      Real.log (x + 1) - Real.log x ≤ 1 / x := by
    have hratioPos : 0 < (x + 1) / x := by positivity
    have hbase := Real.log_le_sub_one_of_pos hratioPos
    rw [Real.log_div (by positivity) hxpos.ne'] at hbase
    calc
      Real.log (x + 1) - Real.log x ≤
          (x + 1) / x - 1 := hbase
      _ = 1 / x := by
        field_simp [hxpos.ne']
        ring
  have hinv :
      1 / x ≤ 1 / Real.log ((L : ℝ) - 1) :=
    one_div_le_one_div_of_le hlogLm1 hxLower.le
  have hideal :
      Real.log ((N : ℝ) * depthCoordinate b) -
          Real.log x =
        (n : ℝ) := by
    dsimp [x]
    rw [Real.log_mul hNR.ne' hcoordb.ne',
      Real.log_mul hNR.ne' hcoordd.ne']
    unfold depthCoordinate
    rw [Real.log_exp, Real.log_exp]
    ring
  calc
    (n : ℝ) - 1 / Real.log ((L : ℝ) - 1) ≤
        (n : ℝ) - 1 / x :=
      sub_le_sub_left hinv _
    _ = Real.log ((N : ℝ) * depthCoordinate b) -
          Real.log x - 1 / x := by rw [hideal]
    _ ≤ Real.log ((N : ℝ) * depthCoordinate b) -
          Real.log (x + 1) := by
      linarith
    _ ≤ Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) :=
      sub_le_sub hlogYlower houterA
    _ = _ := by rfl

/-- Quantitative Mertens lower bound, uniform in the base depth and the
integer depth increment.  All errors depend only on the independent lower
cutoff `L`, not on the checked horizon. -/
theorem depthBandShiftedMass_lower_quantitative
    {N L n X₀ : ℕ} {b C : ℝ}
    (hN : 0 < N) (hL : 3 ≤ L) (hC : 0 ≤ C)
    (hcut : X₀ ≤ L)
    (hlower :
      L ≤ expEndpoint
        (depthCoordinate (b + (n : ℝ))) N)
    (hquad : ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3) :
    (n : ℝ) -
          (1 / Real.log ((L : ℝ) - 1) +
            5 * C / Real.log (L : ℝ) ^ 3 +
            1 / (L : ℝ)) ≤
      depthBandShiftedMass N b (b + (n : ℝ)) := by
  let A : ℕ :=
    expEndpoint (depthCoordinate (b + (n : ℝ))) N
  let Y : ℕ := expEndpoint (depthCoordinate b) N
  have hbd : b ≤ b + (n : ℝ) :=
    le_add_of_nonneg_right (Nat.cast_nonneg n)
  have hAY : A ≤ Y := by
    dsimp [A, Y]
    exact expEndpoint_mono (depthCoordinate_antitone hbd) N
  have hXA : X₀ ≤ A := hcut.trans hlower
  have hLA : L ≤ A := hlower
  have hLposN : 0 < L := by omega
  have hAposN : 0 < A := hLposN.trans_le hLA
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hLposN
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAposN
  have hlogLpos : 0 < Real.log (L : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hlogLA :
      Real.log (L : ℝ) ≤ Real.log (A : ℝ) := by
    exact Real.log_le_log hLpos (by exact_mod_cast hLA)
  have hmain :=
    depthEndpointLogLogSpan_lower
      (b := b) hN hL hlower
  have hquadrature := hquad A Y hXA hAY
  have hunshifted :
      Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) -
          5 * C / Real.log (A : ℝ) ^ 3 ≤
        fullReciprocalSum Y - fullReciprocalSum A := by
    rw [abs_le] at hquadrature
    linarith
  have hshiftRaw :=
    reciprocal_interval_sub_shifted_abs_le
      A Y hAposN hAY
  have hshifted :
      (fullReciprocalSum Y - fullReciprocalSum A) -
          1 / (A : ℝ) ≤
        fullShiftedReciprocalSum Y -
          fullShiftedReciprocalSum A := by
    rw [abs_le] at hshiftRaw
    linarith
  have hquadError :
      5 * C / Real.log (A : ℝ) ^ 3 ≤
        5 * C / Real.log (L : ℝ) ^ 3 := by
    have hnum : 0 ≤ 5 * C := mul_nonneg (by norm_num) hC
    exact div_le_div_of_nonneg_left hnum
      (pow_pos hlogLpos 3)
      (pow_le_pow_left₀ hlogLpos.le hlogLA 3)
  have hshiftError :
      1 / (A : ℝ) ≤ 1 / (L : ℝ) :=
    one_div_le_one_div_of_le hLpos
      (by exact_mod_cast hLA)
  calc
    (n : ℝ) -
          (1 / Real.log ((L : ℝ) - 1) +
            5 * C / Real.log (L : ℝ) ^ 3 +
            1 / (L : ℝ)) ≤
        (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ))) -
          5 * C / Real.log (A : ℝ) ^ 3 -
          1 / (A : ℝ) := by
      linarith
    _ ≤ (fullReciprocalSum Y -
          fullReciprocalSum A) - 1 / (A : ℝ) := by
      linarith
    _ ≤ fullShiftedReciprocalSum Y -
          fullShiftedReciprocalSum A :=
      hshifted
    _ = depthBandShiftedMass N b (b + (n : ℝ)) := by
      rfl

/-! ## The quadratic-scale band -/

/-- The corrected prime band: normalized scale `T²`, with polynomial
lower prime cutoff `T⁶`. -/
def quadraticProfilePrimeBand (T : ℕ) : Finset ℕ :=
  quadraticPrimeBand T 1

@[simp]
theorem mem_quadraticProfilePrimeBand {T p : ℕ} :
    p ∈ quadraticProfilePrimeBand T ↔
      p.Prime ∧ quadraticLowerCutoff T < p ∧
        p ≤ expEndpoint 1 (T ^ 2) := by
  simpa only [quadraticProfilePrimeBand] using
    (mem_quadraticPrimeBand (T := T) (p := p) (a := (1 : ℝ)))

/-- A rounded depth band, viewed in the quadratic-scale ground set. -/
def quadraticDepthBandCarrier (T : ℕ) (b d : ℝ) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  Finset.univ.filter fun p ↦
    p.1 ∈ depthPrimeBand (T ^ 2) b d

@[simp]
theorem mem_quadraticDepthBandCarrier
    {T : ℕ} {b d : ℝ}
    {p : ↥(quadraticProfilePrimeBand T)} :
    p ∈ quadraticDepthBandCarrier T b d ↔
      p.1 ∈ depthPrimeBand (T ^ 2) b d := by
  simp [quadraticDepthBandCarrier]

private theorem depthPrimeBand_subset_quadratic
    {T : ℕ} {b d : ℝ}
    (hb : 0 ≤ b)
    (hlower :
      quadraticLowerCutoff T ≤
        expEndpoint (depthCoordinate d) (T ^ 2)) :
    depthPrimeBand (T ^ 2) b d ⊆
      quadraticProfilePrimeBand T := by
  intro p hp
  have hp' := mem_depthPrimeBand.mp hp
  apply mem_quadraticProfilePrimeBand.mpr
  refine ⟨hp'.1, hlower.trans_lt hp'.2.1, ?_⟩
  have hcoord : depthCoordinate b ≤ 1 := by
    unfold depthCoordinate
    rw [Real.exp_le_one_iff]
    linarith
  exact hp'.2.2.trans
    (expEndpoint_mono hcoord (T ^ 2))

/-- The quadratic depth-band carrier is contained in its normalized-depth
prefix at scale `T²`. -/
theorem quadraticDepthBandCarrier_subset_depthPrefix
    {T : ℕ} {b d : ℝ} (hT : 0 < T) :
    quadraticDepthBandCarrier T b d ⊆
      fiveDepthPrefixCarrier (quadraticProfilePrimeBand T)
        (normalizedLogDepth ((T ^ 2 : ℕ) : ℝ)) d := by
  intro p hp
  have hpBand := mem_quadraticDepthBandCarrier.mp hp
  have hp' := mem_depthPrimeBand.mp hpBand
  rw [mem_fiveDepthPrefixCarrier]
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hEndpointPos :
      (0 : ℝ) <
        expEndpoint (depthCoordinate d) (T ^ 2) := by
    exact_mod_cast
      (Nat.ceil_pos.mpr
        (Real.exp_pos
          (((T ^ 2 : ℕ) : ℝ) * depthCoordinate d)))
  have hEndpointLt :
      (expEndpoint (depthCoordinate d) (T ^ 2) : ℝ) <
        (p.1 : ℝ) := by
    exact_mod_cast hp'.2.1
  have hlogEndpointLt :
      Real.log
          (expEndpoint (depthCoordinate d) (T ^ 2) : ℝ) <
        Real.log (p.1 : ℝ) :=
    Real.log_lt_log hEndpointPos hEndpointLt
  have hlogEndpointLower :
      ((T ^ 2 : ℕ) : ℝ) * depthCoordinate d ≤
        Real.log
          (expEndpoint (depthCoordinate d) (T ^ 2) : ℝ) := by
    simpa only [LocalPrimeBand.localLowerEndpoint] using
      LocalPrimeBand.localLowerEndpoint_log_lower
        (T ^ 2) (depthCoordinate d)
  have hcoord :
      depthCoordinate d <
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 := by
    rw [normalizedLogWeight]
    apply (lt_div_iff₀ hNR).2
    nlinarith
  have hlogcoord :
      Real.log (depthCoordinate d) <
        Real.log
          (normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1) :=
    Real.log_lt_log (depthCoordinate_pos d) hcoord
  unfold normalizedLogDepth
  unfold depthCoordinate at hlogcoord
  rw [Real.log_exp] at hlogcoord
  linarith

/-- Integer rounding at the upper endpoint costs only one logarithmic
unit.  Hence, whenever `a < b`, every carrier starting at depth `b`
eventually lies strictly deeper than `a`, uniformly in its lower
endpoint. -/
theorem eventually_quadraticDepthBandCarrier_depth_gt
    {a b : ℝ} (hab : a < b) :
    ∀ᶠ T : ℕ in atTop, ∀ d : ℝ,
      ∀ p ∈ quadraticDepthBandCarrier T b d,
        a <
          normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p.1 := by
  have hcoordinate :
      0 < depthCoordinate a - depthCoordinate b := by
    unfold depthCoordinate
    rw [sub_pos, Real.exp_lt_exp]
    linarith
  have hpowNat :
      Tendsto (fun T : ℕ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpowReal :
      Tendsto (fun T : ℕ => ((T ^ 2 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hgap :
      Tendsto
        (fun T : ℕ =>
          ((T ^ 2 : ℕ) : ℝ) *
            (depthCoordinate a - depthCoordinate b))
        atTop atTop := by
    have h :=
      hpowReal.const_mul_atTop hcoordinate
    simpa only [mul_comm] using h
  filter_upwards [
      hgap.eventually (eventually_gt_atTop 1),
      eventually_gt_atTop 0] with T hgapT hT
  intro d p hp
  have hpBand := mem_quadraticDepthBandCarrier.mp hp
  have hp' := mem_depthPrimeBand.mp hpBand
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hpR : (0 : ℝ) < p.1 := by
    exact_mod_cast hp'.1.pos
  have hpEndpoint :
      (p.1 : ℝ) ≤
        expEndpoint (depthCoordinate b) (T ^ 2) := by
    exact_mod_cast hp'.2.2
  have hlogpEndpoint :
      Real.log (p.1 : ℝ) ≤
        Real.log
          (expEndpoint (depthCoordinate b) (T ^ 2) : ℝ) :=
    Real.log_le_log hpR hpEndpoint
  have hlogEndpoint :
      Real.log
          (expEndpoint (depthCoordinate b) (T ^ 2) : ℝ) <
        ((T ^ 2 : ℕ) : ℝ) * depthCoordinate b + 1 := by
    simpa only [LocalPrimeBand.localLowerEndpoint] using
      LocalPrimeBand.localLowerEndpoint_log_upper
        (T ^ 2) (show 0 ≤ depthCoordinate b by
          exact (depthCoordinate_pos b).le)
  have hlogp :
      Real.log (p.1 : ℝ) <
        ((T ^ 2 : ℕ) : ℝ) * depthCoordinate a := by
    calc
      _ ≤ Real.log
          (expEndpoint (depthCoordinate b) (T ^ 2) : ℝ) :=
        hlogpEndpoint
      _ < ((T ^ 2 : ℕ) : ℝ) * depthCoordinate b + 1 :=
        hlogEndpoint
      _ < ((T ^ 2 : ℕ) : ℝ) * depthCoordinate a := by
        nlinarith
  have hweight :
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 <
        depthCoordinate a := by
    rw [normalizedLogWeight]
    apply (div_lt_iff₀ hNR).2
    simpa only [mul_comm] using hlogp
  have hlogpPos :
      0 < Real.log (p.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast hp'.1.one_lt)
  have hweightPos :
      0 <
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 := by
    rw [normalizedLogWeight]
    exact div_pos hlogpPos hNR
  have hlogweight :
      Real.log
          (normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1) <
        Real.log (depthCoordinate a) :=
    Real.log_lt_log hweightPos hweight
  unfold normalizedLogDepth
  unfold depthCoordinate at hlogweight
  rw [Real.log_exp] at hlogweight
  linarith

private theorem subtypeSupportVal_quadraticDepthBandCarrier
    {T : ℕ} {b d : ℝ}
    (hb : 0 ≤ b)
    (hlower :
      quadraticLowerCutoff T ≤
        expEndpoint (depthCoordinate d) (T ^ 2)) :
    subtypeSupportVal (quadraticDepthBandCarrier T b d) =
      depthPrimeBand (T ^ 2) b d := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpGround, hpCarrier⟩ :=
      mem_subtypeSupportVal.mp hp
    exact mem_quadraticDepthBandCarrier.mp hpCarrier
  · intro hp
    have hpGround :=
      depthPrimeBand_subset_quadratic hb hlower hp
    exact mem_subtypeSupportVal.mpr
      ⟨hpGround, mem_quadraticDepthBandCarrier.mpr hp⟩

/-- Exact shifted intensity of the quadratic-scale carrier. -/
theorem quadraticDepthBandCarrier_intensity_eq
    {T : ℕ} {b d : ℝ}
    (hb : 0 ≤ b) (hbd : b ≤ d)
    (hlower :
      quadraticLowerCutoff T ≤
        expEndpoint (depthCoordinate d) (T ^ 2)) :
    (∑ p ∈ quadraticDepthBandCarrier T b d,
        reciprocalBernoulli p.1 / 3) =
      depthBandOneThirdIntensity (T ^ 2) b d := by
  have hval :=
    subtypeSupportVal_quadraticDepthBandCarrier hb hlower
  have hsum :
      (∑ p ∈ quadraticDepthBandCarrier T b d,
          1 / ((p.1 : ℝ) + 1)) =
        ∑ p ∈ depthPrimeBand (T ^ 2) b d,
          1 / ((p : ℝ) + 1) := by
    rw [← hval, subtypeSupportVal, Finset.sum_map]
    rfl
  rw [depthBandOneThirdIntensity,
    depthBandShiftedMass_eq_sum hbd]
  simp only [reciprocalBernoulli]
  rw [← Finset.sum_div]
  exact congrArg (fun x : ℝ ↦ x / 3) hsum

/-- The uniform error appearing in the growing-depth Mertens estimate. -/
def depthProfileMertensError (C : ℝ) (L : ℕ) : ℝ :=
  1 / Real.log ((L : ℝ) - 1) +
    5 * C / Real.log (L : ℝ) ^ 3 +
    1 / (L : ℝ)

theorem quadraticDepthProfileMertensError_tendsto_zero (C : ℝ) :
    Tendsto
      (fun T : ℕ ↦
        depthProfileMertensError C (quadraticLowerCutoff T))
      atTop (𝓝 0) := by
  have hL :
      Tendsto (fun T : ℕ ↦ (quadraticLowerCutoff T : ℝ))
        atTop atTop := by
    have hpowNat :
        Tendsto (fun T : ℕ ↦ T ^ 6) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)
    simpa only [quadraticLowerCutoff] using
      tendsto_natCast_atTop_atTop.comp hpowNat
  have hLm1 :
      Tendsto
        (fun T : ℕ ↦ (quadraticLowerCutoff T : ℝ) - 1)
        atTop atTop := by
    simpa only [sub_eq_add_neg] using
      tendsto_atTop_add_const_right atTop (-1 : ℝ) hL
  have hlogLm1 :
      Tendsto
        (fun T : ℕ ↦
          Real.log ((quadraticLowerCutoff T : ℝ) - 1))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hLm1
  have hfirst :
      Tendsto
        (fun T : ℕ ↦
          1 / Real.log ((quadraticLowerCutoff T : ℝ) - 1))
        atTop (𝓝 0) :=
    hlogLm1.const_div_atTop 1
  have hlogL :
      Tendsto
        (fun T : ℕ ↦
          Real.log (quadraticLowerCutoff T : ℝ))
        atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hlogCube :
      Tendsto
        (fun T : ℕ ↦
          Real.log (quadraticLowerCutoff T : ℝ) ^ 3)
        atTop atTop := by
    simpa [Function.comp_def, Real.rpow_natCast] using
      (tendsto_rpow_atTop
        (by norm_num : (0 : ℝ) < 3)).comp hlogL
  have hsecond :
      Tendsto
        (fun T : ℕ ↦
          5 * C / Real.log (quadraticLowerCutoff T : ℝ) ^ 3)
        atTop (𝓝 0) :=
    hlogCube.const_div_atTop (5 * C)
  have hthird :
      Tendsto
        (fun T : ℕ ↦ 1 / (quadraticLowerCutoff T : ℝ))
        atTop (𝓝 0) :=
    hL.const_div_atTop 1
  simpa only [depthProfileMertensError, zero_add] using
    (hfirst.add hsecond).add hthird

/-- Uniform growing-horizon intensity lower bound on the corrected
quadratic prime band. -/
theorem eventually_quadraticDepthBandCarrier_intensity_lower
    {b epsilon : ℝ} (hb : 0 ≤ b) (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ n : ℕ,
      quadraticLowerCutoff T ≤
          expEndpoint
            (depthCoordinate (b + (n : ℝ))) (T ^ 2) →
        (n : ℝ) / 3 - epsilon ≤
          ∑ p ∈ quadraticDepthBandCarrier
              T b (b + (n : ℝ)),
            reciprocalBernoulli p.1 / 3 := by
  obtain ⟨C, hC, X₀, hquad⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  have herror :
      ∀ᶠ T : ℕ in atTop,
        depthProfileMertensError C (quadraticLowerCutoff T) <
          3 * epsilon := by
    exact
      (quadraticDepthProfileMertensError_tendsto_zero C).eventually
        (Iio_mem_nhds (mul_pos (by norm_num) hepsilon))
  have hcut :
      ∀ᶠ T : ℕ in atTop,
        X₀ ≤ quadraticLowerCutoff T := by
    have hpow :
        Tendsto quadraticLowerCutoff atTop atTop := by
      simpa only [quadraticLowerCutoff] using
        (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0))
    exact hpow.eventually (eventually_ge_atTop X₀)
  have hlarge :
      ∀ᶠ T : ℕ in atTop,
        0 < T ∧ 3 ≤ quadraticLowerCutoff T := by
    filter_upwards [
      eventually_gt_atTop 0,
      (show Tendsto quadraticLowerCutoff atTop atTop by
        simpa only [quadraticLowerCutoff] using
          (tendsto_pow_atTop
            (by norm_num : (6 : ℕ) ≠ 0))).eventually
        (eventually_ge_atTop 3)] with T hT hL
    exact ⟨hT, hL⟩
  filter_upwards [herror, hcut, hlarge] with
      T herrorT hcutT hlargeT
  intro n hlower
  have hN : 0 < T ^ 2 := pow_pos hlargeT.1 _
  have hmass :=
    depthBandShiftedMass_lower_quantitative
      (N := T ^ 2) (L := quadraticLowerCutoff T)
      (n := n) (b := b)
      hN hlargeT.2 hC.le hcutT hlower hquad
  have heq :=
    quadraticDepthBandCarrier_intensity_eq
      hb (le_add_of_nonneg_right (Nat.cast_nonneg n)) hlower
  rw [heq]
  unfold depthBandOneThirdIntensity
  dsimp [depthProfileMertensError] at herrorT
  linarith

/-! ## Explicit integer profile at base depth 75 -/

/-- The full checked depth corresponding to residual index `n`. -/
def quadraticProfileDepth (n : ℕ) : ℝ :=
  (75 + n : ℕ)

/-- The manuscript's full lower-prefix threshold at depth `75+n`. -/
def quadraticFullProfileThreshold (n : ℕ) : ℕ :=
  (8 * (75 + n)) / 25

/-- A finite set of horizon-valid checks.  The auxiliary horizon `H` is
arbitrary; all estimates below are independent of it. -/
def quadraticProfileChecks (T H : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).filter fun n ↦
    quadraticLowerCutoff T ≤
      expEndpoint
        (depthCoordinate (quadraticProfileDepth n)) (T ^ 2)

@[simp]
theorem mem_quadraticProfileChecks {T H n : ℕ} :
    n ∈ quadraticProfileChecks T H ↔
      n < H + 1 ∧
      quadraticLowerCutoff T ≤
        expEndpoint
          (depthCoordinate (quadraticProfileDepth n)) (T ^ 2) := by
  simp [quadraticProfileChecks]

theorem quadraticFullProfileThreshold_pos (n : ℕ) :
    0 < quadraticFullProfileThreshold n := by
  unfold quadraticFullProfileThreshold
  omega

theorem quadraticFullProfileThreshold_request (n : ℕ) :
    ((quadraticFullProfileThreshold n - 1 : ℕ) : ℝ) ≤
      (8 / 25 : ℝ) * (n : ℝ) - (-24 : ℝ) := by
  have hdiv :
      25 * quadraticFullProfileThreshold n ≤
        8 * (75 + n) := by
    unfold quadraticFullProfileThreshold
    exact Nat.mul_div_le _ _
  have hcast :
      (25 : ℝ) * quadraticFullProfileThreshold n ≤
        (8 : ℝ) * (75 + n) := by
    exact_mod_cast hdiv
  have hsub :
      ((quadraticFullProfileThreshold n - 1 : ℕ) : ℝ) ≤
        quadraticFullProfileThreshold n := by
    exact_mod_cast Nat.sub_le _ _
  norm_num at hcast ⊢
  nlinarith

theorem quadraticFullProfileThreshold_le (n : ℕ) :
    (quadraticFullProfileThreshold n : ℝ) ≤
      (8 / 25 : ℝ) * (n : ℝ) + 24 := by
  have hdiv :
      25 * quadraticFullProfileThreshold n ≤
        8 * (75 + n) := by
    unfold quadraticFullProfileThreshold
    exact Nat.mul_div_le _ _
  have hcast :
      (25 : ℝ) * quadraticFullProfileThreshold n ≤
        (8 : ℝ) * (75 + n) := by
    exact_mod_cast hdiv
  norm_num at hcast ⊢
  nlinarith

/-- Uniform concrete intensity estimate on every finite set of valid
quadratic-scale checks. -/
theorem eventually_quadraticProfilePrefixIntensity_lower
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ, ∀ n ∈ quadraticProfileChecks T H,
      (75 + n : ℕ) / 3 - epsilon ≤
        ∑ p ∈ fiveDepthPrefixCarrier
            (quadraticProfilePrimeBand T)
            (normalizedLogDepth ((T ^ 2 : ℕ) : ℝ))
            (quadraticProfileDepth n),
          reciprocalBernoulli p.1 / 3 := by
  have hband :=
    eventually_quadraticDepthBandCarrier_intensity_lower
      (b := (0 : ℝ)) (epsilon := epsilon)
      (by norm_num) hepsilon
  filter_upwards [hband, eventually_gt_atTop 0] with T hbandT hT
  intro H n hn
  have hlower :=
    (mem_quadraticProfileChecks.mp hn).2
  have hbandLower :=
    hbandT (75 + n) (by
      simpa [quadraticProfileDepth] using hlower)
  have hsubset :
      quadraticDepthBandCarrier T 0
          (quadraticProfileDepth n) ⊆
        fiveDepthPrefixCarrier
          (quadraticProfilePrimeBand T)
          (normalizedLogDepth ((T ^ 2 : ℕ) : ℝ))
          (quadraticProfileDepth n) := by
    exact quadraticDepthBandCarrier_subset_depthPrefix hT
  have hsum :
      (∑ p ∈ quadraticDepthBandCarrier T 0
          (quadraticProfileDepth n),
          reciprocalBernoulli p.1 / 3) ≤
        ∑ p ∈ fiveDepthPrefixCarrier
            (quadraticProfilePrimeBand T)
            (normalizedLogDepth ((T ^ 2 : ℕ) : ℝ))
            (quadraticProfileDepth n),
          reciprocalBernoulli p.1 / 3 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun p _hp _hnot ↦ by
        exact div_nonneg (reciprocalBernoulli_nonneg p.1)
          (by norm_num))
  have hbandLower' :
      (75 + n : ℕ) / 3 - epsilon ≤
        ∑ p ∈ quadraticDepthBandCarrier T 0
            (quadraticProfileDepth n),
          reciprocalBernoulli p.1 / 3 := by
    simpa [quadraticProfileDepth] using hbandLower
  exact hbandLower'.trans hsum

/-- Concrete finite categorical profile-failure bound.  It is uniform in
the auxiliary horizon `H` and in the quadratic scale once the Mertens
estimate has entered its eventual range. -/
theorem eventually_quadraticFullProfileFailureMass_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      fiveEventMass (quadraticProfilePrimeBand T)
          reciprocalBernoulli
          (fiveIndexedPrefixProfileFailure
            (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ)
            (quadraticProfileChecks T H)
            quadraticProfileDepth
            quadraticFullProfileThreshold) ≤
        4 * Real.exp
            (-(1 / 50 : ℝ) * (-24 : ℝ) +
              (1 - Real.exp (-(1 / 50 : ℝ))) *
                (epsilon - 25)) /
          (1 - Real.exp (-(1 / 10000 : ℝ))) := by
  have hintensity :=
    eventually_quadraticProfilePrefixIntensity_lower hepsilon
  filter_upwards [hintensity] with T hintensityT
  intro H
  apply fivePrefixProfileFailureMass_le_numerical
    (T := ((T ^ 2 : ℕ) : ℝ))
    (depth := quadraticProfileDepth)
    (epsilon := epsilon - 25) (buffer := (-24 : ℝ))
  · intro p _hp
    exact reciprocalBernoulli_nonneg p
  · intro p hp
    exact reciprocalBernoulli_le_three_quarters
      (quadraticPrimeBand_prime T 1 p hp).one_le
  · intro n hn
    exact quadraticFullProfileThreshold_pos n
  · intro n hn
    have h := hintensityT H n hn
    norm_num [quadraticProfileDepth] at h ⊢
    linarith
  · intro n _hn
    exact quadraticFullProfileThreshold_request n

/-! ## Residual tail after a large fixed buffer -/

/-- Extra stock installed before the growing residual profile. -/
def quadraticProfileBuffer : ℕ := 1000

/-- Total fixed stock: `floor((8/25)*75) + 1000 = 1024`. -/
def quadraticProfileFixedStock : ℕ := 1024

/-- Residual number of points needed after installing the fixed stock. -/
def quadraticResidualProfileThreshold (n : ℕ) : ℕ :=
  quadraticFullProfileThreshold n - quadraticProfileFixedStock

/-- Horizon-valid residual checks; zero residual requirements are omitted. -/
def quadraticResidualProfileChecks (T H : ℕ) : Finset ℕ :=
  (quadraticProfileChecks T H).filter fun n ↦
    0 < quadraticResidualProfileThreshold n

@[simp]
theorem mem_quadraticResidualProfileChecks {T H n : ℕ} :
    n ∈ quadraticResidualProfileChecks T H ↔
      n < H + 1 ∧
      quadraticLowerCutoff T ≤
        expEndpoint
          (depthCoordinate (quadraticProfileDepth n)) (T ^ 2) ∧
      0 < quadraticResidualProfileThreshold n := by
  simp [quadraticResidualProfileChecks, and_assoc]

/-- We start the residual carrier one full depth unit below the fixed
region.  The unit gap makes disjointness from depth `≤75` insensitive to
integer endpoint rounding. -/
def quadraticResidualCarrier (T n : ℕ) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  quadraticDepthBandCarrier T 76 (quadraticProfileDepth n)

theorem quadraticResidualProfileThreshold_pos_of_mem
    {T H n : ℕ} (hn : n ∈ quadraticResidualProfileChecks T H) :
    0 < quadraticResidualProfileThreshold n :=
  (mem_quadraticResidualProfileChecks.mp hn).2.2

theorem one_le_of_mem_quadraticResidualProfileChecks
    {T H n : ℕ} (hn : n ∈ quadraticResidualProfileChecks T H) :
    1 ≤ n := by
  have hpos :=
    quadraticResidualProfileThreshold_pos_of_mem hn
  unfold quadraticResidualProfileThreshold
    quadraticProfileFixedStock
    quadraticFullProfileThreshold at hpos
  omega

theorem quadraticResidualProfileThreshold_request
    {T H n : ℕ} (hn : n ∈ quadraticResidualProfileChecks T H) :
    ((quadraticResidualProfileThreshold n - 1 : ℕ) : ℝ) ≤
      (8 / 25 : ℝ) * (n : ℝ) - 1001 := by
  have hpos :=
    quadraticResidualProfileThreshold_pos_of_mem hn
  have hstock :
      quadraticProfileFixedStock ≤
        quadraticFullProfileThreshold n := by
    change
      0 < quadraticFullProfileThreshold n -
        quadraticProfileFixedStock at hpos
    omega
  have hcastSub :
      (quadraticResidualProfileThreshold n : ℝ) =
        quadraticFullProfileThreshold n -
          quadraticProfileFixedStock := by
    unfold quadraticResidualProfileThreshold
    rw [Nat.cast_sub hstock]
  have hsub :
      ((quadraticResidualProfileThreshold n - 1 : ℕ) : ℝ) =
        quadraticResidualProfileThreshold n - 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hpos.ne')]
    norm_num only [Nat.cast_one]
  rw [hsub, hcastSub]
  have hfull := quadraticFullProfileThreshold_le n
  change
    (quadraticFullProfileThreshold n : ℝ) - 1024 - 1 ≤
      (8 / 25 : ℝ) * (n : ℝ) - 1001
  linarith

/-- Residual-carrier intensity.  Its ideal mean is `(n-1)/3`, because the
carrier starts at depth `76` and ends at depth `75+n`. -/
theorem eventually_quadraticResidualCarrier_intensity_lower
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      ∀ n ∈ quadraticResidualProfileChecks T H,
        (n : ℝ) / 3 - (epsilon + 1 / 3) ≤
          ∑ p ∈ quadraticResidualCarrier T n,
            reciprocalBernoulli p.1 / 3 := by
  have hband :=
    eventually_quadraticDepthBandCarrier_intensity_lower
      (b := (76 : ℝ)) (epsilon := epsilon)
      (by norm_num) hepsilon
  filter_upwards [hband] with T hbandT
  intro H n hn
  have hn1 := one_le_of_mem_quadraticResidualProfileChecks hn
  have hlower :=
    (mem_quadraticResidualProfileChecks.mp hn).2.1
  have hdepthEq :
      (76 : ℝ) + ((n - 1 : ℕ) : ℝ) =
        quadraticProfileDepth n := by
    rw [Nat.cast_sub hn1]
    unfold quadraticProfileDepth
    push_cast
    ring
  have hpoint :=
    hbandT (n - 1) (by
      rw [hdepthEq]
      exact hlower)
  rw [hdepthEq] at hpoint
  have hcast :
      ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]
    norm_num only [Nat.cast_one]
  have hpoint' :
      ((n : ℝ) - 1) / 3 - epsilon ≤
        ∑ p ∈ quadraticResidualCarrier T n,
          reciprocalBernoulli p.1 / 3 := by
    simpa [quadraticResidualCarrier, hcast] using hpoint
  norm_num at hpoint' ⊢
  linarith

/-- Explicit residual failure bound with buffer `1000`. -/
theorem eventually_quadraticResidualProfileFailureMass_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      fiveEventMass (quadraticProfilePrimeBand T)
          reciprocalBernoulli
          (fiveIndexedCarrierProfileFailure
            (quadraticProfilePrimeBand T)
            (quadraticResidualProfileChecks T H)
            (quadraticResidualCarrier T)
            quadraticResidualProfileThreshold) ≤
        4 * Real.exp
            (-(1 / 50 : ℝ) * 1001 +
              (1 - Real.exp (-(1 / 50 : ℝ))) *
                (epsilon + 1 / 3)) /
          (1 - Real.exp (-(1 / 10000 : ℝ))) := by
  have hintensity :=
    eventually_quadraticResidualCarrier_intensity_lower hepsilon
  filter_upwards [hintensity] with T hintensityT
  intro H
  apply fiveCarrierProfileFailureMass_le_numerical
    (carrier := quadraticResidualCarrier T)
    (epsilon := epsilon + 1 / 3) (buffer := (1001 : ℝ))
  · intro p _hp
    exact reciprocalBernoulli_nonneg p
  · intro p hp
    exact reciprocalBernoulli_le_three_quarters
      (quadraticPrimeBand_prime T 1 p hp).one_le
  · intro n hn
    exact quadraticResidualProfileThreshold_pos_of_mem hn
  · intro n hn
    simpa [one_div, mul_comm] using hintensityT H n hn
  · intro n hn
    exact quadraticResidualProfileThreshold_request hn

/-! ## Delayed residual profile without shallow stock -/

/-- A long free depth interval supplies the buffer probabilistically,
without forcing any shallow prime configuration. -/
def quadraticDelayedProfileGap : ℕ := 2500

def quadraticDelayedProfileDepth (k : ℕ) : ℝ :=
  (76 + quadraticDelayedProfileGap + k : ℕ)

def quadraticDelayedProfileThreshold (k : ℕ) : ℕ :=
  (8 * k) / 25 + 1

def quadraticDelayedProfileChecks (T H : ℕ) : Finset ℕ :=
  (Finset.range (H + 1)).filter fun k ↦
    quadraticLowerCutoff T ≤
      expEndpoint
        (depthCoordinate (quadraticDelayedProfileDepth k)) (T ^ 2)

@[simp]
theorem mem_quadraticDelayedProfileChecks {T H k : ℕ} :
    k ∈ quadraticDelayedProfileChecks T H ↔
      k < H + 1 ∧
      quadraticLowerCutoff T ≤
        expEndpoint
          (depthCoordinate (quadraticDelayedProfileDepth k)) (T ^ 2) := by
  simp [quadraticDelayedProfileChecks]

def quadraticDelayedProfileCarrier (T k : ℕ) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  quadraticDepthBandCarrier T 76
    (quadraticDelayedProfileDepth k)

/-- The finite real depth grid consumed by `fivePrimeBandEvent`. -/
noncomputable def quadraticDelayedProfileDepths (T H : ℕ) :
    Finset ℝ :=
  (quadraticDelayedProfileChecks T H).image
    quadraticDelayedProfileDepth

/-- A total threshold on real depths.  On the delayed grid it recovers
the natural-index threshold exactly. -/
noncomputable def quadraticDelayedProfileThresholdAtDepth
    (d : ℝ) : ℕ :=
  quadraticDelayedProfileThreshold
    ⌊d - (76 + quadraticDelayedProfileGap : ℕ)⌋₊

/-- The first possible delayed-grid depth. -/
def quadraticDelayedProfileFirstDepth : ℝ :=
  quadraticDelayedProfileDepth 0

theorem quadraticDelayedProfileDepth_injective :
    Function.Injective quadraticDelayedProfileDepth := by
  intro k m h
  unfold quadraticDelayedProfileDepth at h
  have hnat :
      76 + quadraticDelayedProfileGap + k =
        76 + quadraticDelayedProfileGap + m := by
    exact_mod_cast h
  omega

@[simp]
theorem mem_quadraticDelayedProfileDepths
    {T H : ℕ} {d : ℝ} :
    d ∈ quadraticDelayedProfileDepths T H ↔
      ∃ k ∈ quadraticDelayedProfileChecks T H,
        quadraticDelayedProfileDepth k = d := by
  simp [quadraticDelayedProfileDepths]

@[simp]
theorem quadraticDelayedProfileThresholdAtDepth_eq
    (k : ℕ) :
    quadraticDelayedProfileThresholdAtDepth
        (quadraticDelayedProfileDepth k) =
      quadraticDelayedProfileThreshold k := by
  unfold quadraticDelayedProfileThresholdAtDepth
  have hsub :
      quadraticDelayedProfileDepth k -
          ((76 + quadraticDelayedProfileGap : ℕ) : ℝ) =
        (k : ℝ) := by
    unfold quadraticDelayedProfileDepth
    push_cast
    ring
  rw [hsub]
  simp

/-- The entire delayed carrier is eventually disjoint from every
normalized-depth prefix ending at depth `75`, uniformly in `k`. -/
theorem eventually_quadraticDelayedProfileCarrier_depth_gt_75 :
    ∀ᶠ T : ℕ in atTop, ∀ k : ℕ,
      ∀ p ∈ quadraticDelayedProfileCarrier T k,
        75 <
          normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p.1 := by
  have hseparation :=
    eventually_quadraticDepthBandCarrier_depth_gt
      (a := (75 : ℝ)) (b := (76 : ℝ)) (by norm_num)
  filter_upwards [hseparation] with T hseparationT
  intro k
  simpa only [quadraticDelayedProfileCarrier] using
    hseparationT (quadraticDelayedProfileDepth k)

/-- Boolean success of the carrier profile implies the full prefix-count
clause required by `fivePrimeBandEvent` on the real delayed grid. -/
theorem quadraticDelayedProfileSuccess_prefix
    {T H : ℕ} (hT : 0 < T)
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    (hsuccess :
      fiveIndexedCarrierProfileFailure
        (quadraticProfilePrimeBand T)
        (quadraticDelayedProfileChecks T H)
        (quadraticDelayedProfileCarrier T)
        quadraticDelayedProfileThreshold c = false) :
    ∀ l : ActiveFiveLabel,
      ∀ d : ↥(quadraticDelayedProfileDepths T H),
        quadraticDelayedProfileThresholdAtDepth d.1 ≤
          fiveLabelPrefixCount
            (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ) c l d.1 := by
  intro l d
  obtain ⟨k, hk, hdepth⟩ :=
    mem_quadraticDelayedProfileDepths.mp d.2
  rw [← hdepth]
  rw [quadraticDelayedProfileThresholdAtDepth_eq]
  have hcount :
      quadraticDelayedProfileThreshold k ≤
        fiveActiveLabelCountOn
          (quadraticDelayedProfileCarrier T k) l c := by
    by_contra hnot
    have hlt :
        fiveActiveLabelCountOn
            (quadraticDelayedProfileCarrier T k) l c <
          quadraticDelayedProfileThreshold k :=
      Nat.lt_of_not_ge hnot
    have hfailure :
        fiveIndexedCarrierProfileFailure
          (quadraticProfilePrimeBand T)
          (quadraticDelayedProfileChecks T H)
          (quadraticDelayedProfileCarrier T)
          quadraticDelayedProfileThreshold c := by
      rw [fiveIndexedCarrierProfileFailure_iff]
      exact ⟨l, k, hk, hlt⟩
    simp [hsuccess] at hfailure
  have hsubset :
      quadraticDelayedProfileCarrier T k ⊆
        fiveDepthPrefixCarrier
          (quadraticProfilePrimeBand T)
          (normalizedLogDepth ((T ^ 2 : ℕ) : ℝ))
          (quadraticDelayedProfileDepth k) := by
    simpa only [quadraticDelayedProfileCarrier] using
      (quadraticDepthBandCarrier_subset_depthPrefix
        (b := (76 : ℝ))
        (d := quadraticDelayedProfileDepth k) hT)
  have hcountMono :
      fiveActiveLabelCountOn
          (quadraticDelayedProfileCarrier T k) l c ≤
        fiveActiveLabelCountOn
          (fiveDepthPrefixCarrier
            (quadraticProfilePrimeBand T)
            (normalizedLogDepth ((T ^ 2 : ℕ) : ℝ))
            (quadraticDelayedProfileDepth k)) l c := by
    unfold fiveActiveLabelCountOn
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hsubset hp.1, hp.2⟩
  rw [fiveActiveLabelCountOn_depthPrefix] at hcountMono
  exact hcount.trans hcountMono

theorem zero_mem_quadraticDelayedProfileChecks_of_nonempty
    {T H : ℕ}
    (hchecks :
      (quadraticDelayedProfileChecks T H).Nonempty) :
    0 ∈ quadraticDelayedProfileChecks T H := by
  obtain ⟨k, hk⟩ := hchecks
  have hk' := mem_quadraticDelayedProfileChecks.mp hk
  rw [mem_quadraticDelayedProfileChecks]
  constructor
  · omega
  · have hdepth :
        quadraticDelayedProfileDepth 0 ≤
          quadraticDelayedProfileDepth k := by
      unfold quadraticDelayedProfileDepth
      exact_mod_cast (show
        76 + quadraticDelayedProfileGap + 0 ≤
          76 + quadraticDelayedProfileGap + k by omega)
    exact hk'.2.trans
      (expEndpoint_mono
        (depthCoordinate_antitone hdepth) (T ^ 2))

/-- If the natural check set is nonempty, its explicit first real depth
belongs to the event grid and has threshold exactly one. -/
theorem quadraticDelayedProfileFirstDepth_mem_and_threshold
    {T H : ℕ}
    (hchecks :
      (quadraticDelayedProfileChecks T H).Nonempty) :
    quadraticDelayedProfileFirstDepth ∈
        quadraticDelayedProfileDepths T H ∧
      quadraticDelayedProfileThresholdAtDepth
          quadraticDelayedProfileFirstDepth = 1 := by
  constructor
  · rw [mem_quadraticDelayedProfileDepths]
    exact
      ⟨0, zero_mem_quadraticDelayedProfileChecks_of_nonempty
        hchecks, rfl⟩
  · rw [quadraticDelayedProfileFirstDepth,
      quadraticDelayedProfileThresholdAtDepth_eq]
    rfl

theorem quadraticDelayedProfileThresholdAtFirstDepth :
    quadraticDelayedProfileThresholdAtDepth
        quadraticDelayedProfileFirstDepth = 1 := by
  rw [quadraticDelayedProfileFirstDepth,
    quadraticDelayedProfileThresholdAtDepth_eq]
  rfl

/-- The explicit first delayed check is eventually present, uniformly in
the chosen finite horizon. -/
theorem eventually_quadraticDelayedProfileFirstCheck :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      0 ∈ quadraticDelayedProfileChecks T H := by
  have hcutoff :=
    eventually_quadraticLowerCutoff_le_expEndpoint
      (depthCoordinate_pos (quadraticDelayedProfileDepth 0))
  filter_upwards [hcutoff] with T hcutoffT
  intro H
  rw [mem_quadraticDelayedProfileChecks]
  exact ⟨by omega, hcutoffT⟩

/-- Eventual collision-ready witness: the first real depth belongs to
every finite delayed grid and its total threshold is at least one. -/
theorem eventually_quadraticDelayedProfileFirstDepth :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      quadraticDelayedProfileFirstDepth ∈
          quadraticDelayedProfileDepths T H ∧
        1 ≤ quadraticDelayedProfileThresholdAtDepth
          quadraticDelayedProfileFirstDepth := by
  filter_upwards [
      eventually_quadraticDelayedProfileFirstCheck] with T hfirstT
  intro H
  constructor
  · rw [mem_quadraticDelayedProfileDepths]
    exact ⟨0, hfirstT H, rfl⟩
  · rw [quadraticDelayedProfileThresholdAtFirstDepth]

theorem quadraticDelayedProfileThreshold_pos (k : ℕ) :
    0 < quadraticDelayedProfileThreshold k := by
  unfold quadraticDelayedProfileThreshold
  omega

theorem quadraticDelayedProfileThreshold_request (k : ℕ) :
    ((quadraticDelayedProfileThreshold k - 1 : ℕ) : ℝ) ≤
      (8 / 25 : ℝ) * (k : ℝ) := by
  have hdiv :
      25 * ((8 * k) / 25) ≤ 8 * k :=
    Nat.mul_div_le _ _
  have hcast :
      (25 : ℝ) * ((8 * k) / 25 : ℕ) ≤
        (8 : ℝ) * k := by
    exact_mod_cast hdiv
  unfold quadraticDelayedProfileThreshold
  norm_num at hcast ⊢
  nlinarith

theorem eventually_quadraticDelayedCarrier_intensity_lower
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      ∀ k ∈ quadraticDelayedProfileChecks T H,
        (k : ℝ) / 3 -
            (epsilon - (quadraticDelayedProfileGap : ℝ) / 3) ≤
          ∑ p ∈ quadraticDelayedProfileCarrier T k,
            reciprocalBernoulli p.1 / 3 := by
  have hband :=
    eventually_quadraticDepthBandCarrier_intensity_lower
      (b := (76 : ℝ)) (epsilon := epsilon)
      (by norm_num) hepsilon
  filter_upwards [hband] with T hbandT
  intro H k hk
  have hlower :=
    (mem_quadraticDelayedProfileChecks.mp hk).2
  have hdepthEq :
      (76 : ℝ) +
          ((quadraticDelayedProfileGap + k : ℕ) : ℝ) =
        quadraticDelayedProfileDepth k := by
    unfold quadraticDelayedProfileDepth
    push_cast
    ring
  have hpoint :=
    hbandT (quadraticDelayedProfileGap + k) (by
      rw [hdepthEq]
      exact hlower)
  rw [hdepthEq] at hpoint
  have hpoint' :
      (((quadraticDelayedProfileGap : ℝ) + k) / 3) -
          epsilon ≤
        ∑ p ∈ quadraticDelayedProfileCarrier T k,
          reciprocalBernoulli p.1 / 3 := by
    simpa [quadraticDelayedProfileCarrier,
      Nat.cast_add] using hpoint
  linarith

/-- Delayed-profile failure estimate, uniform in the finite horizon. -/
theorem eventually_quadraticDelayedProfileFailureMass_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      fiveEventMass (quadraticProfilePrimeBand T)
          reciprocalBernoulli
          (fiveIndexedCarrierProfileFailure
            (quadraticProfilePrimeBand T)
            (quadraticDelayedProfileChecks T H)
            (quadraticDelayedProfileCarrier T)
            quadraticDelayedProfileThreshold) ≤
        4 * Real.exp
            ((1 - Real.exp (-(1 / 50 : ℝ))) *
              (epsilon -
                (quadraticDelayedProfileGap : ℝ) / 3)) /
          (1 - Real.exp (-(1 / 10000 : ℝ))) := by
  have hintensity :=
    eventually_quadraticDelayedCarrier_intensity_lower hepsilon
  filter_upwards [hintensity] with T hintensityT
  intro H
  have hmass :
      fiveEventMass (quadraticProfilePrimeBand T)
          reciprocalBernoulli
          (fiveIndexedCarrierProfileFailure
            (quadraticProfilePrimeBand T)
            (quadraticDelayedProfileChecks T H)
            (quadraticDelayedProfileCarrier T)
            quadraticDelayedProfileThreshold) ≤
        4 * Real.exp
            (-(1 / 50 : ℝ) * 0 +
              (1 - Real.exp (-(1 / 50 : ℝ))) *
                (epsilon -
                  (quadraticDelayedProfileGap : ℝ) / 3)) /
          (1 - Real.exp (-(1 / 10000 : ℝ))) := by
    apply fiveCarrierProfileFailureMass_le_numerical
      (carrier := quadraticDelayedProfileCarrier T)
      (epsilon :=
        epsilon - (quadraticDelayedProfileGap : ℝ) / 3)
      (buffer := (0 : ℝ))
    · intro p _hp
      exact reciprocalBernoulli_nonneg p
    · intro p hp
      exact reciprocalBernoulli_le_three_quarters
        (quadraticPrimeBand_prime T 1 p hp).one_le
    · intro k _hk
      exact quadraticDelayedProfileThreshold_pos k
    · intro k hk
      simpa [one_div, mul_comm] using hintensityT H k hk
    · intro k _hk
      simpa only [sub_zero] using
        quadraticDelayedProfileThreshold_request k
  simpa only [mul_zero, zero_add] using hmass

/-- With the fixed delay `2500`, the numerical profile tail is already
smaller than `1/8` for every intensity error at most one. -/
theorem quadraticDelayedProfileNumericalBound_lt_one_eighth
    {epsilon : ℝ} (hepsilon : epsilon ≤ 1) :
    4 * Real.exp
        ((1 - Real.exp (-(1 / 50 : ℝ))) *
          (epsilon -
            (quadraticDelayedProfileGap : ℝ) / 3)) /
      (1 - Real.exp (-(1 / 10000 : ℝ))) <
        1 / 8 := by
  have hexp50 :
      (1 : ℝ) + 1 / 50 ≤ Real.exp (1 / 50 : ℝ) := by
    simpa [add_comm] using Real.add_one_le_exp (1 / 50 : ℝ)
  have hinv50 :
      Real.exp (-(1 / 50 : ℝ)) ≤
        1 / ((1 : ℝ) + 1 / 50) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hexp50
  have htheta :
      (1 / 51 : ℝ) ≤
        1 - Real.exp (-(1 / 50 : ℝ)) := by
    norm_num at hinv50 ⊢
    linarith
  have hx :
      epsilon - (quadraticDelayedProfileGap : ℝ) / 3 ≤
        -(2497 / 3 : ℝ) := by
    norm_num [quadraticDelayedProfileGap] at *
    linarith
  have hx0 :
      epsilon - (quadraticDelayedProfileGap : ℝ) / 3 ≤ 0 := by
    linarith
  have hexponent :
      (1 - Real.exp (-(1 / 50 : ℝ))) *
          (epsilon -
            (quadraticDelayedProfileGap : ℝ) / 3) ≤
        -16 := by
    calc
      _ ≤ (1 / 51 : ℝ) *
          (epsilon -
            (quadraticDelayedProfileGap : ℝ) / 3) :=
        mul_le_mul_of_nonpos_right htheta hx0
      _ ≤ (1 / 51 : ℝ) * (-(2497 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hx (by norm_num)
      _ ≤ -16 := by norm_num
  have hexp10000 :
      (1 : ℝ) + 1 / 10000 ≤
        Real.exp (1 / 10000 : ℝ) := by
    simpa [add_comm] using
      Real.add_one_le_exp (1 / 10000 : ℝ)
  have hinv10000 :
      Real.exp (-(1 / 10000 : ℝ)) ≤
        1 / ((1 : ℝ) + 1 / 10000) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hexp10000
  have hden :
      (1 / 10001 : ℝ) ≤
        1 - Real.exp (-(1 / 10000 : ℝ)) := by
    norm_num at hinv10000 ⊢
    linarith
  have hdenpos :
      0 < 1 - Real.exp (-(1 / 10000 : ℝ)) := by
    linarith
  have hexp16 : (320032 : ℝ) < Real.exp 16 := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg (by norm_num) 12)
    simp_rw [Finset.sum_range_succ, Nat.factorial_succ]
    norm_num
  have hexpneg16 :
      Real.exp (-16) < (1 / 320032 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_lt_one_div_of_lt (by norm_num) hexp16
  have hexpbound :
      Real.exp
          ((1 - Real.exp (-(1 / 50 : ℝ))) *
            (epsilon -
              (quadraticDelayedProfileGap : ℝ) / 3)) <
        1 / 320032 := by
    exact (Real.exp_le_exp.mpr hexponent).trans_lt hexpneg16
  have hnum :
      4 * Real.exp
          ((1 - Real.exp (-(1 / 50 : ℝ))) *
            (epsilon -
              (quadraticDelayedProfileGap : ℝ) / 3)) <
        (1 / 8 : ℝ) * (1 / 10001 : ℝ) := by
    norm_num at hexpbound ⊢
    linarith
  apply (div_lt_iff₀ hdenpos).2
  exact hnum.trans_le
    (mul_le_mul_of_nonneg_left hden (by norm_num))

/-- Directly consumable delayed-profile estimate: eventually, and uniformly
in the finite checked horizon, the failure mass is less than `1/8`. -/
theorem eventually_quadraticDelayedProfileFailureMass_lt_one_eighth
    {epsilon : ℝ} (hepsilonPos : 0 < epsilon)
    (hepsilon : epsilon ≤ 1) :
    ∀ᶠ T : ℕ in atTop, ∀ H : ℕ,
      fiveEventMass (quadraticProfilePrimeBand T)
          reciprocalBernoulli
          (fiveIndexedCarrierProfileFailure
            (quadraticProfilePrimeBand T)
            (quadraticDelayedProfileChecks T H)
            (quadraticDelayedProfileCarrier T)
            quadraticDelayedProfileThreshold) <
        1 / 8 := by
  have hfailure :=
    eventually_quadraticDelayedProfileFailureMass_le hepsilonPos
  have hbound :=
    quadraticDelayedProfileNumericalBound_lt_one_eighth hepsilon
  filter_upwards [hfailure] with T hfailureT
  intro H
  exact (hfailureT H).trans_lt hbound

end Erdos536
