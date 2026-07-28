import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalPhysicalReindex
import Erdos390.WholePaper.BankPaperFourFiveSignedCoreErrorAdapter
import Erdos390.Full.PaperScaleEndpoint

/-!
# Endpoint geometry for the three clipped signed exceptional intervals

This file isolates the elementary endpoint work needed before applying the
four/five rough-interval estimate to the three physical intervals in the
signed exceptional core.

There are two separate layers.

* A common endpoint certificate controls the literal real exceptional floor,
  the fifth-power rough chamber, and the padded logarithmic coordinate range.
* For a fixed positive smooth core, each clipped physical interval is either
  empty or satisfies exactly the endpoint hypotheses consumed by the
  four/five counting and kernel-freezing adapters.

The common certificate is proved eventually from
`0 <= deltaStar < 1/18`.  In particular, the proof retains both rounding
operations: the exceptional lower endpoint is a natural floor, while the
smooth-core prefix is bounded by twice the natural ceiling
`tangentPaperExceptionalCutoff`.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Erdos390.Full.PaperScaleMarkedCell

noncomputable section

namespace BankPaperRealization

/-! ## Named endpoints and the exact adapter geometry -/

def roughCanonicalExceptionalPhysicalLowerEndpoint
    (n : Nat) (deltaStar : Real) (b lo : Nat) : Nat :=
  max (lo / b)
    (roughCanonicalRealExceptionalRoughCutoff n deltaStar)

def roughCanonicalExceptionalPhysicalUpperEndpoint
    (b hi : Nat) : Nat :=
  hi / b

theorem roughCanonicalExceptionalClippedRoughInterval_eq_endpoints
    (n b lo hi : Nat) (deltaStar : Real) :
    roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi =
      fourFiveRoughInterval (yNat n)
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b hi) := by
  rfl

/-- The exact endpoint package needed by the per-interval four/five
counting theorem.  The upper scale includes the harmless `+1` used by the
paper-rate adapter. -/
structure RoughCanonicalExceptionalPhysicalIntervalGeometry
    (n : Nat) (deltaStar : Real) (b A B : Nat) : Prop where
  core_pos : 1 <= b
  core_le_cutoff :
    b <= 2 * tangentPaperExceptionalCutoff deltaStar n
  lower_pos : 1 <= A
  lower_le_upper : A <= B
  upper_le_paperScale : B <= 3 * n / b + 1
  rough_cutoff_le_lower : yNat n <= A
  omega_chamber : B < (yNat n + 1) ^ 5
  padded_log_range :
    ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (yNat n : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)

/-- The data common to all three physical intervals before division by a
smooth core. -/
structure RoughCanonicalExceptionalCommonEndpointGeometry
    (n : Nat) (deltaStar : Real) : Prop where
  exceptional_floor_pos :
    1 <= roughCanonicalRealExceptionalRoughCutoff n deltaStar
  rough_cutoff_le_exceptional_floor :
    yNat n <= roughCanonicalRealExceptionalRoughCutoff n deltaStar
  omega_cap : 3 * n < (yNat n + 1) ^ 5
  padded_log_range :
    ∀ t ∈ Set.Icc
        (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real)
        ((3 * n : Nat) : Real),
      Real.log t / Real.log (yNat n : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)

/-- The geometry structure exposes the hypotheses used verbatim by
`abs_fourFiveRoughInterval_card_sub_mixtureIntegral_le_paperRate`.
The last inequality supplies its natural choice of scale `Z`. -/
theorem
    RoughCanonicalExceptionalPhysicalIntervalGeometry.counting_inputs
    {n b A B : Nat} {deltaStar : Real}
    (h :
      RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b A B) :
    1 <= A ∧ A <= B ∧ B < (yNat n + 1) ^ 5 ∧
      yNat n <= B ∧
      (∀ t ∈ Set.Icc (A : Real) (B : Real),
        Real.log t / Real.log (yNat n : Real) ∈
          Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ∧
      (B : Real) <= (3 * n / b + 1 : Nat) := by
  refine ⟨h.lower_pos, h.lower_le_upper, h.omega_chamber,
    h.rough_cutoff_le_lower.trans h.lower_le_upper,
    h.padded_log_range, ?_⟩
  exact_mod_cast h.upper_le_paperScale

/-! ## Empty-interval handling -/

theorem fourFiveRoughInterval_eq_empty_of_upper_le_lower
    {y A B : Nat} (hBA : B <= A) :
    fourFiveRoughInterval y A B = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  have hrData := mem_fourFiveRoughInterval.mp hr
  omega

theorem roughCanonicalExceptionalClippedRoughInterval_eq_empty
    {n b lo hi : Nat} {deltaStar : Real}
    (hBA :
      roughCanonicalExceptionalPhysicalUpperEndpoint b hi <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo) :
    roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi = ∅ := by
  rw [roughCanonicalExceptionalClippedRoughInterval_eq_endpoints]
  exact fourFiveRoughInterval_eq_empty_of_upper_le_lower hBA

theorem roughCanonicalExceptionalClippedRoughInterval_card_eq_zero
    {n b lo hi : Nat} {deltaStar : Real}
    (hBA :
      roughCanonicalExceptionalPhysicalUpperEndpoint b hi <=
        roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo) :
    (roughCanonicalExceptionalClippedRoughInterval
        n deltaStar b lo hi).card = 0 := by
  rw [roughCanonicalExceptionalClippedRoughInterval_eq_empty hBA]
  rfl

/-! ## A common certificate gives every nonempty clipped interval -/

theorem roughCanonicalExceptionalClippedInterval_geometry
    {n b lo hi : Nat} {deltaStar : Real}
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hAB :
      roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo <=
        roughCanonicalExceptionalPhysicalUpperEndpoint b hi)
    (hhi : hi <= 3 * n) :
    RoughCanonicalExceptionalPhysicalIntervalGeometry
      n deltaStar b
      (roughCanonicalExceptionalPhysicalLowerEndpoint
        n deltaStar b lo)
      (roughCanonicalExceptionalPhysicalUpperEndpoint b hi) := by
  let A :=
    roughCanonicalExceptionalPhysicalLowerEndpoint
      n deltaStar b lo
  let B := roughCanonicalExceptionalPhysicalUpperEndpoint b hi
  have hbData := Finset.mem_Icc.mp hb
  have hcutA :
      roughCanonicalRealExceptionalRoughCutoff n deltaStar <= A := by
    exact le_max_right _ _
  have hBHi : B <= hi := by
    dsimp only [B, roughCanonicalExceptionalPhysicalUpperEndpoint]
    exact Nat.div_le_self _ _
  have hBThree : B <= 3 * n := hBHi.trans hhi
  have hBScale : B <= 3 * n / b + 1 := by
    have hdiv : B <= 3 * n / b := by
      dsimp only [B, roughCanonicalExceptionalPhysicalUpperEndpoint]
      exact Nat.div_le_div_right hhi
    omega
  refine
    { core_pos := hbData.1
      core_le_cutoff := hbData.2
      lower_pos := hcommon.exceptional_floor_pos.trans hcutA
      lower_le_upper := by simpa only [A, B] using hAB
      upper_le_paperScale := by simpa only [B] using hBScale
      rough_cutoff_le_lower :=
        hcommon.rough_cutoff_le_exceptional_floor.trans hcutA
      omega_chamber := hBThree.trans_lt hcommon.omega_cap
      padded_log_range := ?_ }
  intro t ht
  apply hcommon.padded_log_range t
  constructor
  · have hcutAR :
        (roughCanonicalRealExceptionalRoughCutoff
          n deltaStar : Real) <= (A : Real) := by
      exact_mod_cast hcutA
    exact hcutAR.trans ht.1
  · have hBThreeR : (B : Real) <= ((3 * n : Nat) : Real) := by
      exact_mod_cast hBThree
    exact ht.2.trans hBThreeR

/-- Every clipped interval is either in the exact four/five geometry or is
literally empty. -/
theorem roughCanonicalExceptionalClippedInterval_geometry_or_empty
    {n b lo hi : Nat} {deltaStar : Real}
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hhi : hi <= 3 * n) :
    RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b hi) ∨
      roughCanonicalExceptionalClippedRoughInterval
          n deltaStar b lo hi = ∅ := by
  by_cases hAB :
      roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b lo <=
        roughCanonicalExceptionalPhysicalUpperEndpoint b hi
  · exact Or.inl
      (roughCanonicalExceptionalClippedInterval_geometry
        hcommon hb hAB hhi)
  · exact Or.inr
      (roughCanonicalExceptionalClippedRoughInterval_eq_empty
        (by omega))

/-- Simultaneous endpoint alternative for the upper, high, and broad
physical pieces at the actual positive depth `K0+1`. -/
theorem roughCanonicalExceptional_threePhysicalIntervals_geometry_or_empty
    {n K0 b : Nat} {c deltaStar : Real}
    (hcommon :
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (htail : upperTailLength c n <= n) :
    (RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b (2 * n))
        (roughCanonicalExceptionalPhysicalUpperEndpoint
          b (2 * n + upperTailLength c n)) ∨
      roughCanonicalExceptionalUpperPhysicalRoughInterval
          n (upperTailLength c n) deltaStar b = ∅) ∧
    (RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b
        (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
          (2 * n - (K0 + 1) * upperTailLength c n))
        (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)) ∨
      roughCanonicalExceptionalHighPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b = ∅) ∧
    (RoughCanonicalExceptionalPhysicalIntervalGeometry
        n deltaStar b
        (roughCanonicalExceptionalPhysicalLowerEndpoint
          n deltaStar b n)
        (roughCanonicalExceptionalPhysicalUpperEndpoint b
          (2 * n - (K0 + 1) * upperTailLength c n)) ∨
      roughCanonicalExceptionalBroadPhysicalRoughInterval
          n (upperTailLength c n) (K0 + 1) deltaStar b = ∅) := by
  have hupper :
      2 * n + upperTailLength c n <= 3 * n := by omega
  have hhigh : 2 * n <= 3 * n := by omega
  have hbroad :
      2 * n - (K0 + 1) * upperTailLength c n <= 3 * n := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [
      roughCanonicalExceptionalUpperPhysicalRoughInterval] using
      (roughCanonicalExceptionalClippedInterval_geometry_or_empty
        (n := n) (b := b) (lo := 2 * n)
        (hi := 2 * n + upperTailLength c n)
        (deltaStar := deltaStar) hcommon hb hupper)
  · simpa only [
      roughCanonicalExceptionalHighPhysicalRoughInterval] using
      (roughCanonicalExceptionalClippedInterval_geometry_or_empty
        (n := n) (b := b)
        (lo := 2 * n - (K0 + 1) * upperTailLength c n)
        (hi := 2 * n) (deltaStar := deltaStar)
        hcommon hb hhigh)
  · simpa only [
      roughCanonicalExceptionalBroadPhysicalRoughInterval] using
      (roughCanonicalExceptionalClippedInterval_geometry_or_empty
        (n := n) (b := b) (lo := n)
        (hi := 2 * n - (K0 + 1) * upperTailLength c n)
        (deltaStar := deltaStar) hcommon hb hbroad)

/-! ## The literal exceptional floor dominates `n^(1-deltaStar)` -/

theorem rpow_one_sub_le_roughCanonicalRealExceptionalRoughCutoff
    {n : Nat} {deltaStar : Real}
    (hn : 1 <= n) (_hdelta : 0 <= deltaStar)
    (hdeltaOne : deltaStar <= 1) :
    (n : Real) ^ (1 - deltaStar) <=
      (roughCanonicalRealExceptionalRoughCutoff
        n deltaStar : Real) := by
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hpowerOne :
      (1 : Real) <= (n : Real) ^ (1 - deltaStar) :=
    Real.one_le_rpow hnOne (sub_nonneg.mpr hdeltaOne)
  have hquotient :
      2 * (n : Real) / (n : Real) ^ deltaStar =
        2 * (n : Real) ^ (1 - deltaStar) := by
    rw [Real.rpow_sub hnReal, Real.rpow_one]
    ring
  have hfloor :=
    Nat.lt_floor_add_one
      (2 * (n : Real) / (n : Real) ^ deltaStar)
  change
    2 * (n : Real) / (n : Real) ^ deltaStar <
      (roughCanonicalRealExceptionalRoughCutoff
        n deltaStar : Real) + 1 at hfloor
  rw [hquotient] at hfloor
  linarith

theorem one_le_roughCanonicalRealExceptionalRoughCutoff
    {n : Nat} {deltaStar : Real}
    (hn : 1 <= n) (hdelta : 0 <= deltaStar)
    (hdeltaOne : deltaStar <= 1) :
    1 <= roughCanonicalRealExceptionalRoughCutoff n deltaStar := by
  have hpower :=
    rpow_one_sub_le_roughCanonicalRealExceptionalRoughCutoff
      hn hdelta hdeltaOne
  have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hone :
      (1 : Real) <= (n : Real) ^ (1 - deltaStar) :=
    Real.one_le_rpow hnOne (sub_nonneg.mpr hdeltaOne)
  exact_mod_cast hone.trans hpower

theorem yNat_le_roughCanonicalRealExceptionalRoughCutoff
    {n : Nat} {deltaStar : Real}
    (hn : 1 <= n) (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar <= 1 / 18) :
    yNat n <=
      roughCanonicalRealExceptionalRoughCutoff n deltaStar := by
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hnOne : (1 : Real) <= (n : Real) := by exact_mod_cast hn
  have hyFloor : (yNat n : Real) <= y n :=
    Nat.floor_le (y_pos (by omega)).le
  have hpowerCompare :
      y n <= (n : Real) ^ (1 - deltaStar) := by
    unfold y
    apply Real.rpow_le_rpow_of_exponent_le hnOne
    linarith
  have hcut :=
    rpow_one_sub_le_roughCanonicalRealExceptionalRoughCutoff
      hn hdelta (by linarith [hdeltaUpper])
  exact_mod_cast hyFloor.trans (hpowerCompare.trans hcut)

/-! ## Padded logarithmic coordinates -/

/-- One explicit logarithmic threshold pays the upper endpoint rounding
from `3n` and the floor loss in `yNat`. -/
def roughCanonicalExceptionalPaddedLogThreshold : Real :=
  (45 / 2 : Real) *
    (Real.log 3 + (47 / 10 : Real) * Real.log 2)

theorem roughCanonicalExceptional_common_padded_log_range
    {n : Nat} {deltaStar : Real}
    (hn : 1 < n) (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hyTwo : (2 : Real) <= y n)
    (hLlarge :
      roughCanonicalExceptionalPaddedLogThreshold <= L n) :
    ∀ t ∈ Set.Icc
        (roughCanonicalRealExceptionalRoughCutoff n deltaStar : Real)
        ((3 * n : Nat) : Real),
      Real.log t / Real.log (yNat n : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hnOne : (1 : Real) <= (n : Real) := by
    exact_mod_cast (show 1 <= n by omega)
  have hLPos : 0 < L n := L_pos hn
  have hyNatTwo : 2 <= yNat n := Nat.le_floor hyTwo
  have hlogYPos : 0 < Real.log (yNat n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hyGap := log_y_sub_log_yNat_bounds hnPos hyTwo
  have hlogYUpper :
      Real.log (yNat n : Real) <= (2 / 9 : Real) * L n := by
    rw [← log_y hnPos]
    linarith [hyGap.1]
  have hlogYLower :
      (2 / 9 : Real) * L n - Real.log 2 <=
        Real.log (yNat n : Real) := by
    rw [← log_y hnPos]
    linarith [hyGap.2]
  have hupperModel :
      Real.log 3 + L n <=
        (47 / 10 : Real) *
          ((2 / 9 : Real) * L n - Real.log 2) := by
    unfold roughCanonicalExceptionalPaddedLogThreshold at hLlarge
    nlinarith
  have hcutPower :=
    rpow_one_sub_le_roughCanonicalRealExceptionalRoughCutoff
      (show 1 <= n by omega) hdelta
      (by linarith [hdeltaUpper])
  intro t ht
  have hcutOne :=
    one_le_roughCanonicalRealExceptionalRoughCutoff
      (show 1 <= n by omega) hdelta
      (by linarith [hdeltaUpper])
  have hcutPosR :
      (0 : Real) <
        (roughCanonicalRealExceptionalRoughCutoff
          n deltaStar : Real) := by
    exact_mod_cast
      (show 0 <
        roughCanonicalRealExceptionalRoughCutoff n deltaStar by omega)
  have htPos : (0 : Real) < t := by
    exact hcutPosR.trans_le ht.1
  have hcutLeT :
      (roughCanonicalRealExceptionalRoughCutoff
        n deltaStar : Real) <= t := ht.1
  have hpowerLeT :
      (n : Real) ^ (1 - deltaStar) <= t :=
    hcutPower.trans hcutLeT
  have hlogLower :
      (1 - deltaStar) * L n <= Real.log t := by
    have hlog :=
      Real.log_le_log
        (Real.rpow_pos_of_pos hnReal (1 - deltaStar)) hpowerLeT
    rw [Real.log_rpow hnReal] at hlog
    simpa only [L] using hlog
  have hlower :
      (41 / 10 : Real) <=
        Real.log t / Real.log (yNat n : Real) := by
    apply (le_div_iff₀ hlogYPos).2
    have hcoefficient :
        (41 / 10 : Real) * Real.log (yNat n : Real) <=
          (41 / 45 : Real) * L n := by
      nlinarith [hlogYUpper]
    nlinarith [hcoefficient, hlogLower]
  have htThree : t <= ((3 * n : Nat) : Real) := ht.2
  have hlogThree :
      Real.log t <= Real.log 3 + L n := by
    calc
      Real.log t <=
          Real.log (((3 * n : Nat) : Real)) :=
        Real.log_le_log htPos htThree
      _ = Real.log ((3 : Real) * (n : Real)) := by
        norm_num
      _ = Real.log 3 + Real.log (n : Real) :=
        Real.log_mul (by norm_num) hnReal.ne'
      _ = Real.log 3 + L n := by rfl
  have hupper :
      Real.log t / Real.log (yNat n : Real) <=
        (47 / 10 : Real) := by
    apply (div_le_iff₀ hlogYPos).2
    calc
      Real.log t <= Real.log 3 + L n := hlogThree
      _ <= (47 / 10 : Real) *
          ((2 / 9 : Real) * L n - Real.log 2) := hupperModel
      _ <= (47 / 10 : Real) *
          Real.log (yNat n : Real) :=
        mul_le_mul_of_nonneg_left hlogYLower (by norm_num)
  exact ⟨hlower, hupper⟩

/-! ## Fifth-power chamber and the eventual common certificate -/

theorem three_mul_lt_yNat_succ_pow_five
    {n : Nat} (hn : 0 < n)
    (hpower : (3 : Real) < (n : Real) ^ (1 / 9 : Real)) :
    3 * n < (yNat n + 1) ^ 5 := by
  have hnReal : (0 : Real) < (n : Real) := by positivity
  have hmul :
      (3 : Real) * (n : Real) <
        (n : Real) * (n : Real) ^ (1 / 9 : Real) := by
    calc
      (3 : Real) * (n : Real) <
          (n : Real) ^ (1 / 9 : Real) * (n : Real) :=
        mul_lt_mul_of_pos_right hpower hnReal
      _ = (n : Real) * (n : Real) ^ (1 / 9 : Real) :=
        mul_comm _ _
  have hpowerIdentity :
      (n : Real) * (n : Real) ^ (1 / 9 : Real) = y n ^ 5 := by
    unfold y
    calc
      (n : Real) * (n : Real) ^ (1 / 9 : Real) =
          (n : Real) ^ (1 : Real) *
            (n : Real) ^ (1 / 9 : Real) := by rw [Real.rpow_one]
      _ = (n : Real) ^ ((1 : Real) + 1 / 9) :=
        (Real.rpow_add hnReal 1 (1 / 9)).symm
      _ = (n : Real) ^ ((2 / 9 : Real) * (5 : Nat)) := by norm_num
      _ = ((n : Real) ^ (2 / 9 : Real)) ^ 5 :=
        Real.rpow_mul_natCast hnReal.le (2 / 9) 5
  have hyFloor : y n < (yNat n : Real) + 1 :=
    Nat.lt_floor_add_one _
  have hyPow :
      y n ^ 5 < ((yNat n : Real) + 1) ^ 5 :=
    pow_lt_pow_left₀ hyFloor (y_pos hn).le (by norm_num)
  have hreal :
      (3 : Real) * (n : Real) <
        ((yNat n : Real) + 1) ^ 5 := by
    calc
      (3 : Real) * (n : Real) <
          (n : Real) * (n : Real) ^ (1 / 9 : Real) := hmul
      _ = y n ^ 5 := hpowerIdentity
      _ < ((yNat n : Real) + 1) ^ 5 := hyPow
  exact_mod_cast hreal

theorem roughCanonicalExceptionalCommonEndpointGeometry_of_bounds
    {n : Nat} {deltaStar : Real}
    (hn : 1 < n) (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hyTwo : (2 : Real) <= y n)
    (hLlarge :
      roughCanonicalExceptionalPaddedLogThreshold <= L n)
    (hpower : (3 : Real) < (n : Real) ^ (1 / 9 : Real)) :
    RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar := by
  refine
    { exceptional_floor_pos :=
        one_le_roughCanonicalRealExceptionalRoughCutoff
          (show 1 <= n by omega) hdelta
          (by linarith [hdeltaUpper])
      rough_cutoff_le_exceptional_floor :=
        yNat_le_roughCanonicalRealExceptionalRoughCutoff
          (show 1 <= n by omega) hdelta hdeltaUpper.le
      omega_cap :=
        three_mul_lt_yNat_succ_pow_five (by omega) hpower
      padded_log_range :=
        roughCanonicalExceptional_common_padded_log_range
          hn hdelta hdeltaUpper hyTwo hLlarge }

theorem eventually_roughCanonicalExceptionalCommonEndpointGeometry
    {deltaStar : Real} (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop,
      RoughCanonicalExceptionalCommonEndpointGeometry n deltaStar := by
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyTop : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa only [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hpowerTop :
      Tendsto (fun n : Nat => (n : Real) ^ (1 / 9 : Real))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : Real) < 1 / 9)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [
      eventually_gt_atTop 1,
      hLTop.eventually
        (eventually_ge_atTop
          roughCanonicalExceptionalPaddedLogThreshold),
      hyTop.eventually (eventually_ge_atTop 2),
      hpowerTop.eventually (eventually_gt_atTop 3)]
      with n hn hL hy hpower
  exact
    roughCanonicalExceptionalCommonEndpointGeometry_of_bounds
      hn hdelta hdeltaUpper hy hL hpower

/-- Eventual simultaneous geometry for every core in the full exceptional
prefix.  This is the finite endpoint boundary used by both the deep prefix
and the positive cutoff band. -/
theorem
    eventually_roughCanonicalExceptional_threePhysicalIntervals_geometry_or_empty
    {K0 : Nat} {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 <= deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∀ᶠ n : Nat in atTop, forall b : Nat,
      b ∈ Finset.Icc 1
          (2 * tangentPaperExceptionalCutoff deltaStar n) ->
        (RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b
            (roughCanonicalExceptionalPhysicalLowerEndpoint
              n deltaStar b (2 * n))
            (roughCanonicalExceptionalPhysicalUpperEndpoint
              b (2 * n + upperTailLength c n)) ∨
          roughCanonicalExceptionalUpperPhysicalRoughInterval
              n (upperTailLength c n) deltaStar b = ∅) ∧
        (RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b
            (roughCanonicalExceptionalPhysicalLowerEndpoint n deltaStar b
              (2 * n - (K0 + 1) * upperTailLength c n))
            (roughCanonicalExceptionalPhysicalUpperEndpoint b (2 * n)) ∨
          roughCanonicalExceptionalHighPhysicalRoughInterval
              n (upperTailLength c n) (K0 + 1) deltaStar b = ∅) ∧
        (RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b
            (roughCanonicalExceptionalPhysicalLowerEndpoint
              n deltaStar b n)
            (roughCanonicalExceptionalPhysicalUpperEndpoint b
              (2 * n - (K0 + 1) * upperTailLength c n)) ∨
          roughCanonicalExceptionalBroadPhysicalRoughInterval
              n (upperTailLength c n) (K0 + 1) deltaStar b = ∅) := by
  filter_upwards [
      eventually_roughCanonicalExceptionalCommonEndpointGeometry
        hdelta hdeltaUpper,
      eventually_upperTailLength_le hc]
      with n hcommon htail
  intro b hb
  exact
    roughCanonicalExceptional_threePhysicalIntervals_geometry_or_empty
      hcommon hb htail

end BankPaperRealization

end

end Erdos390.WholePaper
