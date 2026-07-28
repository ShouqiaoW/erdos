import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalClippedIntervalGeometry

/-!
# Ordered four/five specialization on exceptional physical intervals

This file is the narrow analytic connector between the exact endpoint
geometry of the clipped exceptional intervals and the fully bounded ordered
four/five mixture theorem.

The padded logarithmic range has two roles.  It is the common-domain input
for the moving/fixed simplex identification, and its upper endpoint bounds
the log-log mass span.  Together with the eventual reciprocal-BV bound and
the unconditional endpoint PNT witness, this gives the ordered mixture
estimate with the fixed compact mass constant.

No arithmetic-to-rough transfer, paper-rate conversion, or kernel freezing
is claimed here.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Elementary inputs for the compact mass theorem -/

theorem fourFiveReciprocalBVError_le_one_of_log_large
    {y : Nat}
    (hlogOne : 1 <= Real.log (y : Real))
    (hlogConstant :
      5 * fullReciprocalSumUniformConstant <=
        Real.log (y : Real)) :
    fourFiveReciprocalBVError y <= 1 := by
  have hlogPos : 0 < Real.log (y : Real) :=
    zero_lt_one.trans_le hlogOne
  have hlogLeCube :
      Real.log (y : Real) <= Real.log (y : Real) ^ 3 := by
    calc
      Real.log (y : Real) =
          Real.log (y : Real) * 1 := by ring
      _ <= Real.log (y : Real) * Real.log (y : Real) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (one_le_pow₀ (n := 2) hlogOne) hlogPos.le
      _ = Real.log (y : Real) ^ 3 := by ring
  unfold fourFiveReciprocalBVError
  exact
    (div_le_one (pow_pos hlogPos 3)).2
      (hlogConstant.trans hlogLeCube)

/-- The upper padded coordinate `4.7` is already strictly below the compact
mass cutoff `4.8`.  Thus the paper range bounds the complete log-log span
from the rough scale `y` to the upper endpoint `B`. -/
theorem
    fourFiveLogLogPrimitive_sub_le_log_twentyfour_fifths_of_paperRange
    {y A B : Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      fourFiveRealLogCoordinate y t ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    fourFiveLogLogPrimitive B - fourFiveLogLogPrimitive y <=
      Real.log ((24 : Real) / 5) := by
  have hyB : y <= B := hyA.trans hAB
  have hlogY : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogB : 0 < Real.log (B : Real) :=
    Real.log_pos
      (by exact_mod_cast (show 1 < B by omega))
  have hBmem : (B : Real) ∈ Set.Icc (A : Real) (B : Real) := by
    constructor
    · exact_mod_cast hAB
    · exact le_rfl
  have hcoordinate :=
    (hrange (B : Real) hBmem).2
  unfold fourFiveRealLogCoordinate at hcoordinate
  have hratioPos :
      0 < Real.log (B : Real) / Real.log (y : Real) :=
    div_pos hlogB hlogY
  have hratioUpper :
      Real.log (B : Real) / Real.log (y : Real) <=
        (24 : Real) / 5 :=
    hcoordinate.trans (by norm_num)
  unfold fourFiveLogLogPrimitive
  rw [← Real.log_div hlogB.ne' hlogY.ne']
  exact Real.log_le_log hratioPos hratioUpper

/-! ## Finite ordered analytic specialization -/

/-- The paper-range certificate removes both explicit mass hypotheses from
the fully bounded ordered theorem.  The reciprocal-BV smallness and the PNT
witness remain visible finite inputs. -/
theorem
    fourFiveOrderedPrimeMixtureEstimate_realEndpoint_compact_of_paperRange
    {y A B : Nat} {C X0 : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hyX0 : X0 <= (y : Real))
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (herror : fourFiveReciprocalBVError y <= 1)
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      fourFiveRealLogCoordinate y t ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumMixtureIntegralMain y A B)
      (fourFiveRealEndpointFullyBoundedAssemblyError C y A B
        fourFiveCompactReciprocalMass) := by
  have hyB : y <= B := hyA.trans hAB
  have hspan :=
    fourFiveLogLogPrimitive_sub_le_log_twentyfour_fifths_of_paperRange
      hy hyA hAB hrange
  have hmass :=
    fourFive_actual_and_continuum_mass_le_compact
      hcut hyB hspan herror
  exact
    fourFiveOrderedPrimeMixtureEstimate_realEndpoint_fullyBounded_mixtureIntegral
      hC hX0 hyX0 hy hyA hAB hcut hmass.1 hmass.2 hrange hPNT

/-! ## Eventual specialization to every certified exceptional interval -/

theorem roughCanonicalExceptional_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : Nat => y n) atTop atTop := by
    simpa only [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : Real) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

theorem roughCanonicalExceptional_log_yNat_tendsto_atTop :
    Tendsto (fun n : Nat => Real.log (yNat n : Real))
      atTop atTop := by
  have hyReal :
      Tendsto (fun n : Nat => (yNat n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      roughCanonicalExceptional_yNat_tendsto_atTop
  exact Real.tendsto_log_atTop.comp hyReal

/-- Uniform eventual ordered estimate for every nonempty clipped interval
represented by the exact exceptional endpoint geometry.  The constant is
the unconditional endpoint-PNT constant and is independent of the smooth
core and both interval endpoints. -/
theorem
    exists_eventually_roughCanonicalExceptionalPhysicalInterval_orderedMixtureEstimate
    {deltaStar : Real} :
    ∃ C : Real, 0 < C ∧
      ∀ᶠ n : Nat in atTop, ∀ b A B : Nat,
        RoughCanonicalExceptionalPhysicalIntervalGeometry
            n deltaStar b A B ->
          FourFiveOrderedPrimeMixtureEstimate (yNat n) A B
            (fourFiveContinuumMixtureIntegralMain (yNat n) A B)
            (fourFiveRealEndpointFullyBoundedAssemblyError
              C (yNat n) A B fourFiveCompactReciprocalMass) := by
  obtain ⟨C, hC, X0, hX0, hPNT⟩ :=
    exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le
  refine ⟨C, hC, ?_⟩
  have hyReal :
      Tendsto (fun n : Nat => (yNat n : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      roughCanonicalExceptional_yNat_tendsto_atTop
  filter_upwards [
      roughCanonicalExceptional_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop fourFiveReciprocalBVSafeCutoff),
      hyReal.eventually (eventually_ge_atTop X0),
      roughCanonicalExceptional_log_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop 1),
      roughCanonicalExceptional_log_yNat_tendsto_atTop.eventually
        (eventually_ge_atTop
          (5 * fullReciprocalSumUniformConstant))]
      with n hcut hyX0 hlogOne hlogConstant
  intro b A B hgeometry
  have hy : 2 <= yNat n :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hcut
  have herror : fourFiveReciprocalBVError (yNat n) <= 1 :=
    fourFiveReciprocalBVError_le_one_of_log_large
      hlogOne hlogConstant
  have hrange :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        fourFiveRealLogCoordinate (yNat n) t ∈
          Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
    simpa only [fourFiveRealLogCoordinate] using
      hgeometry.padded_log_range
  exact
    fourFiveOrderedPrimeMixtureEstimate_realEndpoint_compact_of_paperRange
      hC hX0 hyX0 hy hgeometry.rough_cutoff_le_lower
      hgeometry.lower_le_upper hcut herror hrange hPNT

end BankPaperRealization

end

end Erdos390.WholePaper
