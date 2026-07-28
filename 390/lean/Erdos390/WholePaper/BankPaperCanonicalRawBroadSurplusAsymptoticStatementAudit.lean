import Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic

/-!
# Statement audit: eventual raw broad-pool surplus

This audit restates every public declaration of
`BankPaperCanonicalRawBroadSurplusAsymptotic`.  In particular, the final
surplus and capacity theorems have no rowwise pool estimate among their
premises and retain an arbitrary fixed `poolMinimum` parameter.
-/

open Filter
open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptoticStatementAudit

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.DickmanBasic
open Erdos390.Full.StructuredCells
open Erdos390.WholePaper
open Erdos390.WholePaper.BankPaperRealization

#check roughCanonicalPoolDickmanFloor

example : 0 < roughCanonicalPoolDickmanFloor :=
  roughCanonicalPoolDickmanFloor_pos

example {u : Real} (hu0 : 0 <= u) (hu5 : u <= 5) :
    roughCanonicalPoolDickmanFloor <= rho u :=
  roughCanonicalPoolDickmanFloor_le_rho hu0 hu5

#check roughCanonical_dickmanEndpointMain_sub_lower
#check roughCanonical_smoothInterval_card_lower

example (W : Nat) :
    (∑ d ∈ (roughHeadModulus W).divisors,
        (ArithmeticFunction.moebius d : Real) / (d : Real)) =
      roughHeadDensity W :=
  roughHead_sum_moebius_div_eq_density W

#check roughCanonical_smoothInterval_divisorShift_error
#check roughCanonical_headFreeSmoothInterval_lower_of_shift
#check roughCanonical_headFreeSmoothInterval_card_lower

#check roughCanonicalRawBroadPoolDensity

example (W : Nat) : 0 < roughCanonicalRawBroadPoolDensity W :=
  roughCanonicalRawBroadPoolDensity_pos W

#check roughCanonicalBroadCorrectionPool_card_eq_headFreeSmoothInterval
#check roughCanonicalBroadCorrectionPool_card_eq_headFreeSmoothInterval_of_isCompleteRoughLabel
#check roughUpperCompleteRoughRowTarget_le_div_add_one
#check BankPaperRealization.rawCanonicalRowOfGuardedLabel
#check roughCanonical_activeLabel_div_scale_lower
#check roughCanonical_activeLabel_three_mul_le_half
#check eventually_roughCanonical_activeRawBroadPool_linear_lower
#check RoughCanonicalActiveIntrinsicRawBroadSurplus
#check eventually_roughCanonicalActiveIntrinsicRawBroadSurplus
#check BankPaperRealization.eventually_roughCanonicalActiveRawBroadSurplus
#check BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
#check BankPaperRealization.eventually_roughCanonical_active_guard_capacity_inputs

end Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptoticStatementAudit
