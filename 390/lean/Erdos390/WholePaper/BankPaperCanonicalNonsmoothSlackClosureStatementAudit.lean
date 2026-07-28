import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure

/-! # Statement audit: canonical nonsmooth slack closure -/

namespace Erdos390.WholePaper

open Erdos390.Full.Scale
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Filter Topology
open scoped BigOperators

noncomputable section

namespace BankPaperRealization

#check paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
#check prechargeBaseState_completeLabelMultiplicity_le_one
#check roughCanonicalGuardDeletedRow_subset_anchorRow_of_baseMultiplicity_zero
#check roughCanonicalGuardDeletedRow_card_le_one_of_baseMultiplicity_zero
#check roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_two
#check roughCanonicalBalancedRawWeightGuardBound
#check roughCanonicalBalancedRawWeightGuardBound_nonneg
#check roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
#check roughCanonicalBalancedGuardNumeratorConstant
#check roughCanonicalBalancedGuardNumeratorConstant_pos
#check roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_fixed

end BankPaperRealization

#check isCompleteRoughLabel_three_le_of_two_le
#check eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active

namespace BankPaperRealization

#check roughCanonicalGuardedPostchargeCorrectionDensity_eq_discrepancy_div
#check roughCanonicalRawRowDiscrepancy_eq_quotaError
#check roughCanonicalBalancedPostchargeRowDiscrepancy_abs_le_raw_add_guard
#check roughCanonicalGuardedBroadCorrectionPool_linear_half_lower
#check roughCanonicalBalancedGuardedPostchargeCorrectionDensity_abs_le_reserve
#check RoughCanonicalBalancedNonsmoothBounds
#check nonsmoothEndpointBounds_force_margin_inequalities
#check nonsmoothEndpointBounds_impossible_of_beta_le_sigma
#check eventually_roughCanonicalBalancedNonsmoothBounds
#check RoughCanonicalBalancedNonsmoothBounds.to_actualEndpointBounds

example {ell sigma beta correction : Real} (hell : 0 < ell)
    (hfloor : sigma / ell + |correction| <= beta / ell)
    (hceiling :
      beta / ell + |correction| <= 1 - sigma / ell) :
    ell * |correction| <= beta - sigma ∧
      ell * |correction| <= ell - beta - sigma :=
  nonsmoothEndpointBounds_force_margin_inequalities
    hell hfloor hceiling

example (W K0 : Nat)
    {c deltaStar betaProt betaAct sigma : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hbetaAct : 0 < betaAct) (hsigma : sigma <= betaProt) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
        RoughCanonicalBalancedNonsmoothBounds R certificate deltaStar
          W K0 betaProt betaAct sigma :=
  eventually_roughCanonicalBalancedNonsmoothBounds
    W K0 hc hdelta hbetaAct hsigma

end BankPaperRealization

end

end Erdos390.WholePaper
