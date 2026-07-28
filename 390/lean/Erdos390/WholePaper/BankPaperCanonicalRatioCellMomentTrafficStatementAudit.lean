import Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic

/-!
# Expanded statement audit for the canonical ratio-cell moment collapse

The declaration census covers every public definition and theorem.  The
expanded examples pin down the paper-scale total-traffic conclusion and
the literal `hmain`/`herror` scalar terminals.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

#check tangentRatioCell_sum_tailPointwiseUpper_eq_indexMoment
#check bankPaperCanonical_ratioCellIndex_le_logGap_div_logRho
#check bankPaperCanonical_ratioCellIndex_le_coordinateGap
#check bankPaperCanonicalRatioCellCoordinateMoment
#check bankPaperCanonical_fiber_shiftedCoordinate_eq
#check bankPaperCanonical_sum_shiftedCoordinate_eq_coordinateMoment
#check bankPaperCanonicalRatioCellFloorLoss
#check bankPaperCanonical_positive_shiftedCoordinate_le
#check bankPaperCanonical_low_shiftedCoordinate_le
#check bankPaperCanonical_ratioCellCoordinateMoment_le
#check bankPaperCanonicalRatioCellMomentCutMajorant
#check bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
#check bankPaperCanonical_ratioCellIndexMoment_le_coordinateMoment
#check bankPaperCanonical_ratioCellCutTraffic_le_momentMajorant
#check bankPaperCanonical_ratioCellTotalTraffic_le_momentMajorant
#check bankPaperCanonicalRatioCellTrafficConstant
#check bankPaperCanonicalRatioCellTrafficErrorCoefficient
#check bankPaperCanonical_ratioCellMomentTotalTrafficMajorant_paperScale
#check bankPaperCanonicalRatioCellCurrentLower
#check bankPaperCanonical_fixedCutoff_le_ratioCellCurrentLower
#check bankPaperCanonical_ratioCellCurrentLower_lt_label
#check bankPaperCanonical_label_le_two_mul_rho_sq_mul_currentLower
#check bankPaperCanonicalHarmonicTailMajorant_mono_lower
#check bankPaperCanonical_log_mul_logLogGap_le_logGap
#check bankPaperCanonical_logCurrentLower_mul_portNumerator_le
#check bankPaperCanonical_weightedPNTEnvelope_le_logGap
#check bankPaperCanonical_exponentBand_logWidth_le
#check bankPaperCanonical_currentLower_bandUpper_logGap_le
#check bankPaperCanonicalRatioCellUniformPortMajorant
#check bankPaperCanonical_weightedPNTEnvelope_le_uniformPortMajorant
#check bankPaperCanonical_weightedRatioCellUniformPortLoad_le_majorant
#check bankPaperCanonicalRatioCellPortConstant
#check bankPaperCanonicalRatioCellIncidentConstant
#check bankPaperCanonicalRatioCellIncidentErrorCoefficient
#check bankPaperCanonical_incidentMajorant_paperScale
#check tendsto_bankPaperCanonicalRatioCellIncidentErrorCoefficient_zero
#check bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
#check bankPaperCanonical_ratioCellTrafficErrorCoefficient_le_upper
#check tendsto_bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient_zero
#check bankPaperCanonical_yNat_tendsto_atTop
#check eventually_bankPaperCanonical_ratioCellErrorCoefficients_le
#check bankPaperCanonicalRatioCellMainCoefficient
#check bankPaperCanonical_ratioCellMainCoefficient_pos
#check bankPaperCanonicalRatioCellPaperWidthChoice
#check bankPaperCanonical_ratioCellPaperWidthChoice_pos
#check bankPaperCanonical_paperMainBudget_widthChoice_eq
#check bankPaperCanonical_paperMainBudget_le
#check bankPaperCanonicalRatioCellPaperErrorChoice
#check bankPaperCanonical_ratioCellPaperErrorChoice_pos
#check bankPaperCanonical_paperErrorBudget_choice_eq
#check eventually_bankPaperCanonical_paperErrorBudget_le

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} {rho tangentConstant N : Real}
    (hdelta : 0 < delta) (hn : 1 < n) (hWtwo : 2 <= W)
    (hrho : 1 < rho)
    (htangent : 0 <= tangentConstant) (hN : 0 <= N) :
    bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M n W rho
        (tangentConstant * N / Real.log (y n)) <=
      bankPaperCanonicalRatioCellTrafficConstant rho *
          tangentConstant * N * (delta + M.ratio) +
        bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant * N :=
  bankPaperCanonical_ratioCellMomentTotalTrafficMajorant_paperScale
    M hdelta hn hWtwo hrho htangent hN

example {density sigma rho tangentConstant width : Real}
    (hsigma : 0 < sigma) (hrho : 1 < rho)
    (htangent : 0 < tangentConstant)
    (hwidth : width <= bankPaperCanonicalRatioCellPaperWidthChoice
      density sigma rho tangentConstant) :
    tangentDistributedPaperMainBudget
        (bankPaperCanonicalRatioCellTrafficConstant rho)
        (bankPaperCanonicalRatioCellIncidentConstant rho)
        tangentConstant width sigma <= density ^ 2 / 48 :=
  bankPaperCanonical_paperMainBudget_le
    hsigma hrho htangent hwidth

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (W : Nat) (rho tangentConstant density sigma : Real)
    (hdensity : 0 < density) (hsigma : 0 < sigma) :
    ∀ᶠ n : Nat in atTop,
      2 <= yNat n ∧
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
            M W n rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <= density ^ 2 / 96 :=
  eventually_bankPaperCanonical_paperErrorBudget_le
    M W rho tangentConstant density sigma hdensity hsigma

end

end Erdos390.WholePaper
