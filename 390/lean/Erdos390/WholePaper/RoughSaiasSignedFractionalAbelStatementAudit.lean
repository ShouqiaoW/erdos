import Erdos390.WholePaper.RoughSaiasSignedFractionalAbel

/-! Statement checks for the signed fractional and finite Abel layer. -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

#check roughSaiasContinuousPrimeNormalForm
#check roughSaiasSignedPrimeFloorCorrection
#check roughSaiasSignedFractionalCorrectionTerm
#check roughSaiasRealQuotient_sub_fract_eq_natQuotient
#check roughSaiasSignedPrimeFloorCorrection_eq_fractional
#check roughSaiasReverseContinuousNormalFormDefect
#check roughSaiasReverseNormalFormDefect_eq_continuous_add_signedFloor
#check roughSaiasReverseNormalFormDefect_eq_continuous_add_fractional
#check roughSaiasNormalFormThetaWeight
#check roughSaiasPrimeThetaWeightedInterval_eq_continuousSum
#check roughSaiasIntegerAbelConsistencyDefect
#check roughSaiasThetaErrorTransfer
#check roughSaiasReverseContinuousNormalFormDefect_eq_abel_sub_theta
#check roughSaiasSignedAbelCenter
#check roughSaiasReverseNormalFormDefect_eq_signedAbelCenter_sub_theta
#check roughSaiasThetaErrorTransfer_eq_finiteAbel
#check roughSaiasNaturalQuotientThetaWeight
#check roughSaiasFractionalCorrectionThetaWeight
#check roughSaiasNormalFormThetaWeight_eq_natural_add_fractional
#check roughSaiasNaturalQuotientThetaWeight_diff_eq_paired
#check roughSaiasPrimeThetaWeightedInterval_eq_naturalSum
#check roughSaiasPrimeThetaWeightedInterval_eq_fractionalSum
#check roughSaiasIntegerAbelMain_normalForm_eq_natural_add_fractional
#check roughSaiasNaturalIntegerAbelConsistencyDefect
#check roughSaiasNaturalThetaErrorTransfer
#check roughSaiasFractionalThetaErrorTransfer
#check roughSaiasSignedAbelCenter_eq_natural_add_fractionalTheta
#check roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta
#check roughSaiasNaturalThetaErrorTransfer_eq_finiteAbel
#check roughSaiasThetaPNTLedger
#check roughSaiasThetaErrorTransfer_abs_le_pntLedger
#check roughSaiasNaturalThetaPNTLedger
#check roughSaiasNaturalThetaErrorTransfer_abs_le_pntLedger
#check roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le
#check roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le
#check roughSaiasThetaFourthPowerConstant
#check roughSaiasThetaFourthPowerConstant_pos
#check roughSaiasThetaFourthPowerCutoff
#check roughSaiasThetaFourthPower_bound
#check roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le_fourthPower
#check roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le_fourthPower

example (X m : ℕ) :
    roughSaiasSignedPrimeFloorCorrection X m =
      roughSaiasSignedFractionalCorrectionTerm X m :=
  roughSaiasSignedPrimeFloorCorrection_eq_fractional X m

example (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasReverseContinuousNormalFormDefect X y Z +
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughSaiasSignedFractionalCorrectionTerm X p :=
  roughSaiasReverseNormalFormDefect_eq_continuous_add_fractional X y Z

example (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasSignedAbelCenter X y Z -
        roughSaiasThetaErrorTransfer X y Z :=
  roughSaiasReverseNormalFormDefect_eq_signedAbelCenter_sub_theta X y Z

example {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasThetaErrorTransfer X y Z =
      roughSaiasNormalFormThetaWeight X Z *
          (FriableAsymptotic.primeLogSumUpTo Z - (Z : ℝ)) -
        roughSaiasNormalFormThetaWeight X (y + 1) *
          (FriableAsymptotic.primeLogSumUpTo y - (y : ℝ)) -
        ∑ m ∈ Finset.Ioc y (Z - 1),
          (roughSaiasNormalFormThetaWeight X (m + 1) -
              roughSaiasNormalFormThetaWeight X m) *
            (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) :=
  roughSaiasThetaErrorTransfer_eq_finiteAbel hyZ

example (X m : ℕ) :
    roughSaiasNormalFormThetaWeight X m =
      roughSaiasNaturalQuotientThetaWeight X m +
        roughSaiasFractionalCorrectionThetaWeight X m :=
  roughSaiasNormalFormThetaWeight_eq_natural_add_fractional X m

example (X m : ℕ) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      (roughSaiasNormalFormThetaWeight X (m + 1) -
          roughSaiasNormalFormThetaWeight X m) -
        (roughSaiasFractionalCorrectionThetaWeight X (m + 1) -
          roughSaiasFractionalCorrectionThetaWeight X m) :=
  roughSaiasNaturalQuotientThetaWeight_diff_eq_paired X m

example {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasSignedAbelCenter X y Z =
      roughSaiasNaturalIntegerAbelConsistencyDefect X y Z +
        roughSaiasFractionalThetaErrorTransfer X y Z :=
  roughSaiasSignedAbelCenter_eq_natural_add_fractionalTheta hyZ

example (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z :=
  roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta X y Z

example {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      roughSaiasNaturalQuotientThetaWeight X Z *
          (FriableAsymptotic.primeLogSumUpTo Z - (Z : ℝ)) -
        roughSaiasNaturalQuotientThetaWeight X (y + 1) *
          (FriableAsymptotic.primeLogSumUpTo y - (y : ℝ)) -
        ∑ m ∈ Finset.Ioc y (Z - 1),
          (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
              roughSaiasNaturalQuotientThetaWeight X m) *
            (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) :=
  roughSaiasNaturalThetaErrorTransfer_eq_finiteAbel hyZ

example {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hX₀y : X₀ ≤ y) (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasSignedAbelCenter X y Z| ≤
      roughSaiasThetaPNTLedger A C X y Z :=
  roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le
    htheta hX₀y hyZ

example {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasSignedAbelCenter X y Z| ≤
      roughSaiasThetaPNTLedger (4 : ℝ)
        roughSaiasThetaFourthPowerConstant X y Z :=
  roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le_fourthPower
    hY hyZ

example {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| ≤
      roughSaiasNaturalThetaPNTLedger (4 : ℝ)
        roughSaiasThetaFourthPowerConstant X y Z :=
  roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le_fourthPower
    hY hyZ

end

end Erdos390.WholePaper
