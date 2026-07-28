import Erdos390.WholePaper.RoughSaiasSharpCorrectionTarget

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

#check roughSaiasFullyRealCorrectionIntegrand
#check roughSaiasSharpCorrectionObstruction
#check roughSaiasDickmanContinuousPrimeDiscrepancy
#check roughSaiasLocalNaturalPrimeCellDiscrepancy
#check roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy
#check roughSaiasDualSpreadFullyRealNaturalCellRemainder
#check roughSaiasFullyRealCorrectionIntegrand_eq
#check roughSaiasReverseNormalFormDefect_eq_dickman_add_sharpCorrection
#check roughSaiasDickmanContinuousPrimeDiscrepancy_eq_riemann_sub_theta
#check roughSaiasSharpCorrectionObstruction_eq_naturalCells_sub_riemann_sub_residual
#check roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_localPrimeErrorResidual
#check roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
#check sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_split
#check sum_roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy_eq
#check sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_dualInvolution
#check sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_eq
#check sum_roughSaiasFullyRealNaturalCells_eq_dualInvolution
#check sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_integral_sub_primeTheta
#check roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_selectorCellLedger
#check roughSaiasNatHyperbolaCoefficient_sub_succ_eq_selectorCellLedger
#check roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
#check sum_roughSaiasSelectorCellLedger_mul_fourth_le
#check sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
#check sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
#check roughSaiasNaturalThetaPNTVariationLedger_fourth_le_invLogSq
#check roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_explicit
#check roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
#check roughSaiasNaturalThetaErrorTransfer_abs_le_upper_invLogSq
#check roughSaiasNaturalThetaErrorTransfer_abs_le_invLogSq
#check roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
#check roughSaiasReverseNormalFormDefect_self_abs_le_dualLowerNaturalCells_add_invLogSq
#check abs_sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_upper_le_invLogSq
#check roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
#check roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerLocal_add_upperInvLogSq
#check roughSaiasReverseNormalFormDefect_self_abs_le_upperInvLogSq_of_sqrt_succ_le
#check roughSaiasReverseNormalFormDefect_self_abs_le_dualLower_add_upperInvLogSq
#check roughSaiasDickmanContinuousPrimeDiscrepancy_abs_le_invLogSq
#check roughSaiasReverseNormalFormDefect_abs_le_closed_add_sharpCorrection
#check abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
#check abs_sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_le_forty_invLogSq
#check roughSaiasSharpDefectConstant
#check roughSaiasSharpDefectCutoff
#check roughSaiasReverseNormalFormDefect_self_abs_le_sharp_invLogSq
#check roughSaiasSharpReverseNormalFormDefectInvLogSqBound
#check roughSaiasSharpEndpointApproximationUpToFive

example {X : ℕ} {s : ℝ} (hX : 0 < X) (hs : 1 < s) :
    roughSaiasFullyRealCorrectionIntegrand X s =
      (((X : ℝ) / s) *
          (roughSaiasFullyRealG s
              (Real.log ((X : ℝ) / s) / Real.log s) -
            rho (Real.log (X : ℝ) / Real.log s - 1)) -
        Int.fract ((X : ℝ) / s)) /
      Real.log s :=
  roughSaiasFullyRealCorrectionIntegrand_eq hX hs

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasDickmanContinuousPrimeDiscrepancy X y Z +
        roughSaiasSharpCorrectionObstruction X y Z :=
  roughSaiasReverseNormalFormDefect_eq_dickman_add_sharpCorrection
    hy2 hyZ hZX hu5

example (X y Z : ℕ) (hyZ : y < Z) :
    roughSaiasDickmanContinuousPrimeDiscrepancy X y Z =
      roughSaiasDickmanBuchstabBlockRemainder X y Z -
        (FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y Z -
          FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y Z) :=
  roughSaiasDickmanContinuousPrimeDiscrepancy_eq_riemann_sub_theta X y Z hyZ

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasSharpCorrectionObstruction X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      roughSaiasDickmanBuchstabBlockRemainder X y Z -
      roughSaiasNaturalMinusDickmanThetaTransfer X y Z :=
  roughSaiasSharpCorrectionObstruction_eq_naturalCells_sub_riemann_sub_residual
    hy2 hyZ hZX hu5

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      ∑ m ∈ Finset.Ioc y Z,
        roughSaiasNaturalQuotientThetaWeight X m *
          (FriableAsymptotic.primeLogIncrement m - 1) :=
  roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_localPrimeErrorResidual
    hy2 hyZ hZX hu5

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m :=
  roughSaiasReverseNormalFormDefect_eq_sum_localNaturalPrimeCellDiscrepancy
    hy2 hyZ hZX hu5

example (X : ℕ) {y M Z : ℕ} (hyM : y ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico y Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m :=
  sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_split X hyM hMZ

example {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    (∑ _q ∈ roughSaiasDualQuotientInterval X m,
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X m) =
      roughSaiasLocalNaturalPrimeCellDiscrepancy X m :=
  sum_roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy_eq hm hmsqrt

example {X y M : ℕ} (hy : 0 < y) (hyM : y ≤ M)
    (hM : M ≤ Nat.sqrt X + 1) :
    (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y),
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X (X / q) :=
  sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_dualInvolution
    hy hyM hM

example {X m : ℕ} (hm : 0 < m) (hmsqrt : m ≤ Nat.sqrt X) :
    (∑ _q ∈ roughSaiasDualQuotientInterval X m,
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X m) =
      roughSaiasFullyRealNaturalBuchstabCellRemainder X m :=
  sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_eq hm hmsqrt

example {X y M : ℕ} (hy : 0 < y) (hyM : y ≤ M)
    (hM : M ≤ Nat.sqrt X + 1) :
    (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
      ∑ q ∈ Finset.Ioc (X / M) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q) :=
  sum_roughSaiasFullyRealNaturalCells_eq_dualInvolution hy hyM hM

example {X y M : ℕ} (hy2 : 2 ≤ y) (hyM : y < M) (hMX : M ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m) =
      (∫ s in (y : ℝ)..(M : ℝ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) -
      FriableAsymptotic.primeThetaWeightedInterval
        (roughSaiasNaturalQuotientThetaWeight X) y M :=
  sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_eq_integral_sub_primeTheta
    hy2 hyM hMX hu5

example {X m : ℕ} (hm3 : 3 ≤ m) (hupper : X ≤ (m - 1) ^ 2) :
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| ≤
      roughSaiasSelectorCellLedger X m :=
  roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_selectorCellLedger
    hm3 hupper

example (X m : ℕ) :
    ((X / m : ℕ) : ℝ) / Real.log (m : ℝ) -
        ((X / (m + 1) : ℕ) : ℝ) /
          Real.log ((m + 1 : ℕ) : ℝ) =
      roughSaiasSelectorCellLedger X m :=
  roughSaiasNatHyperbolaCoefficient_sub_succ_eq_selectorCellLedger X m

example {X a b m : ℕ} (ha2 : 2 ≤ a) (_hab : a ≤ b) (hbX : b ≤ X)
    (hm : m ∈ Finset.Ico a b)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m| ≤
      16 * roughSaiasSelectorCellLedger X m +
        ((X : ℝ) / ((m : ℝ) * Real.log (m : ℝ))) *
          (|rho (Real.log ((X / (m + 1) : ℕ) : ℝ) /
                  Real.log ((m + 1 : ℕ) : ℝ)) -
              rho (Real.log ((X / m : ℕ) : ℝ) /
                Real.log (m : ℝ))| +
            |roughSaiasBaseFreeFractionalIntegral (X / (m + 1)) (m + 1) -
              roughSaiasBaseFreeFractionalIntegral (X / m) m|) :=
  roughSaiasNaturalQuotientThetaWeight_succ_sub_abs_le_hyperbolaComponents
    ha2 _hab hbX hm hu5

example {C : ℝ} (hC : 0 ≤ C) (X : ℕ) {M Z : ℕ}
    (hM2 : 2 ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        roughSaiasSelectorCellLedger X m *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 :=
  sum_roughSaiasSelectorCellLedger_mul_fourth_le hC X hM2 hMZ

example {C : ℝ} (hC : 0 ≤ C) {X a b : ℕ}
    (ha2 : 2 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      16 * (C * (X : ℝ) * (2 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (b : ℝ)) /
          Real.log (a : ℝ) ^ 6) +
        (C * (X : ℝ) / Real.log (a : ℝ) ^ 5) *
          (1 + 2 / Real.log (a : ℝ)) :=
  sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_hyperbola
    hC ha2 hab hbX hu5

example {C : ℝ} (hC : 0 ≤ C) {X a b : ℕ}
    (ha3 : 3 ≤ a) (hab : a ≤ b) (hbX : b ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    (∑ m ∈ Finset.Ico a b,
        |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 4))) ≤
      211 * C * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
  sum_roughSaiasNaturalThetaWeightVariation_mul_fourth_le_invLogSq
    hC ha3 hab hbX hu5

example {C : ℝ} (hC : 0 ≤ C) {X y Z : ℕ}
    (hy3 : 3 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X y Z ≤
      211 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
  roughSaiasNaturalThetaPNTVariationLedger_fourth_le_invLogSq
    hC hy3 hyZ hZX hu5

example {C : ℝ} (hC : 0 ≤ C) {X M Z : ℕ}
    (hM2 : 2 ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      C * (X : ℝ) * (2 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 5 +
        C * (X : ℝ) * (1 + Real.log (Z : ℝ)) /
          Real.log (M : ℝ) ^ 6 :=
  roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_explicit
    hC hM2 hMZ hupper

example {C : ℝ} (hC : 0 ≤ C) {X M Z : ℕ}
    (hM3 : 3 ≤ M) (hMZ : M ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ) C X M Z ≤
      13 * C * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
  roughSaiasNaturalThetaPNTVariationLedger_fourth_le_upper_invLogSq
    hC hM3 hMZ hZX hu5 hupper

example {X M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ M)
    (hM3 : 3 ≤ M) (hMZ : M < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    |roughSaiasNaturalThetaErrorTransfer X M Z| ≤
      45 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 :=
  roughSaiasNaturalThetaErrorTransfer_abs_le_upper_invLogSq
    hY hM3 hMZ hZX hu5 hupper

example {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      243 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasNaturalThetaErrorTransfer_abs_le_invLogSq
    hY hy3 hyZ hZX hu5

example {X y M Z : ℕ} (hX : 0 < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_abs_le_lowerNaturalCells_add_invLogSq
    hX hY hy3 hyZ hZX hu5 hyM hMZ hupper

example {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hysqrt : y ≤ Nat.sqrt X + 1) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ q ∈ Finset.Ioc (X / (Nat.sqrt X + 1)) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q)| +
      (3 + 243 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_self_abs_le_dualLowerNaturalCells_add_invLogSq
    hY hy3 hyX hu5 hysqrt

example {X M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ M)
    (hM3 : 3 ≤ M) (hMZ : M ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (M : ℝ) ≤ 5)
    (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| ≤
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (M : ℝ) ^ 2 :=
  abs_sum_roughSaiasLocalNaturalPrimeCellDiscrepancy_upper_le_invLogSq
    hY hM3 hMZ hZX hu5 hupper

example {X y M Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_abs_le_lowerLocal_add_upperInvLogSq
    hY hy3 hyZ hZX hu5 hyM hMZ hupper

example {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ m ∈ Finset.Ico y (roughSaiasSelectorTransition X y),
        roughSaiasLocalNaturalPrimeCellDiscrepancy X m| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerLocal_add_upperInvLogSq
    hY hy3 hyX hu5

example {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hsqrt : Nat.sqrt X + 1 ≤ y) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_self_abs_le_upperInvLogSq_of_sqrt_succ_le
    hY hy3 hyX hu5 hsqrt

example {X y : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy3 : 3 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hysqrt : y ≤ Nat.sqrt X + 1) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ q ∈ Finset.Ioc (X / (Nat.sqrt X + 1)) (X / y),
        roughSaiasDualSpreadLocalNaturalPrimeCellDiscrepancy X (X / q)| +
      (3 + 45 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_self_abs_le_dualLower_add_upperInvLogSq
    hY hy3 hyX hu5 hysqrt

example {X y Z : ℕ}
    (hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hYriemann : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasDickmanContinuousPrimeDiscrepancy X y Z| ≤
      (1 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasDickmanContinuousPrimeDiscrepancy_abs_le_invLogSq
    hYtheta hYriemann hX hy2 hyZ hZX hu5

example {X y Z : ℕ}
    (hYtheta : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hYriemann : roughSaiasRiemannAbsorptionCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      (1 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasSharpCorrectionObstruction X y Z| :=
  roughSaiasReverseNormalFormDefect_abs_le_closed_add_sharpCorrection
    hYtheta hYriemann hX hy2 hyZ hZX hu5

example {X a b : ℕ} (hX : 0 < X) (ha3 : 3 ≤ a) (hab : a ≤ b)
    (hbX : b ≤ X) (hbSqrt : b ≤ Nat.sqrt X + 1)
    (hu5 : Real.log (X : ℝ) / Real.log (a : ℝ) ≤ 5) :
    |∑ m ∈ Finset.Ico a b,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      40 * (X : ℝ) / Real.log (a : ℝ) ^ 2 :=
  abs_sum_roughSaiasFullyRealNaturalCells_lower_le_forty_invLogSq
    hX ha3 hab hbX hbSqrt hu5

example {X y : ℕ} (hX : 0 < X) (hy3 : 3 ≤ y)
    (hySqrt : y ≤ Nat.sqrt X + 1)
    (hMX : Nat.sqrt X + 1 ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |∑ q ∈ Finset.Ioc (X / (Nat.sqrt X + 1)) (X / y),
        roughSaiasDualSpreadFullyRealNaturalCellRemainder X (X / q)| ≤
      40 * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
  abs_sum_roughSaiasDualSpreadFullyRealNaturalCellRemainder_le_forty_invLogSq
    hX hy3 hySqrt hMX hu5

example {X y : ℕ} (hY : roughSaiasSharpDefectCutoff ≤ y)
    (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      roughSaiasSharpDefectConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 :=
  roughSaiasReverseNormalFormDefect_self_abs_le_sharp_invLogSq
    hY hyX hu5

example :
    RoughSaiasReverseNormalFormDefectInvLogSqBound
      roughSaiasSharpDefectConstant roughSaiasSharpDefectCutoff :=
  roughSaiasSharpReverseNormalFormDefectInvLogSqBound

example :
    RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
      (roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff) :=
  roughSaiasSharpEndpointApproximationUpToFive

end

end Erdos390.WholePaper
