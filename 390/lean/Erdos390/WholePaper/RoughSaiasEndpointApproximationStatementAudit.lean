import Erdos390.WholePaper.RoughSaiasEndpointApproximation

/-! Statement checks separating the closed inverse-log witness from the
conditional inverse-log-square defect reduction. -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

#check roughSaiasDickmanEndpointConstant
#check roughSaiasDickmanEndpointConstant_pos
#check roughSaiasDickmanEndpointCutoff
#check roughSaiasDickmanEndpoint_bound
#check roughSaiasInvLogEndpointRate
#check roughSaiasEndpointError_eq_friableCount_sub_lambdaNormalForm
#check roughSaiasInvLogEndpointApproximationUpToFive
#check roughSaiasLambdaNormalForm_endpoint_invLog_bound
#check roughSaiasReverseNormalFormDefect
#check roughSaiasEndpointError_reverseRecurrence
#check roughSaiasEndpointError_reverseRecurrence_top
#check RoughSaiasReverseNormalFormDefectInvLogSqBound
#check roughSaiasPrimeInvLogContractionCutoff
#check roughSaiasPrimeInvLogContraction_bound
#check roughSaiasPrimeInvLogSqSum
#check roughSaiasPrimeInvLogSqSum_contraction
#check roughSaiasInvLogSqEndpointRate
#check roughSaiasInvLogSqEndpointCutoff
#check roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect
#check roughSaiasLambdaNormalForm_endpoint_invLogSq_bound_of_defect

example : RoughSaiasEndpointApproximationUpToFive
    roughSaiasInvLogEndpointRate roughSaiasDickmanEndpointCutoff :=
  roughSaiasInvLogEndpointApproximationUpToFive

example {X y : ℕ} (hY : roughSaiasDickmanEndpointCutoff ≤ y)
    (hX : 0 < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(FriableAsymptotic.friableCount X y : ℝ) -
        (X : ℝ) * rho
          (FriableAsymptotic.dickmanU X y)| ≤
      roughSaiasDickmanEndpointConstant * (X : ℝ) /
        Real.log (y : ℝ) :=
  roughSaiasDickmanEndpoint_bound hY hX hlog

example (X y : ℕ) :
    roughSaiasEndpointError X y =
      (FriableAsymptotic.friableCount X y : ℝ) -
        roughSaiasLambdaNormalForm (X : ℝ) y :=
  roughSaiasEndpointError_eq_friableCount_sub_lambdaNormalForm X y

example {X y : ℕ} (hY : roughSaiasDickmanEndpointCutoff ≤ y)
    (hy2 : 2 ≤ y) (hX : 0 < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(FriableAsymptotic.friableCount X y : ℝ) -
        roughSaiasLambdaNormalForm (X : ℝ) y| ≤
      roughSaiasInvLogEndpointRate y * (X : ℝ) :=
  roughSaiasLambdaNormalForm_endpoint_invLog_bound hY hy2 hX hlog

example {X y : ℕ} (hX2 : 2 ≤ X) (hyX : y ≤ X) :
    roughSaiasEndpointError X y =
      roughSaiasReverseNormalFormDefect X y X -
        ∑ p ∈ roughReversePrimeInterval y X,
          roughSaiasEndpointError (X / p) p :=
  roughSaiasEndpointError_reverseRecurrence_top hX2 hyX

example {X y Z : ℕ} (hX : 0 < X) (hyZ : y ≤ Z) :
    roughSaiasEndpointError X y =
      roughSaiasEndpointError X Z -
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughSaiasEndpointError (X / p) p +
        roughSaiasReverseNormalFormDefect X y Z :=
  roughSaiasEndpointError_reverseRecurrence hX hyZ

example {y X : ℕ}
    (hY : roughSaiasPrimeInvLogContractionCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyX : y < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    roughSaiasPrimeInvLogSqSum y X ≤
      9 / (10 * Real.log (y : ℝ) ^ 2) :=
  roughSaiasPrimeInvLogSqSum_contraction hY hy2 hyX hlog

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀) :
    RoughSaiasEndpointApproximationUpToFive
      (roughSaiasInvLogSqEndpointRate C)
      (roughSaiasInvLogSqEndpointCutoff Y₀) :=
  roughSaiasInvLogSqEndpointApproximationUpToFive_of_defect hC hdefect

example {C : ℝ} {Y₀ X y : ℕ} (hC : 0 ≤ C)
    (hdefect : RoughSaiasReverseNormalFormDefectInvLogSqBound C Y₀)
    (hY : roughSaiasInvLogSqEndpointCutoff Y₀ ≤ y)
    (hy2 : 2 ≤ y) (hX : 0 < X)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(FriableAsymptotic.friableCount X y : ℝ) -
        roughSaiasLambdaNormalForm (X : ℝ) y| ≤
      roughSaiasInvLogSqEndpointRate C y * (X : ℝ) :=
  roughSaiasLambdaNormalForm_endpoint_invLogSq_bound_of_defect
    hC hdefect hY hy2 hX hlog

end

end Erdos390.WholePaper
