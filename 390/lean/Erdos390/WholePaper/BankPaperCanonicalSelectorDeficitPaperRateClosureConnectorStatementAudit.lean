import Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitPaperRateClosureConnector

/-!
# Statement audit for the canonical selector-deficit paper-rate closure

The audited interface keeps the source-to-guarded and guarded-to-raw
defects separate, transports the exact signs through structured placement,
and exposes the three remaining medium-prime implementation estimates.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

#check roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
#check bankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex_iff_defect_eq_zero
#check roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect_eq_sourceToGuarded_add_guardedRaw
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment
#check bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceToGuardedDefect_sub_guardedRawDefect_sub_moment_of_chargeDvd
#check RoughCanonicalBalancedRawSignedValuationResidualBound
#check BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
#check abs_sub_sub_sub_le_scale
#check abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_complete_and_implementation
#check abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_complete_and_implementation_of_chargeDvd
#check abs_bankPaperCanonicalPostHfitStructuredPreSelector_deficit_le_scale_of_components
#check roughCanonicalBalancedCompleteSignedResidual
#check roughCanonicalPostHfitCompleteSignedResidual_eq_balanced
#check exists_eventually_roughCanonicalBalancedCompleteSignedResidualBound_of_raw

/-- The quantitative bookkeeping adds one constant for each of the three
independently visible implementation terms. -/
example
    {base sourceDefect guardedRawDefect placement scale
      Cbase Csource CguardedRaw Cplacement : Real}
    (hbase : abs base <= Cbase * scale)
    (hsource : abs sourceDefect <= Csource * scale)
    (hguardedRaw :
      abs guardedRawDefect <= CguardedRaw * scale)
    (hplacement : abs placement <= Cplacement * scale) :
    abs (base - sourceDefect - guardedRawDefect - placement) <=
      (Cbase + Csource + CguardedRaw + Cplacement) * scale :=
  abs_sub_sub_sub_le_scale
    hbase hsource hguardedRaw hplacement

/-- The generic eventual closure really leaves only the raw signed
residual as a premise; the exceptional, row-correction, and guard terms are
already discharged in its conclusion. -/
example
    (W K0 depth : Nat) {c deltaStar beta Craw epsilon : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hepsilon : 0 < epsilon)
    (hTwoW : 2 <= W) (hprefix : 2 * depth + 1 <= W) :
    ∃ Cexceptional : Real, 0 <= Cexceptional ∧
      ∀ᶠ n : Nat in atTop,
        ∀ (R : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)))
          (left right : Nat -> Nat) (changed : Finset Nat)
          (certificate : GuardedCentralAnchorCertificate c depth n
            left right changed) (p : Nat),
        (0 <= roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n) ∧
          roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n) <= 1) ->
        (0 <= beta / L n ∧ beta / L n <= 1) ->
        p.Prime -> W < p -> p <= yNat n ->
        RoughCanonicalBalancedRawSignedValuationResidualBound
          W n K0 c beta p
            (Craw * secondOrderScale n / ((p : Real) * L n)) ->
        abs (R.roughCanonicalBalancedCompleteSignedResidual
          W K0 certificate deltaStar beta p) <=
          (Craw + Cexceptional +
              roughCanonicalUniformRawRowCorrectionDensityConstant
                W K0 c beta +
              epsilon) *
            secondOrderScale n / ((p : Real) * L n) :=
  exists_eventually_roughCanonicalBalancedCompleteSignedResidualBound_of_raw
    W K0 depth hc hdelta hdeltaUpper hepsilon hTwoW hprefix

end BankPaperRealization

end

end Erdos390.WholePaper
