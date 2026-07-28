import Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature

/-!
# Expanded statement audit for canonical prefix quadrature

The census covers both public definitions and all four public theorems.
The two private finite-set helpers are covered transitively by the public
full-reciprocal-sum comparison.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

noncomputable section

/-! ## Complete public declaration census -/

#check bankPaperCanonicalHarmonicPointwiseUpper
#check bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper
#check bankPaperCanonicalHarmonicTailMajorant
#check tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
#check tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
#check bankPaperCanonicalRoundedSelectorTangentInput_of_harmonicTailGeometry

/-! ## Exact pointwise and endpoint majorants -/

example {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalHarmonicPointwiseUpper scale p =
      scale / (bankPaperCanonicalTangentPrimeLabel p : Real) := by
  rfl

example {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        bankPaperCanonicalHarmonicPointwiseUpper scale p = scale :=
  bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper scale p

example (scale : Real) (A Y : Nat) :
    bankPaperCanonicalHarmonicTailMajorant scale A Y =
      scale *
        (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3) := by
  rfl

/-! The finite reduction asks only that the declared strict tail be a
subset of `(A,Y]`; it does not identify the tail with that interval. -/
example
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      if bandOf p = band ∧ cut < cellIndex p then
        scale / (bankPaperCanonicalTangentPrimeLabel p : Real)
      else 0) <=
      scale * (fullReciprocalSum Y - fullReciprocalSum A) := by
  simpa only [tangentRatioCellTailPointwiseUpper,
    bankPaperCanonicalHarmonicPointwiseUpper] using
    tangentRatioCellTail_harmonicPointwiseUpper_le_fullReciprocalSum_sub
      bandOf cellIndex scale hscale band cut A Y hAY hgeometry

/-! The analytic corollary exposes the literal log-log main term and the
verified uniform endpoint error. -/
example
    {n W : Nat} {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (scale : Real) (hscale : 0 <= scale)
    (band : Band) (cut A Y : Nat)
    (hA : fullReciprocalSumUniformCutoff <= A) (hAY : A <= Y)
    (hgeometry : forall p : BankPaperCanonicalTangentPrime n W,
      bandOf p = band -> cut < cellIndex p ->
        A < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= Y) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
      if bandOf p = band ∧ cut < cellIndex p then
        scale / (bankPaperCanonicalTangentPrimeLabel p : Real)
      else 0) <=
      scale *
        (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)) +
          5 * fullReciprocalSumUniformConstant /
            Real.log (A : Real) ^ 3) := by
  simpa only [tangentRatioCellTailPointwiseUpper,
    bankPaperCanonicalHarmonicPointwiseUpper,
    bankPaperCanonicalHarmonicTailMajorant] using
    tangentRatioCellTail_harmonicPointwiseUpper_le_uniformMajorant
      bandOf cellIndex scale hscale band cut A Y hA hAY hgeometry

/-! The constructor keeps every rounding and band-balance premise visible;
the only analytic replacement is the uniform harmonic tail majorant. -/
example
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (tailLower tailUpper : Band -> Nat -> Nat)
    (scale : Real) (selector : Nat -> Real)
    (hscale : 0 <= scale)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector)
    (hprimeBandBalance :
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector)
    (hdeficitSupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <=
        bankPaperCanonicalHarmonicPointwiseUpper scale p)
    (hlowerCutoff : forall band cut,
      fullReciprocalSumUniformCutoff <= tailLower band cut)
    (hendpoints : forall band cut,
      tailLower band cut <= tailUpper band cut)
    (hgeometry : forall band cut
        (p : BankPaperCanonicalTangentPrime n W),
      bandOf p = band -> cut < cellIndex p ->
        tailLower band cut < bankPaperCanonicalTangentPrimeLabel p ∧
          bankPaperCanonicalTangentPrimeLabel p <= tailUpper band cut) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
          (tailLower band cut) (tailUpper band cut)) selector :=
  bankPaperCanonicalRoundedSelectorTangentInput_of_harmonicTailGeometry
    R certificate fixed candidates bandOf cellIndex tailLower tailUpper
      scale selector hscale hselector hrowIntegral hprimeBandBalance
      hdeficitSupport hbalance hpointwise hlowerCutoff hendpoints hgeometry

end

end Erdos390.WholePaper
