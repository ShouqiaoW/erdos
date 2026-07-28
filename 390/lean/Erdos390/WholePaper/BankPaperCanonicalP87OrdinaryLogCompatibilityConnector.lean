import Erdos390.WholePaper.BankPaperCanonicalP87TargetEnvelopeConnector

/-!
# Exact ordinary-log propagation through the canonical P87 endpoint

The Proposition 8.7 path preserves the medium-prime logarithmic moment

`paperMoment primeLogScore`.

This file identifies that moment with the `tPrime`-weighted marked valuation
moments and transfers the preservation statement to the literal canonical
selector deficit.  Consequently the actual P87 endpoint satisfies the
ordinary-log compatibility required by the target-envelope connector whenever
the supplied pre-selector already satisfies it.

This is a propagation theorem, not a source theorem.  The presently exported
guarded pre-selector data contain exact unweighted band balances, but no
theorem forcing their `tPrime`-weighted sum to vanish.  Likewise, the scalar
`roughCanonicalCompleteSignedResidual` has not yet been identified with the
primewise valuation deficit of that pre-selector, so no such identification is
asserted here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## The prime-log moment is the weighted marked moment -/

/-- The medium-prime logarithmic moment is exactly the finite sum of the
normalized prime-log weights times the corresponding marked valuation
moments. -/
theorem bankPaperCanonicalPaperMoment_primeLogScore_eq_sum_markedValuation
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (xi : B.ParamSpace) :
    B.paperMoment B.primeLogScore xi =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          B.paperMoment (B.markedValuation p.1) xi := by
  change
    B.paperMoment
        (fun m =>
          ∑ p : BankPaperCanonicalTangentPrime
              B.sampleData.n B.sampleData.W,
            tPrime B.sampleData.n p.1 *
              B.markedValuation p.1 m) xi =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          B.paperMoment (B.markedValuation p.1) xi
  rw [B.paperMoment_fintype_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  exact B.paperMoment_const_mul
    (tPrime B.sampleData.n p.1) (B.markedValuation p.1) xi

/-- A `tPrime`-weighted active residual is the weighted target total minus
the medium-prime logarithmic moment. -/
theorem bankPaperCanonicalWeightedActiveResidual_eq_target_sub_primeLogMoment
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (markedTarget : Nat -> Real) (xi : B.ParamSpace) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        (markedTarget p.1 -
          B.paperMoment (B.markedValuation p.1) xi)) =
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * markedTarget p.1) -
        B.paperMoment B.primeLogScore xi := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        (markedTarget p.1 -
          B.paperMoment (B.markedValuation p.1) xi)) =
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          (tPrime B.sampleData.n p.1 * markedTarget p.1 -
            tPrime B.sampleData.n p.1 *
              B.paperMoment (B.markedValuation p.1) xi) := by
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ =
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 * markedTarget p.1) -
          ∑ p : BankPaperCanonicalTangentPrime
              B.sampleData.n B.sampleData.W,
            tPrime B.sampleData.n p.1 *
              B.paperMoment (B.markedValuation p.1) xi := by
      rw [Finset.sum_sub_distrib]
    _ =
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 * markedTarget p.1) -
          B.paperMoment B.primeLogScore xi := by
      rw [bankPaperCanonicalPaperMoment_primeLogScore_eq_sum_markedValuation]

/-! ## Literal endpoint and initial selector identities -/

/-- The weighted literal deficit of the actual P87 endpoint is the weighted
active target total minus its endpoint prime-log moment. -/
theorem bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p) =
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p.1) -
        B.paperMoment B.primeLogScore (path 1) := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p) =
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate
                fixed candidates preSelector activeSeed p.1 -
              B.paperMoment (B.markedValuation p.1) (path 1)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      unfold bankPaperCanonicalTangentResidual
      rw [bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
        B R certificate fixed candidates preSelector activeSeed
          hvalues path p.1]
    _ =
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed p.1) -
          B.paperMoment B.primeLogScore (path 1) :=
      bankPaperCanonicalWeightedActiveResidual_eq_target_sub_primeLogMoment
        B
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed)
        (path 1)

/-- The same exact formula at the initial pre-selector. -/
theorem bankPaperCanonicalActualInitialSelector_weightedResidual_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates preSelector p) =
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p.1) -
        B.paperMoment B.primeLogScore 0 := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates preSelector p) =
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate
                fixed candidates preSelector activeSeed p.1 -
              B.paperMoment (B.markedValuation p.1) 0) := by
      apply Finset.sum_congr rfl
      intro p _hp
      unfold bankPaperCanonicalTangentResidual
      rw [bankPaperCanonicalActualInitial_deficit_eq_activeResidual
        B R certificate fixed candidates preSelector activeSeed
          Hmeasure hseed p.1]
    _ =
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed p.1) -
          B.paperMoment B.primeLogScore 0 :=
      bankPaperCanonicalWeightedActiveResidual_eq_target_sub_primeLogMoment
        B
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed)
        0

/-! ## Exact P87 propagation -/

/-- Prime-log preservation along the actual P87 path is exactly preservation
of the weighted literal selector deficit. -/
theorem bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq_initial
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hprimeLog :
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p) =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates preSelector p := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p) =
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed p.1) -
          B.paperMoment B.primeLogScore (path 1) := by
      exact bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq
        B R certificate fixed candidates preSelector activeSeed
          (fun m =>
            bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m)
          path
    _ =
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed p.1) -
          B.paperMoment B.primeLogScore 0 := by
      rw [hprimeLog]
    _ =
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 *
            bankPaperCanonicalTangentResidual
              R certificate fixed candidates preSelector p := by
      exact (bankPaperCanonicalActualInitialSelector_weightedResidual_eq
        B R certificate fixed candidates preSelector activeSeed
          Hmeasure hseed).symm

/-- Therefore exact ordinary-log compatibility of the pre-selector is
inherited by the actual P87 endpoint. -/
theorem bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatible
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hprimeLog :
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0)
    (hinitial : BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W)
      R certificate fixed candidates preSelector) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W) R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatible at hinitial ⊢
  rw [bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq_initial
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed path hprimeLog]
  exact hinitial

/-- The preceding corollary specialized to the prime-log field exported by a
literal Proposition 8.7 path. -/
theorem bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatible_of_path
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (hpath : B.IsPaperProposition87Path Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate
        fixed candidates preSelector activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight
        B.sampleData candidates preSelector activeSeed)
      quota path)
    (hinitial : BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W)
      R certificate fixed candidates preSelector) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W) R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) := by
  rcases hpath with
    ⟨_hzero, _hball, _hsize, _hderiv, _hbands, _hphysical,
      _hordinary, _hheads, _hsmall, hprimeLog, _hmarked,
      _hfeasible, _hfixed, _hmass, _hquota⟩
  exact bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatible
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed path hprimeLog hinitial

end

end Erdos390.WholePaper
