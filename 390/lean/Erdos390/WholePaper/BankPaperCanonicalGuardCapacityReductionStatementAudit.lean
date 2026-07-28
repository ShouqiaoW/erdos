import Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction

/-! # Statement audit for canonical guard-capacity reduction -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

example {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a :=
  prime_dvd_completeRoughLabel_of_cutoff_lt hp hyp ha hpa

example {n y p : Nat} (hn : 0 < n) (hyTwo : 2 <= y)
    (hp : p.Prime) (hpy : p <= y) :
    completeRoughLabel y (promotedCentralFactor n p) = 1 :=
  completeRoughLabel_promotedCentralFactor_eq_one_of_base_le
    hn hyTwo hp hpy

example
    {depth n y : Nat} {q : Nat -> Nat}
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (hq : IsLargeCentralCofactorChoice n
      (centralAnchorCutoff depth n) q)
    {a b : Nat}
    (ha : a ∈ fullCentralAnchors n (centralAnchorCutoff depth n) q)
    (hb : b ∈ fullCentralAnchors n (centralAnchorCutoff depth n) q)
    (haNontrivial : completeRoughLabel y a ≠ 1)
    (hab : completeRoughLabel y a = completeRoughLabel y b) :
    a = b :=
  fullCentralAnchors_completeRoughLabel_injective_of_ne_one
    hnCutoff hyTwo hyCutoff hq ha hb haNontrivial hab

example
    {c : Real} {depth n y : Nat} {left right : Nat -> Nat}
    {changed candidates : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (label : Nat) (hlabel : label ≠ 1) :
    (completeRoughRowFiber y candidates label ∩
      certificate.anchors).card <= 1 :=
  completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
    certificate hnCutoff hyTwo hyCutoff label hlabel

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    (R.marker request).Prime :=
  R.paperMarker_prime request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    yNat n < R.marker request :=
  R.yNat_lt_paperMarker request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeDonorValue request) =
      completeRoughSignature (yNat n) (R.marker request) :=
  R.prechargeDonor_completeRoughSignature_eq_marker request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) :=
  R.prechargeBase_completeRoughSignature_eq_marker request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) :=
  R.prechargeAlternate_completeRoughSignature_eq_marker request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.marker request) = R.marker request :=
  R.completeRoughLabel_paperMarker request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      R.marker request :=
  R.prechargeBase_completeRoughLabel_eq_marker request

example {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) = R.marker request :=
  R.prechargeAlternate_completeRoughLabel_eq_marker request

example {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n) (R.prechargeBaseStateValue request)) :=
  R.prechargeBase_completeRoughLabel_injective

example {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request)) :=
  R.prechargeAlternate_completeRoughLabel_injective

example {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeBaseState).card <= 1 :=
  R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one candidates

example {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeAlternateState).card <= 1 :=
  R.completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
    candidates

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hlabel : label ≠ 1) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 :=
  R.roughCanonicalGuardLocalCensusBound_three_of_ne_one certificate
    deltaStar K label hnCutoff hyCutoff hlabel

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K budget poolMinimum : Nat) :
    RoughCanonicalActiveRawBroadSurplus R certificate deltaStar W K
        budget poolMinimum ↔
      ∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          max poolMinimum
              (roughUpperCompleteRoughRowTarget n h (yNat n) label) +
                budget <=
            (roughCanonicalBroadCorrectionPool W n h K (yNat n)
              label).card := by
  rfl

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 :=
  R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
    deltaStar K label hnCutoff hyCutoff hactive

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum budget : Nat)
    (hcensus : RoughCanonicalGuardLocalCensusBound R certificate deltaStar
      K label budget)
    (hraw : minimum + budget <=
      (roughCanonicalBroadCorrectionPool W n h K (yNat n) label).card) :
    RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar W K
      label minimum :=
  R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus certificate
    deltaStar W K label minimum budget hcensus hraw

example {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) (label : Nat) :
    R.roughCanonicalPostchargeRowTarget deltaStar label <=
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) :=
  R.roughCanonicalPostchargeRowTarget_le_upperTarget deltaStar label

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum : Nat)
    (hupper : roughUpperCompleteRoughRowTarget n h (yNat n) label <= minimum)
    (hpool : RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
      W K label minimum) :
    RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label :=
  R.roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
    certificate deltaStar W K label minimum hupper hpool

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K poolMinimum : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hsurplus : RoughCanonicalActiveRawBroadSurplus R certificate deltaStar
      W K 3 poolMinimum) :
    (∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalGuardLocalCensusBound R certificate deltaStar K
          label 3) ∧
    (∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
          W K label poolMinimum) ∧
    (∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
          label) :=
  R.roughCanonical_active_guard_capacity_inputs_of_rawBroadSurplus
    certificate deltaStar W K poolMinimum hnCutoff hyCutoff hsurplus

end BankPaperRealization

end

end Erdos390.WholePaper
