import Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger

/-!
# Canonical rough-row guard capacity reduction

This file closes the finite part of the three guard-local obligations exposed
by `BankPaperCanonicalGuardLocalRowLedger`.

For every non-smooth complete rough row, at most one central anchor, one bank
base, and one bank alternate can occur.  Thus the literal local guard census
is at most three.  Removing those three possible coordinates from a raw broad
pool gives the guarded-pool capacity, and containment of the guarded broad
pool in the guarded row gives the postcharge capacity.

The only non-finite input left visible is `RoughCanonicalActiveRawBroadSurplus`:
the raw broad pool must contain the larger of the requested pool minimum and
the literal upper-row target, plus the three-coordinate guard slack.  This is
the exact de Bruijn--Saias lower-bound consequence still needed from the
analytic rough-row argument; it contains no selector or bookkeeping premise.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete rough labels remember retained prime divisors -/

/-- A prime divisor above the smooth cutoff is retained in the complete
rough label. -/
theorem prime_dvd_completeRoughLabel_of_cutoff_lt
    {y a p : Nat} (hp : p.Prime) (hyp : y < p)
    (ha : a ≠ 0) (hpa : p ∣ a) :
    p ∣ completeRoughLabel y a := by
  apply (hp.dvd_iff_one_le_factorization
    (completeRoughLabel_ne_zero y a)).mpr
  rw [completeRoughLabel_factorization_apply, if_pos hyp]
  exact (hp.dvd_iff_one_le_factorization ha).mp hpa

/-- A promoted central factor whose base prime is below the smooth cutoff
has trivial complete rough label. -/
theorem completeRoughLabel_promotedCentralFactor_eq_one_of_base_le
    {n y p : Nat} (hn : 0 < n) (hyTwo : 2 <= y)
    (hp : p.Prime) (hpy : p <= y) :
    completeRoughLabel y (promotedCentralFactor n p) = 1 := by
  apply (completeRoughLabel_eq_one_iff_mem_smoothNumbers
    (Nat.zero_lt_of_lt
      (promotedCentralFactor_gt (n := n) (p := p) hn))).2
  rw [Nat.mem_smoothNumbers']
  intro ell hell hellDvd
  rcases prime_dvd_promotedCentralFactor hp hell hellDvd with
      rfl | rfl
  · omega
  · omega

/-! ## One central anchor in every non-smooth row -/

/-- The full central-anchor map is injective after passing to any nontrivial
complete rough label whose cutoff lies below the large-marker cutoff.

Promoted anchors with base at most `y` lie in the smooth row.  A retained
promoted base prime recovers that promoted anchor.  For a routed large anchor,
its marker prime is retained and is too large to divide any other promoted
anchor or any other routed cofactor. -/
theorem fullCentralAnchors_completeRoughLabel_injective_of_ne_one
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
    a = b := by
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  rw [fullCentralAnchors] at ha hb
  rcases Finset.mem_union.mp ha with haPromoted | haLarge
  · obtain ⟨p, hpMem, rfl⟩ := Finset.mem_image.mp haPromoted
    have hpPrime := residualCentralPrimes_prime hpMem
    have hpSmall := residualCentralPrimes_le hpMem
    rcases Finset.mem_union.mp hb with hbPromoted | hbLarge
    · obtain ⟨p', hp'Mem, rfl⟩ := Finset.mem_image.mp hbPromoted
      have hp'Prime := residualCentralPrimes_prime hp'Mem
      have hpHigh : y < p := by
        by_contra hpNotHigh
        have hpLow : p <= y := Nat.le_of_not_gt hpNotHigh
        exact haNontrivial
          (completeRoughLabel_promotedCentralFactor_eq_one_of_base_le
            hn hyTwo hpPrime hpLow)
      have hpDvdPromoted : p ∣ promotedCentralFactor n p := by
        unfold promotedCentralFactor promotedBlock centralPrimeBlock
        exact dvd_mul_of_dvd_right
          (dvd_pow_self p
            (residualCentralPrimes_exponent_pos hpMem).ne') _
      have hpDvdLabel :
          p ∣ completeRoughLabel y (promotedCentralFactor n p) :=
        prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hpHigh
          (Nat.zero_lt_of_lt (promotedCentralFactor_gt hn)).ne'
          hpDvdPromoted
      have hpDvdOther : p ∣ promotedCentralFactor n p' := by
        apply hpDvdLabel.trans
        rw [hab]
        exact completeRoughLabel_dvd y (promotedCentralFactor n p')
      rcases prime_dvd_promotedCentralFactor hp'Prime hpPrime hpDvdOther with
          hpTwo | hpp'
      · omega
      · subst p'
        rfl
    · obtain ⟨P, hPMem, rfl⟩ := Finset.mem_image.mp hbLarge
      have hPPrime := largeCentralPrimes_prime hPMem
      have hPHigh : y < P :=
        hyCutoff.trans (largeCentralPrimes_gt hPMem)
      have hPAnchorPos : 0 < largeCentralAnchor q P := by
        exact Nat.zero_lt_of_lt
          (Finset.mem_Ioc.mp
            (largeCentralAnchor_mem_centralInterval hq hPMem)).1
      have hPDvdLabel :
          P ∣ completeRoughLabel y (largeCentralAnchor q P) :=
        prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
          hPAnchorPos.ne' (by
            exact dvd_mul_right P (q P))
      have hPDvdPromoted : P ∣ promotedCentralFactor n p := by
        apply hPDvdLabel.trans
        rw [← hab]
        exact completeRoughLabel_dvd y (promotedCentralFactor n p)
      exact (markerPrime_not_dvd_promotedCentralFactor hPPrime hpPrime
        (two_le_centralAnchorCutoff hnCutoff)
        (largeCentralPrimes_gt hPMem) hpSmall hPDvdPromoted).elim
  · obtain ⟨P, hPMem, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hPMem
    have hPHigh : y < P :=
      hyCutoff.trans (largeCentralPrimes_gt hPMem)
    have hPAnchorPos : 0 < largeCentralAnchor q P := by
      exact Nat.zero_lt_of_lt
        (Finset.mem_Ioc.mp
          (largeCentralAnchor_mem_centralInterval hq hPMem)).1
    have hPDvdLabel :
        P ∣ completeRoughLabel y (largeCentralAnchor q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        hPAnchorPos.ne' (by exact dvd_mul_right P (q P))
    rcases Finset.mem_union.mp hb with hbPromoted | hbLarge
    · obtain ⟨p, hpMem, rfl⟩ := Finset.mem_image.mp hbPromoted
      have hpPrime := residualCentralPrimes_prime hpMem
      have hpSmall := residualCentralPrimes_le hpMem
      have hPDvdPromoted : P ∣ promotedCentralFactor n p := by
        apply hPDvdLabel.trans
        rw [hab]
        exact completeRoughLabel_dvd y (promotedCentralFactor n p)
      exact (markerPrime_not_dvd_promotedCentralFactor hPPrime hpPrime
        (two_le_centralAnchorCutoff hnCutoff)
        (largeCentralPrimes_gt hPMem) hpSmall hPDvdPromoted).elim
    · obtain ⟨P', hP'Mem, rfl⟩ := Finset.mem_image.mp hbLarge
      have hP'Prime := largeCentralPrimes_prime hP'Mem
      have hPDvdOther : P ∣ largeCentralAnchor q P' := by
        apply hPDvdLabel.trans
        rw [hab]
        exact completeRoughLabel_dvd y (largeCentralAnchor q P')
      rw [largeCentralAnchor] at hPDvdOther
      rcases hPPrime.dvd_mul.mp hPDvdOther with hPP' | hPq
      · have hmarker : P = P' :=
          (Nat.prime_dvd_prime_iff_eq hPPrime hP'Prime).mp hPP'
        subst P'
        rfl
      · have hqPos : 0 < q P' :=
          largeCentralCofactor_pos hq hP'Mem
        have hPLeQ : P <= q P' := Nat.le_of_dvd hqPos hPq
        have hqLe : q P' <= 2 * depth + 1 :=
          largeCentralCofactor_le_fixedPrefix hq hP'Mem
        have hprefixCutoff :=
          two_mul_add_one_lt_centralAnchorCutoff hnCutoff
        have hcutoffP := largeCentralPrimes_gt hPMem
        omega

/-- Consequently, one fixed non-smooth rough row meets the guarded central
anchor set in at most one coordinate. -/
theorem completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
    {c : Real} {depth n y : Nat} {left right : Nat -> Nat}
    {changed candidates : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyTwo : 2 <= y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (label : Nat) (hlabel : label ≠ 1) :
    (completeRoughRowFiber y candidates label ∩
      certificate.anchors).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  apply fullCentralAnchors_completeRoughLabel_injective_of_ne_one
    hnCutoff hyTwo hyCutoff certificate.isCofactorChoice
  · simpa only [certificate.anchors_eq] using haData.2
  · simpa only [certificate.anchors_eq] using hbData.2
  · simpa only [haLabel] using hlabel
  · rw [haLabel, hbLabel]

namespace BankPaperRealization

/-! ## One base and one alternate in every bank row -/

/-- The global bank marker is prime. -/
theorem paperMarker_prime
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    (R.marker request).Prime := by
  cases request with
  | inl request =>
      exact R.bottom.marker_prime
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.marker_prime request

/-- Every global bank marker lies above the complete rough cutoff. -/
theorem yNat_lt_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    yNat n < R.marker request := by
  cases request with
  | inl request =>
      exact R.bottom.yNat_lt_marker R.ordinary.two_mul_n_le_M
        R.three_mul_yNat_le_n
        (bankBottomRelevantRequestToPaperRequest request)
  | inr request => exact R.ordinary.yNat_lt_marker request

/-- The actual donor has the same complete rough signature as its global
marker. -/
theorem prechargeDonor_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n) (R.prechargeDonorValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  cases request with
  | inl request =>
      let fullRequest := bankBottomRelevantRequestToPaperRequest request
      simpa only [prechargeDonorValue, marker, fullRequest,
        BankBottomPaperRealization.occurrenceValue_donor] using
        (R.bottom.occurrenceValue_completeRoughSignature R.six_le_yNat
          fullRequest .donor)
  | inr request =>
      have hsignature := completeRoughSignature_marker_mul_smooth_eq
        (y := yNat n) (P := R.ordinary.marker request)
        (a := R.ordinary.donorCore request) (b := 1)
        (R.ordinary.marker_prime request).ne_zero
        (R.ordinary.donorCore_smooth request)
        (by simp [Nat.mem_smoothNumbers])
      simpa only [prechargeDonorValue, marker,
        BankOrdinaryPaperRealization.donorValue, mul_one] using hsignature

theorem prechargeBase_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.prechargeBase_donor_completeRoughSignature_eq request).trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

theorem prechargeAlternate_completeRoughSignature_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughSignature (yNat n) (R.marker request) := by
  exact (R.precharge_completeRoughSignature_eq request).2.trans
    (R.prechargeDonor_completeRoughSignature_eq_marker request)

/-- A prime above the cutoff is its own complete rough label. -/
theorem completeRoughLabel_paperMarker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.marker request) = R.marker request := by
  have hprime := R.paperMarker_prime request
  have hhigh := R.yNat_lt_paperMarker request
  apply Nat.dvd_antisymm
  · exact completeRoughLabel_dvd (yNat n) (R.marker request)
  · exact prime_dvd_completeRoughLabel_of_cutoff_lt hprime hhigh
      hprime.ne_zero (dvd_refl (R.marker request))

theorem prechargeBase_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      R.marker request := by
  calc
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeBase_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeAlternate_completeRoughLabel_eq_marker
    {n M : Nat} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) = R.marker request := by
  calc
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
        completeRoughLabel (yNat n) (R.marker request) :=
      completeRoughSignature_eq_iff_label_eq.mp
        (R.prechargeAlternate_completeRoughSignature_eq_marker request)
    _ = R.marker request := R.completeRoughLabel_paperMarker request

theorem prechargeBase_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n) (R.prechargeBaseStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n) (R.prechargeBaseStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeBaseStateValue request') at heq
  simpa only [R.prechargeBase_completeRoughLabel_eq_marker] using heq

theorem prechargeAlternate_completeRoughLabel_injective
    {n M : Nat} (R : BankPaperRealization n M) :
    Function.Injective (fun request : BankPaperMarkerRequest n =>
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request)) := by
  intro request request' heq
  apply R.marker_injective
  change
    completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request) =
      completeRoughLabel (yNat n)
        (R.prechargeAlternateStateValue request') at heq
  simpa only [R.prechargeAlternate_completeRoughLabel_eq_marker] using heq

private theorem completeRoughRowFiber_inter_indexedPathState_card_le_one
    {C : Type*} [Fintype C] [DecidableEq C]
    {y label : Nat} {candidates : Finset Nat} (state : C -> Nat)
    (hinjective : Function.Injective
      (fun component => completeRoughLabel y (state component))) :
    (completeRoughRowFiber y candidates label ∩
      indexedPathState state).card <= 1 := by
  rw [Finset.card_le_one_iff]
  intro a b ha hb
  have haData := Finset.mem_inter.mp ha
  have hbData := Finset.mem_inter.mp hb
  have haLabel := (mem_completeRoughRowFiber.mp haData.1).2
  have hbLabel := (mem_completeRoughRowFiber.mp hbData.1).2
  rw [indexedPathState, Finset.mem_image] at haData hbData
  obtain ⟨component, _hcomponent, rfl⟩ := haData.2
  obtain ⟨component', _hcomponent', rfl⟩ := hbData.2
  apply congrArg state
  apply hinjective
  change completeRoughLabel y (state component) =
    completeRoughLabel y (state component')
  rw [haLabel, hbLabel]

theorem completeRoughRowFiber_inter_prechargeBaseState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeBaseState).card <= 1 := by
  classical
  rw [prechargeBaseState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeBaseStateValue
    R.prechargeBase_completeRoughLabel_injective

theorem completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
    {n M label : Nat} (R : BankPaperRealization n M)
    (candidates : Finset Nat) :
    (completeRoughRowFiber (yNat n) candidates label ∩
      R.prechargeAlternateState).card <= 1 := by
  classical
  rw [prechargeAlternateState]
  exact completeRoughRowFiber_inter_indexedPathState_card_le_one
    R.prechargeAlternateStateValue
    R.prechargeAlternate_completeRoughLabel_injective

/-! ## The literal three-coordinate local census -/

/-- In every non-smooth complete rough row, the numerical guards delete at
most one anchor, one bank base, and one bank alternate.  Fixed exceptional
factors and donors are in the upper tail and were already removed by the
support theorem in the local ledger. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_ne_one
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K label : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hlabel : label ≠ 1) :
    RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label 3 := by
  let rawRow := completeRoughRowFiber (yNat n)
    (roughRawCandidateSet n h K) label
  have hsubset :
      R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
        (rawRow ∩ certificate.anchors) ∪
          (rawRow ∩ R.prechargeBaseState) ∪
            (rawRow ∩ R.prechargeAlternateState) := by
    intro a ha
    have haDeleted := ha
    change a ∈ rawRow ∩
      R.roughCanonicalGuardSet certificate deltaStar at haDeleted
    have haRaw : a ∈ rawRow := by
      exact (Finset.mem_inter.mp haDeleted).1
    have haSupport :=
      R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
        certificate deltaStar K label ha
    rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
    · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_inter.mpr ⟨haRaw, haAnchor⟩
      · exact Finset.mem_union.mpr <| Or.inl <|
          Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_inter.mpr ⟨haRaw, haBase⟩
    · exact Finset.mem_union.mpr <| Or.inr <|
        Finset.mem_inter.mpr ⟨haRaw, haAlternate⟩
  have hanchor : (rawRow ∩ certificate.anchors).card <= 1 := by
    have hyTwo : 2 <= yNat n := by
      have hySix := R.six_le_yNat
      omega
    exact completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
      certificate hnCutoff hyTwo hyCutoff label hlabel
  have hbase : (rawRow ∩ R.prechargeBaseState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one
      (roughRawCandidateSet n h K)
  have halternate :
      (rawRow ∩ R.prechargeAlternateState).card <= 1 := by
    exact R.completeRoughRowFiber_inter_prechargeAlternateState_card_le_one
      (roughRawCandidateSet n h K)
  have hfirst := Finset.card_union_le
    (rawRow ∩ certificate.anchors) (rawRow ∩ R.prechargeBaseState)
  have hall := Finset.card_union_le
    ((rawRow ∩ certificate.anchors) ∪
      (rawRow ∩ R.prechargeBaseState))
    (rawRow ∩ R.prechargeAlternateState)
  have hcard := Finset.card_le_card hsubset
  exact show
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card <= 3
    by omega

/-- Active nonexceptional rows are non-smooth, so the preceding census
directly supplies the first Section 9 guard-local input. -/
theorem roughCanonicalGuardLocalCensusBound_three_of_active
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
  R.roughCanonicalGuardLocalCensusBound_three_of_ne_one certificate
    deltaStar K label hnCutoff hyCutoff hactive.1

/-! ## Guarded broad-pool and postcharge capacities -/

/-- A raw pool with `budget` units of surplus retains its requested minimum
after deleting a guard whose intersection with the row has that census. -/
theorem roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus
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
      label minimum := by
  have hinterSubset :
      roughCanonicalBroadCorrectionPool W n h K (yNat n) label ∩
          R.roughCanonicalGuardSet certificate deltaStar ⊆
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label := by
    intro a ha
    have haData := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr
      ⟨roughCanonicalBroadCorrectionPool_subset_rawRow
        W n h K (yNat n) label haData.1, haData.2⟩
  have hinter :
      (roughCanonicalBroadCorrectionPool W n h K (yNat n) label ∩
        R.roughCanonicalGuardSet certificate deltaStar).card <= budget :=
    (Finset.card_le_card hinterSubset).trans hcensus
  unfold RoughCanonicalGuardedBroadPoolCapacity
  rw [roughCanonicalGuardedBroadCorrectionPool, Finset.card_sdiff,
    Finset.inter_comm]
  omega

/-- The postcharge target never exceeds the uncorrected upper-row target. -/
theorem roughCanonicalPostchargeRowTarget_le_upperTarget
    {n h : Nat} (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) (label : Nat) :
    R.roughCanonicalPostchargeRowTarget deltaStar label <=
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) := by
  have hfixed : 0 <=
      (completeLabelMultiplicity (yNat n)
        (R.paperFixedExceptionalFactors deltaStar) label : Real) := by
    positivity
  have hbase : 0 <=
      (completeLabelMultiplicity (yNat n)
        R.prechargeBaseState label : Real) := by
    positivity
  unfold roughCanonicalPostchargeRowTarget
  linarith

/-- Any guarded broad-pool lower bound at least as large as the literal
upper-row target supplies capacity for the nonnegative postcharge quota. -/
theorem roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K label minimum : Nat)
    (hupper : roughUpperCompleteRoughRowTarget n h (yNat n) label <= minimum)
    (hpool : RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar
      W K label minimum) :
    RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label := by
  have htarget := R.roughCanonicalPostchargeRowTarget_le_upperTarget
    deltaStar label
  have hupperReal :
      (roughUpperCompleteRoughRowTarget n h (yNat n) label : Real) <=
        (minimum : Real) := by
    exact_mod_cast hupper
  have hpoolRow := Finset.card_le_card
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar W K label)
  have hminimumPool : minimum <=
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card := hpool
  unfold RoughCanonicalPostchargeRowCapacity
  exact htarget.trans <| hupperReal.trans <| by
    exact_mod_cast hminimumPool.trans hpoolRow

/-! ## The single remaining analytic raw-pool input -/

/-- Exact raw broad-pool surplus needed on the active labels occurring in
the guarded candidate set.  The maximum simultaneously pays for the desired
broad-pool minimum and the full upper-row target; `budget` pays for the local
finite guard census. -/
def RoughCanonicalActiveRawBroadSurplus
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K budget poolMinimum : Nat) : Prop :=
  ∀ label ∈ completeRoughLabelSet (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      max poolMinimum
          (roughUpperCompleteRoughRowTarget n h (yNat n) label) + budget <=
        (roughCanonicalBroadCorrectionPool W n h K (yNat n) label).card

/-- Once the raw de Bruijn--Saias surplus is supplied, all three guard-local
capacity clauses required by the guarded Section 9 continuation follow with
the literal budget `3`. -/
theorem roughCanonical_active_guard_capacity_inputs_of_rawBroadSurplus
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
          label) := by
  constructor
  · intro label _hlabelMem hactive
    exact R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  constructor
  · intro label hlabelMem hactive
    apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus certificate
      deltaStar W K label poolMinimum 3
    · exact R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
        deltaStar K label hnCutoff hyCutoff hactive
    · exact le_trans
        (Nat.add_le_add_right (Nat.le_max_left _ _) 3)
        (hsurplus label hlabelMem hactive)
  · intro label hlabelMem hactive
    let minimum := max poolMinimum
      (roughUpperCompleteRoughRowTarget n h (yNat n) label)
    have hcapacity : RoughCanonicalGuardedBroadPoolCapacity R certificate
        deltaStar W K label minimum := by
      apply R.roughCanonicalGuardedBroadPoolCapacity_of_raw_surplus certificate
        deltaStar W K label minimum 3
      · exact R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
          deltaStar K label hnCutoff hyCutoff hactive
      · exact hsurplus label hlabelMem hactive
    apply R.roughCanonicalPostchargeRowCapacity_of_guardedBroadPoolCapacity
      certificate deltaStar W K label minimum
    · exact Nat.le_max_right _ _
    · exact hcapacity

end BankPaperRealization

end

end Erdos390.WholePaper
