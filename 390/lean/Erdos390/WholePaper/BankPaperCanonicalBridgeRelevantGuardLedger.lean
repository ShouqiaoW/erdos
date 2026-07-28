import Erdos390.Full.PaperGuardedStructuredSample
import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction
import Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction

/-!
# The bridge-relevant numerical-guard ledger

The literal rough construction uses the global five-family guard

`anchors ∪ fixedExceptional ∪ donors ∪ baseState ∪ alternateState`.

That global set is not the guard census used by the smooth bridge.  Fixed
exceptional factors and donors lie above `2n`, while the two bank endpoint
states have a prime complete-rough label above `yNat n`.  Hence, on the
positive `yNat n`-smooth values at most `2n` which occur in every bridge
cell, the global guard agrees exactly with the promoted residual anchors
whose base prime is at most `yNat n`.

This file makes that relevant guard literal.  Its cardinality is at most
`yNat n`, so it fits in the promoted part of `GuardSlot`.  We adjoin the
harmless sentinel value `0` before enumerating it.  This avoids a false
nonemptiness requirement on an image of a nonempty slot type; the sentinel
cannot occur in a structured cell.  Two promoted slots per smooth integer
therefore suffice uniformly, and no bank slot is required.

Thus the correct replacement for a global
`ledger.guards = roughCanonicalGuardSet` hypothesis is the eventual local
predicate `BankPaperCanonicalBridgeGuardAgreement`.  A total fixed ledger
family, chosen before any realization or certificate, uses a harmless
zero-valued fallback on the finite prefix where the relevant guard does not
fit.  Once a realization exists the paper census forces the canonical branch,
so this fixed family agrees with the global rough guard on the bridge
universe.  The concrete elimination interfaces below give equality after
deleting guards from a raw cell, equality after restricting deletion to
structured active values, and pointwise avoidance of the full guard.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

/-! ## Enumerating an arbitrary finite guard together with a zero sentinel -/

/-- An embedding of a finite guard-with-sentinel into a large enough guard
slot type. -/
noncomputable def guardFinsetWithZeroEmbedding
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    (insert 0 guards : Finset Nat) ↪ GuardSlot n Cprom Cbank :=
  Classical.choice <| Function.Embedding.nonempty_of_card_le <| by
    simpa only [Fintype.card_coe] using hcard

/-- Enumerate a finite guard in a concrete `Ledger`, padding every unused
slot by the sentinel value zero. -/
noncomputable def ledgerOfFinsetWithZero
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    Ledger n Cprom Cbank where
  value :=
    Function.extend
      (guardFinsetWithZeroEmbedding guards hcard)
      (fun a : (insert 0 guards : Finset Nat) => a.1)
      (fun _ => 0)

/-- The padded enumeration has exactly the requested guard together with
the sentinel; no other integer is introduced. -/
theorem ledgerOfFinsetWithZero_guards
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    (ledgerOfFinsetWithZero guards hcard).guards = insert 0 guards := by
  classical
  let e : (insert 0 guards : Finset Nat) ↪
      GuardSlot n Cprom Cbank :=
    guardFinsetWithZeroEmbedding guards hcard
  change Finset.univ.image
      (Function.extend e
        (fun a : (insert 0 guards : Finset Nat) => a.1)
        (fun _ => 0)) =
    insert 0 guards
  ext a
  constructor
  · intro ha
    rw [Finset.mem_image] at ha
    obtain ⟨slot, _hslot, rfl⟩ := ha
    by_cases hslot : ∃ x, e x = slot
    · rw [Function.extend_def, dif_pos hslot]
      exact (Classical.choose hslot).property
    · rw [Function.extend_apply'
        (g := fun x : (insert 0 guards : Finset Nat) => x.1)
        (e' := fun _ : GuardSlot n Cprom Cbank => 0)
        slot hslot]
      exact Finset.mem_insert_self 0 guards
  · intro ha
    rw [Finset.mem_image]
    refine ⟨e ⟨a, ha⟩, Finset.mem_univ _, ?_⟩
    simpa only using
      e.injective.extend_apply
        (fun x : (insert 0 guards : Finset Nat) => x.1)
        (fun _ : GuardSlot n Cprom Cbank => 0)
        ⟨a, ha⟩

/-! ## The literal bridge-relevant subfamily -/

/-- The only numerical guards visible on positive `yNat n`-smooth values
at most `2n`: promoted residual anchors whose base prime is at most the
smooth cutoff. -/
def roughCanonicalBridgeRelevantGuardSet
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (_certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) : Finset Nat :=
  bankPaperCanonicalSmoothResidualAnchorPool n
    (centralAnchorCutoff depth n) (yNat n)

/-- The relevant guard has the paper-sized pointwise census. -/
theorem roughCanonicalBridgeRelevantGuardSet_card_le
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (roughCanonicalBridgeRelevantGuardSet certificate).card <= yNat n := by
  exact bankPaperCanonicalSmoothResidualAnchorPool_card_le
    n (centralAnchorCutoff depth n) (yNat n)

/-- Every relevant promoted anchor belongs to the certificate's full anchor
set. -/
theorem roughCanonicalBridgeRelevantGuardSet_subset_anchors
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    roughCanonicalBridgeRelevantGuardSet certificate ⊆
      certificate.anchors := by
  intro a ha
  rw [roughCanonicalBridgeRelevantGuardSet,
    bankPaperCanonicalSmoothResidualAnchorPool,
    Finset.mem_image] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  rw [certificate.anchors_eq, fullCentralAnchors]
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr
    ⟨p, (Finset.mem_filter.mp hp).1, rfl⟩

/-- A smooth guarded central anchor is necessarily one of the relevant
promoted residual anchors.  Large routed anchors retain their marker prime
above the smooth cutoff. -/
theorem guardedCentralAnchor_mem_bridgeRelevant_of_smooth
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    {a : Nat} (ha : a ∈ certificate.anchors) (haPos : 0 < a)
    (haSmooth : a ∈ Nat.smoothNumbers (yNat n + 1)) :
    a ∈ roughCanonicalBridgeRelevantGuardSet certificate := by
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mpr haSmooth
  rw [certificate.anchors_eq, fullCentralAnchors] at ha
  rcases Finset.mem_union.mp ha with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    rw [roughCanonicalBridgeRelevantGuardSet,
      bankPaperCanonicalSmoothResidualAnchorPool]
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hpHigh : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p
          (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel :
        p ∣ completeRoughLabel (yNat n)
          (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hpHigh
        haPos.ne' hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPDvdLabel :
        P ∣ completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        haPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim

/-- A realization- and certificate-independent ledger family for the bridge.
When the relevant guard fits in the literal two-promoted-slot census it is
enumerated exactly.  The zero-valued fallback makes the family total on the
irrelevant finite prefix. -/
noncomputable def roughCanonicalBridgeRelevantLedgerFamily
    (depth n : Nat) : Ledger n 2 0 :=
  let guards :=
    bankPaperCanonicalSmoothResidualAnchorPool n
      (centralAnchorCutoff depth n) (yNat n)
  if hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n 2 0) then
    ledgerOfFinsetWithZero guards hcard
  else
    ⟨fun _ => 0⟩

namespace BankPaperRealization

/-- On every positive smooth integer at most `2n`, membership in the
bridge-relevant guard is equivalent to membership in the global five-family
rough guard. -/
theorem mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    {a : Nat} (haPos : 0 < a) (haUpper : a <= 2 * n)
    (haSmooth : a ∈ Nat.smoothNumbers (yNat n + 1)) :
    a ∈ roughCanonicalBridgeRelevantGuardSet certificate ↔
      a ∈ R.roughCanonicalGuardSet certificate deltaStar := by
  classical
  constructor
  · intro ha
    have haAnchor :=
      roughCanonicalBridgeRelevantGuardSet_subset_anchors certificate ha
    simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
      Finset.mem_union]
    exact Or.inl <| Or.inl <| Or.inl <| Or.inl haAnchor
  · intro haGuard
    have haLabel : completeRoughLabel (yNat n) a = 1 :=
      (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mpr haSmooth
    simp only [roughCanonicalGuardSet, tangentPaperNumericalGuardSet,
      Finset.mem_union] at haGuard
    rcases haGuard with
      (((haAnchor | haFixed) | haDonor) | haBase) | haAlternate
    · exact guardedCentralAnchor_mem_bridgeRelevant_of_smooth
        certificate hyCutoff haAnchor haPos haSmooth
    · have haTail :=
        R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
      exact (Nat.not_lt_of_ge haUpper (Finset.mem_Ioc.mp haTail).1).elim
    · have haTail := R.prechargeDonorSet_subset_tail haDonor
      exact (Nat.not_lt_of_ge haUpper (Finset.mem_Ioc.mp haTail).1).elim
    · rw [prechargeBaseState, indexedPathState, Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at haLabel
      have hmarker := R.yNat_lt_paperMarker request
      have hySix := R.six_le_yNat
      omega
    · rw [prechargeAlternateState, indexedPathState,
        Finset.mem_image] at haAlternate
      obtain ⟨request, _hrequest, rfl⟩ := haAlternate
      rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at haLabel
      have hmarker := R.yNat_lt_paperMarker request
      have hySix := R.six_le_yNat
      omega

/-! ## The canonical two-promoted-slot ledger -/

/-- After adjoining the zero sentinel, the relevant guard fits in the
literal two-promoted-slot census. -/
theorem roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (insert 0
        (roughCanonicalBridgeRelevantGuardSet certificate)).card <=
      Fintype.card (GuardSlot n 2 0) := by
  have hrelevant :=
    roughCanonicalBridgeRelevantGuardSet_card_le certificate
  have hyOne : 1 <= yNat n := by
    have hySix := R.six_le_yNat
    omega
  rw [card_guardSlot]
  calc
    (insert 0
        (roughCanonicalBridgeRelevantGuardSet certificate)).card <=
        (roughCanonicalBridgeRelevantGuardSet certificate).card + 1 :=
      Finset.card_insert_le _ _
    _ <= yNat n + 1 := Nat.add_le_add_right hrelevant 1
    _ <= 2 * yNat n + 0 * yNat n * scaleSlots n * 3 := by omega

/-- The canonical bridge ledger.  It enumerates the relevant guard plus the
zero sentinel in `GuardSlot n 2 0`. -/
noncomputable def roughCanonicalBridgeRelevantLedger
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    Ledger n 2 0 :=
  ledgerOfFinsetWithZero
    (roughCanonicalBridgeRelevantGuardSet certificate)
    (R.roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
      certificate)

/-- Whenever a realization exists, its pointwise canonical relevant ledger is
the fixed family chosen before the realization and certificate.  The
realization supplies only the proof that the canonical branch of the total
family is active. -/
theorem roughCanonicalBridgeRelevantLedgerFamily_eq
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    roughCanonicalBridgeRelevantLedgerFamily depth n =
      R.roughCanonicalBridgeRelevantLedger certificate := by
  have hcard :
      (insert 0
        (bankPaperCanonicalSmoothResidualAnchorPool n
          (centralAnchorCutoff depth n) (yNat n))).card <=
        Fintype.card (GuardSlot n 2 0) := by
    simpa only [roughCanonicalBridgeRelevantGuardSet] using
      R.roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
        certificate
  unfold roughCanonicalBridgeRelevantLedgerFamily
  rw [dif_pos hcard]
  unfold roughCanonicalBridgeRelevantLedger
    roughCanonicalBridgeRelevantGuardSet
  rfl

/-- Exact image of the canonical relevant ledger. -/
theorem roughCanonicalBridgeRelevantLedger_guards
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    (R.roughCanonicalBridgeRelevantLedger certificate).guards =
      insert 0 (roughCanonicalBridgeRelevantGuardSet certificate) := by
  unfold roughCanonicalBridgeRelevantLedger
  apply ledgerOfFinsetWithZero_guards

/-- The exact local interface needed by the bridge: its ledger and the
global rough guard agree on all possible structured values. -/
def BankPaperCanonicalBridgeGuardAgreement
    {c : Real} {depth n h Cprom Cbank : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (G : Ledger n Cprom Cbank)
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) : Prop :=
  forall a : Nat, 0 < a -> a <= 2 * n ->
    a ∈ Nat.smoothNumbers (yNat n + 1) ->
      (a ∈ G.guards ↔
        a ∈ R.roughCanonicalGuardSet certificate deltaStar)

/-- The canonical relevant ledger satisfies the local agreement interface. -/
theorem roughCanonicalBridgeRelevantLedger_agreement
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (R.roughCanonicalBridgeRelevantLedger certificate)
      R certificate deltaStar := by
  intro a haPos haUpper haSmooth
  rw [R.roughCanonicalBridgeRelevantLedger_guards certificate,
    Finset.mem_insert]
  have haZero : a ≠ 0 := haPos.ne'
  simp only [haZero, false_or]
  exact R.mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
    certificate deltaStar hyCutoff haPos haUpper haSmooth

/-- Finite local agreement for the fixed ledger family. -/
theorem roughCanonicalBridgeRelevantLedgerFamily_agreement
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (roughCanonicalBridgeRelevantLedgerFamily depth n)
      R certificate deltaStar := by
  rw [R.roughCanonicalBridgeRelevantLedgerFamily_eq certificate]
  exact R.roughCanonicalBridgeRelevantLedger_agreement
    certificate deltaStar hyCutoff

/-- Pointwise eventual form: at every sufficiently large index, each canonical
relevant ledger agrees with the global guard exactly on the positive smooth
bridge universe. -/
theorem eventually_roughCanonicalBridgeRelevantLedger_agreement
    {c : Real} (depth : Nat) (deltaStar : Real) :
    ∀ᶠ n : Nat in atTop,
      forall
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        BankPaperCanonicalBridgeGuardAgreement
          (R.roughCanonicalBridgeRelevantLedger certificate)
          R certificate deltaStar := by
  filter_upwards [eventually_yNat_lt_centralAnchorCutoff depth] with
    n hyCutoff
  intro R certificate
  exact R.roughCanonicalBridgeRelevantLedger_agreement
    certificate deltaStar hyCutoff

/-- Eventual agreement with the ledger family fixed before quantifying over
the realization and certificate.  This is the quantifier order consumed by
the canonical structured-sample and one-shot bridge interfaces. -/
theorem eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
    {c : Real} (depth : Nat) (deltaStar : Real) :
    ∀ᶠ n : Nat in atTop,
      forall
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        BankPaperCanonicalBridgeGuardAgreement
          (roughCanonicalBridgeRelevantLedgerFamily depth n)
          R certificate deltaStar := by
  filter_upwards [eventually_yNat_lt_centralAnchorCutoff depth] with
    n hyCutoff
  intro R certificate
  exact R.roughCanonicalBridgeRelevantLedgerFamily_agreement
    certificate deltaStar hyCutoff

/-! ## Equality on raw cells and structured active values -/

/-- A raw cell with physical upper endpoint at most `2` consists of values
at most `2n`. -/
theorem rawCell_value_le_two_mul
    {Head : Type*} [Fintype Head]
    (P : Head -> HeadPattern.Pattern) (I : PhysicalIntervals)
    {n : Nat} (hupperTwo : forall sigma, I.upper sigma <= 2)
    {cell : Cell Head} {a : Nat} (ha : a ∈ rawCell P I n cell) :
    a <= 2 * n := by
  have haStructured :
      a ∈ structuredCell (P cell.1)
        (physicalBound (I.lower cell.2) n)
        (physicalBound (I.upper cell.2) n) (yNat n) := by
    simpa only [rawCell] using ha
  have haUpper :
      a <= physicalBound (I.upper cell.2) n :=
    (mem_smoothInterval.mp
      (mem_structuredCell.mp haStructured).1).2.1
  have hupperPos : 0 < I.upper cell.2 :=
    (I.lower_pos cell.2).trans (I.lower_lt_upper cell.2)
  have hfloor :
      (physicalBound (I.upper cell.2) n : Real) <=
        I.upper cell.2 * (n : Real) := by
    unfold physicalBound
    exact Nat.floor_le
      (mul_nonneg hupperPos.le (by positivity))
  have htwo :
      I.upper cell.2 * (n : Real) <= 2 * (n : Real) :=
    mul_le_mul_of_nonneg_right (hupperTwo cell.2) (by positivity)
  have hbound : physicalBound (I.upper cell.2) n <= 2 * n := by
    have hcast := hfloor.trans htwo
    exact_mod_cast hcast
  exact haUpper.trans hbound

/-- Deleting the canonical relevant ledger or deleting the full global
rough guard gives exactly the same raw bridge cell. -/
theorem rawCell_sdiff_roughCanonicalBridgeRelevantLedger_eq_fullGuard
    {Head : Type*} [Fintype Head]
    (P : Head -> HeadPattern.Pattern) (I : PhysicalIntervals)
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (cell : Cell Head) :
    rawCell P I n cell \
        (R.roughCanonicalBridgeRelevantLedger certificate).guards =
      rawCell P I n cell \
        R.roughCanonicalGuardSet certificate deltaStar := by
  ext a
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨haRaw, haNotRelevant⟩
    refine ⟨haRaw, ?_⟩
    intro haFull
    have haStructured :
        a ∈ structuredCell (P cell.1)
          (physicalBound (I.lower cell.2) n)
          (physicalBound (I.upper cell.2) n) (yNat n) := by
      simpa only [rawCell] using haRaw
    have haSmoothData :=
      mem_smoothInterval.mp (mem_structuredCell.mp haStructured).1
    have haPos := pos_of_mem_smoothInterval
      (mem_structuredCell.mp haStructured).1
    have haUpper := rawCell_value_le_two_mul P I hupperTwo haRaw
    exact haNotRelevant <|
      ((R.roughCanonicalBridgeRelevantLedger_agreement certificate
        deltaStar hyCutoff) a haPos haUpper haSmoothData.2.2).mpr haFull
  · rintro ⟨haRaw, haNotFull⟩
    refine ⟨haRaw, ?_⟩
    intro haRelevant
    have haStructured :
        a ∈ structuredCell (P cell.1)
          (physicalBound (I.lower cell.2) n)
          (physicalBound (I.upper cell.2) n) (yNat n) := by
      simpa only [rawCell] using haRaw
    have haSmoothData :=
      mem_smoothInterval.mp (mem_structuredCell.mp haStructured).1
    have haPos := pos_of_mem_smoothInterval
      (mem_structuredCell.mp haStructured).1
    have haUpper := rawCell_value_le_two_mul P I hupperTwo haRaw
    exact haNotFull <|
      ((R.roughCanonicalBridgeRelevantLedger_agreement certificate
        deltaStar hyCutoff) a haPos haUpper haSmoothData.2.2).mp
          haRelevant

/-- Pointwise structured-sample form of the same local agreement. -/
theorem structuredSample_value_mem_relevantLedger_iff_fullGuard
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    {c : Real} {depth h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization D.n (upperEndpoint D.n h))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat D.n < centralAnchorCutoff depth D.n)
    (hupper : forall m : D.Sample, D.value m <= 2 * D.n)
    (m : D.Sample) :
    D.value m ∈
        (R.roughCanonicalBridgeRelevantLedger certificate).guards ↔
      D.value m ∈ R.roughCanonicalGuardSet certificate deltaStar := by
  exact
    (R.roughCanonicalBridgeRelevantLedger_agreement certificate
      deltaStar hyCutoff)
      (D.value m) (D.value_pos m) (hupper m)
        (D.value_mem_smoothNumbers m)

/-- Deleting the relevant ledger and deleting the full rough guard agree
exactly after restriction to the finite image of a structured sample whose
values lie below `2n`. -/
theorem structuredActiveValues_sdiff_relevantLedger_eq_fullGuard
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    {c : Real} {depth h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization D.n (upperEndpoint D.n h))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat D.n < centralAnchorCutoff depth D.n)
    (hupper : forall m : D.Sample, D.value m <= 2 * D.n) :
    bankPaperCanonicalStructuredActiveValues D \
        (R.roughCanonicalBridgeRelevantLedger certificate).guards =
      bankPaperCanonicalStructuredActiveValues D \
        R.roughCanonicalGuardSet certificate deltaStar := by
  ext a
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨haActive, haNotRelevant⟩
    refine ⟨haActive, ?_⟩
    obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp haActive
    intro haFull
    exact haNotRelevant <|
      (structuredSample_value_mem_relevantLedger_iff_fullGuard
        D R certificate deltaStar hyCutoff hupper m).mpr haFull
  · rintro ⟨haActive, haNotFull⟩
    refine ⟨haActive, ?_⟩
    obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp haActive
    intro haRelevant
    exact haNotFull <|
      (structuredSample_value_mem_relevantLedger_iff_fullGuard
        D R certificate deltaStar hyCutoff hupper m).mp haRelevant

/-- Any locally agreeing ledger turns the structured sample's built-in guard
avoidance into avoidance of the full global rough guard.  This is the generic
`hnotGuard` migration interface; it does not require a global equality of
finite guard sets. -/
theorem structuredSample_value_not_fullGuard_of_agreement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    {c : Real} {depth h Cprom Cbank : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (G : Ledger D.n Cprom Cbank)
    (R : BankPaperRealization D.n (upperEndpoint D.n h))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      left right changed)
    (deltaStar : Real)
    (hagreement : BankPaperCanonicalBridgeGuardAgreement
      G R certificate deltaStar)
    (hupper : forall m : D.Sample, D.value m <= 2 * D.n)
    (hguards : D.guards = G.guards)
    (m : D.Sample) :
    D.value m ∉ R.roughCanonicalGuardSet certificate deltaStar := by
  intro haFull
  apply D.value_not_guard m
  rw [hguards]
  exact
    (hagreement (D.value m) (D.value_pos m) (hupper m)
      (D.value_mem_smoothNumbers m)).mpr haFull

/-- If a structured sample deletes the canonical relevant ledger, then each
of its values also avoids the full global rough guard. -/
theorem structuredSample_value_not_fullGuard_of_relevantLedger
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head)
    {c : Real} {depth h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization D.n (upperEndpoint D.n h))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat D.n < centralAnchorCutoff depth D.n)
    (hupper : forall m : D.Sample, D.value m <= 2 * D.n)
    (hguards : D.guards =
      (R.roughCanonicalBridgeRelevantLedger certificate).guards)
    (m : D.Sample) :
    D.value m ∉ R.roughCanonicalGuardSet certificate deltaStar := by
  exact structuredSample_value_not_fullGuard_of_agreement
    D (R.roughCanonicalBridgeRelevantLedger certificate)
      R certificate deltaStar
      (R.roughCanonicalBridgeRelevantLedger_agreement
        certificate deltaStar hyCutoff)
      hupper hguards m

end BankPaperRealization

end

end Erdos390.WholePaper
