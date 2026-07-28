import Erdos390.WholePaper.TangentCommonMultiplierLists
import Erdos390.WholePaper.BankPaperPrecharge
import Erdos390.WholePaper.CentralAnchorGuardedCertificate
import Erdos390.WholePaper.CentralAnchorDivisorSupport

/-!
# The literal Section 9 numerical guards and bank-row census

This file instantiates the exhaustive numerical guard family used by the
tangent common lists.  In the notation of the paper it is exactly

`Γ_num = H' ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`.

Here `H'` is the actual guarded central-anchor set, `G_fix` is supplied by
the eventual rough selector, and the last three sets are the already
constructed precharge donor, base-state, and alternate-state sets.  The
global union is bounded directly from these definitions.  For a permitted
pair `u,v`, its lower-endpoint-relevant subfamily has at most two promoted
anchors and two bank states per component; fixed exceptional factors and
donors disappear because they lie strictly above `2n`.

The paper's bank-row census is also made literal.  The nontrivial bank rows
are the realized marker rows, while the fully dedicated set is empty.  Thus
the dedicated-row deletion in `TangentCommonMultiplierLists` is exactly
zero, without an assumed cardinality estimate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Actual bank rows and the exhaustive five-family guard set -/

/-- The rows touched by nontrivial precharged bank components.  Marker
injectivity makes this the literal component-row census. -/
def tangentPaperBankRows
    {n M : ℕ} (R : BankPaperRealization n M) : Finset ℕ :=
  R.allMarkers

/-- Section 9 does not reserve any complete rough row exclusively for the
bank: `D_row = ∅`. -/
def tangentPaperDedicatedRows
    {n M : ℕ} (_R : BankPaperRealization n M) : Finset ℕ :=
  ∅

/-- The paper's exhaustive numerical guard family
`H' ∪ G_fix ∪ E_donor ∪ G_bank^0 ∪ G_bank^1`. -/
def tangentPaperNumericalGuardSet
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ) : Finset ℕ :=
  certificate.anchors ∪ fixedExceptional ∪ R.prechargeDonorSet ∪
    R.prechargeBaseState ∪ R.prechargeAlternateState

theorem tangentPaperBankRows_card_eq_componentCount
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows.card =
      Fintype.card (BankPaperMarkerRequest n) := by
  rw [tangentPaperBankRows, R.allMarkers_card,
    card_bankPaperMarkerRequest]
  omega

theorem tangentPaperBankRows_card_le_anchorMarkerBudget
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperBankRows.card ≤ bankPaperAnchorMarkerBudget n := by
  rw [R.tangentPaperBankRows_card_eq_componentCount]
  exact R.prechargeComponentCount_le_anchorMarkerBudget

@[simp]
theorem tangentPaperDedicatedRows_card
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperDedicatedRows.card = 0 := by
  simp [tangentPaperDedicatedRows]

theorem tangentPaperDedicatedRows_subset_bankRows
    {n M : ℕ} (R : BankPaperRealization n M) :
    R.tangentPaperDedicatedRows ⊆ R.tangentPaperBankRows := by
  simp [tangentPaperDedicatedRows]

@[simp]
theorem tangentDedicatedRowMultipliers_tangentPaperDedicatedRows
    {n M y : ℕ} (R : BankPaperRealization n M)
    (multipliers : Finset ℕ) :
    tangentDedicatedRowMultipliers y R.tangentPaperDedicatedRows
      multipliers = ∅ := by
  simp [tangentDedicatedRowMultipliers, tangentPaperDedicatedRows]

/-- The global exhaustive union is finite with the cardinality supplied by
its five literal constituent families.  In particular, no cardinality of
`Γ_num` is postulated. -/
theorem tangentPaperNumericalGuardSet_card_le
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
      (residualCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        (largeCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        fixedExceptional.card +
        3 * Fintype.card (BankPaperMarkerRequest n) := by
  have hAnchorFixed := Finset.card_union_le
    certificate.anchors fixedExceptional
  have hDonor := Finset.card_union_le
    (certificate.anchors ∪ fixedExceptional) R.prechargeDonorSet
  have hBase := Finset.card_union_le
    (certificate.anchors ∪ fixedExceptional ∪ R.prechargeDonorSet)
    R.prechargeBaseState
  have hAlternate := Finset.card_union_le
    (certificate.anchors ∪ fixedExceptional ∪ R.prechargeDonorSet ∪
      R.prechargeBaseState) R.prechargeAlternateState
  have hUnion :
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
        certificate.anchors.card + fixedExceptional.card +
          R.prechargeDonorSet.card + R.prechargeBaseState.card +
            R.prechargeAlternateState.card := by
    unfold tangentPaperNumericalGuardSet
    omega
  calc
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
        certificate.anchors.card + fixedExceptional.card +
          R.prechargeDonorSet.card + R.prechargeBaseState.card +
            R.prechargeAlternateState.card := hUnion
    _ = (residualCentralPrimes n
            (centralAnchorCutoff depth n)).card +
          (largeCentralPrimes n
            (centralAnchorCutoff depth n)).card +
          fixedExceptional.card +
          3 * Fintype.card (BankPaperMarkerRequest n) := by
      rw [certificate.anchors_eq,
        fullCentralAnchors_card
          (two_le_centralAnchorCutoff hnCutoff)
          (two_mul_lt_centralAnchorCutoff_sq hnCutoff)
          certificate.isCofactorChoice,
        R.prechargeDonorSet_card, R.prechargeBaseState_card,
        R.prechargeAlternateState_card]
      omega

theorem tangentPaperNumericalGuardSet_card_le_anchorMarkerBudget
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n) :
    (R.tangentPaperNumericalGuardSet certificate fixedExceptional).card ≤
      (residualCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        (largeCentralPrimes n
          (centralAnchorCutoff depth n)).card +
        fixedExceptional.card + 3 * bankPaperAnchorMarkerBudget n := by
  have hglobal := R.tangentPaperNumericalGuardSet_card_le
    certificate fixedExceptional hnCutoff
  have hcomponent := R.prechargeComponentCount_le_anchorMarkerBudget
  omega

end BankPaperRealization

/-! ## Only promoted anchors can meet a permitted medium label -/

/-- A prime between the fixed cofactor prefix and the smooth cutoff cannot
divide any routed large-marker anchor. -/
theorem mediumPrime_not_dvd_guardedLargeCentralAnchor
    {c : ℝ} {depth n W y ℓ P : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hPrefix : 2 * depth + 1 ≤ W)
    (hWℓ : W < ℓ) (hℓy : ℓ ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (hℓPrime : ℓ.Prime)
    (hP : P ∈ largeCentralPrimes n
      (centralAnchorCutoff depth n)) :
    ¬ℓ ∣ largeCentralAnchor certificate.q P := by
  intro hdiv
  rw [largeCentralAnchor] at hdiv
  rcases hℓPrime.dvd_mul.mp hdiv with hℓP | hℓq
  · have hPPrime := largeCentralPrimes_prime hP
    have hEq : ℓ = P :=
      (Nat.prime_dvd_prime_iff_eq hℓPrime hPPrime).mp hℓP
    have hPLarge := largeCentralPrimes_gt hP
    omega
  · have hqPos : 0 < certificate.q P :=
      largeCentralCofactor_pos certificate.isCofactorChoice hP
    have hℓLeQ : ℓ ≤ certificate.q P := Nat.le_of_dvd hqPos hℓq
    have hqLe : certificate.q P ≤ 2 * depth + 1 :=
      largeCentralCofactor_le_fixedPrefix
        certificate.isCofactorChoice hP
    omega

/-- For one permitted pair, every central anchor divisible by `u` or `v`
is one of the two corresponding promoted factors.  The prefix, row-zero,
and other large-marker anchors are eliminated arithmetically. -/
theorem guardedCentralAnchors_pairPrimeDivisors_subset
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ⊆
      {promotedCentralFactor n u, promotedCentralFactor n v} := by
  intro g hg
  have hgAnchor := (Finset.mem_filter.mp hg).1
  have hgDiv := (Finset.mem_filter.mp hg).2
  rw [certificate.anchors_eq, fullCentralAnchors] at hgAnchor
  rcases Finset.mem_union.mp hgAnchor with hgPromoted | hgLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hgPromoted
    have hpPrime := residualCentralPrimes_prime hp
    rcases hgDiv with huDiv | hvDiv
    · rcases prime_dvd_promotedCentralFactor hpPrime huPrime huDiv with
        huTwo | hup
      · omega
      · subst p
        simp
    · rcases prime_dvd_promotedCentralFactor hpPrime hvPrime hvDiv with
        hvTwo | hvp
      · omega
      · subst p
        simp
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hgLarge
    exfalso
    rcases hgDiv with huDiv | hvDiv
    · exact mediumPrime_not_dvd_guardedLargeCentralAnchor
        certificate hPrefix (hWv.trans_le hvu) huy hyCutoff
          huPrime hP huDiv
    · exact mediumPrime_not_dvd_guardedLargeCentralAnchor
        certificate hPrefix hWv (hvu.trans huy) hyCutoff
          hvPrime hP hvDiv

theorem card_guardedCentralAnchors_pairPrimeDivisors_le_two
    {c : ℝ} {depth n W y u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hyCutoff : y < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g)).card ≤ 2 := by
  have hsubset := guardedCentralAnchors_pairPrimeDivisors_subset
    certificate hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hcard := Finset.card_le_card hsubset
  have hpair :
      ({promotedCentralFactor n u,
          promotedCentralFactor n v} : Finset ℕ).card ≤ 2 := by
    exact Finset.card_le_two
  omega

namespace BankPaperRealization

/-! ## A lossless endpoint-relevant overapproximation and its upper bound -/

/-- A lossless overapproximation of the part of `Γ_num` that could equal one
of the two endpoints in the broad interval.  It may retain guards whose
quotient lies outside the common-multiplier interval.  Under the tail
hypothesis used below, its upper cutoff removes the fixed exceptional and
donor families before counting guards. -/
def tangentPaperPairNumericalGuards
    {c : ℝ} {depth n M : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ) (K h u v : ℕ) : Finset ℕ :=
  (R.tangentPaperNumericalGuardSet certificate fixedExceptional).filter
    fun g ↦ g ≤ tangentBroadUpper n K h ∧ (u ∣ g ∨ v ∣ g)

theorem tangentPaperPairNumericalGuards_subset_anchor_states
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M) :
    R.tangentPaperPairNumericalGuards certificate fixedExceptional
        K h u v ⊆
      certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g) ∪
        R.prechargeBaseState ∪ R.prechargeAlternateState := by
  intro g hg
  have hgData := Finset.mem_filter.mp hg
  have hgGuard := hgData.1
  have hgUpper := hgData.2.1
  have hgDiv := hgData.2.2
  simp only [tangentPaperNumericalGuardSet, Finset.mem_union] at hgGuard
  rcases hgGuard with hgBeforeAlternate | hgAlternate
  · rcases hgBeforeAlternate with hgBeforeBase | hgBase
    · rcases hgBeforeBase with hgBeforeDonor | hgDonor
      · rcases hgBeforeDonor with hgAnchor | hgFixed
        · exact Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_union.mpr <| Or.inl <|
              Finset.mem_filter.mpr ⟨hgAnchor, hgDiv⟩
        · have htail := Finset.mem_Ioc.mp (hfixedTail hgFixed)
          have hbroad : tangentBroadUpper n K h ≤ 2 * n := by
            exact Nat.sub_le _ _
          omega
      · have htail := Finset.mem_Ioc.mp
          (R.prechargeDonorSet_subset_tail hgDonor)
        have hbroad : tangentBroadUpper n K h ≤ 2 * n := by
          exact Nat.sub_le _ _
        omega
    · exact Finset.mem_union.mpr <| Or.inl <|
        Finset.mem_union.mpr <| Or.inr hgBase
  · exact Finset.mem_union.mpr <| Or.inr hgAlternate

theorem tangentPaperPairNumericalGuards_card_le_componentCount
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤
        2 + 2 * Fintype.card (BankPaperMarkerRequest n) := by
  let anchorGuards :=
    certificate.anchors.filter (fun g ↦ u ∣ g ∨ v ∣ g)
  have hsubset := R.tangentPaperPairNumericalGuards_subset_anchor_states
    (K := K) (h := h) (u := u) (v := v)
      certificate fixedExceptional hfixedTail
  change R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v ⊆ anchorGuards ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState at hsubset
  have hAnchor : anchorGuards.card ≤ 2 := by
    simpa only [anchorGuards] using
      card_guardedCentralAnchors_pairPrimeDivisors_le_two
        certificate hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hAnchorBase := Finset.card_union_le
    anchorGuards R.prechargeBaseState
  have hAlternate := Finset.card_union_le
    (anchorGuards ∪ R.prechargeBaseState) R.prechargeAlternateState
  have htarget :
      (anchorGuards ∪ R.prechargeBaseState ∪
        R.prechargeAlternateState).card ≤
          anchorGuards.card + R.prechargeBaseState.card +
            R.prechargeAlternateState.card := by
    omega
  have hPairCard := Finset.card_le_card hsubset
  rw [R.prechargeBaseState_card, R.prechargeAlternateState_card] at htarget
  omega

theorem tangentPaperPairNumericalGuards_card_le_anchorMarkerBudget
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v).card ≤ 2 + 2 * bankPaperAnchorMarkerBudget n := by
  have hcount := R.tangentPaperPairNumericalGuards_card_le_componentCount
    (W := W) (K := K) (h := h) (u := u) (v := v)
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
        hyCutoff huPrime hvPrime
  have hcomponent := R.prechargeComponentCount_le_anchorMarkerBudget
  omega

/-! ## Filtering is lossless for actual endpoint deletion -/

theorem tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_left
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentLabelGuardDeletedMultipliers u
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentLabelGuardDeletedMultipliers u
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) := by
  ext a
  simp only [tangentLabelGuardDeletedMultipliers, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hguard⟩
    refine ⟨ha, ?_⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter]
    have hendpoints := tangentCommonMultiplierInterval_endpoints
      hu hv hvu ha
    exact ⟨hguard, (Finset.mem_Ioc.mp hendpoints.1).2,
      Or.inl (dvd_mul_right u a)⟩
  · rintro ⟨ha, hguard⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter] at hguard
    exact ⟨ha, hguard.1⟩

theorem tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_right
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentLabelGuardDeletedMultipliers v
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentLabelGuardDeletedMultipliers v
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) := by
  ext a
  simp only [tangentLabelGuardDeletedMultipliers, Finset.mem_filter]
  constructor
  · rintro ⟨ha, hguard⟩
    refine ⟨ha, ?_⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter]
    have hendpoints := tangentCommonMultiplierInterval_endpoints
      hu hv hvu ha
    exact ⟨hguard, (Finset.mem_Ioc.mp hendpoints.2).2,
      Or.inr (dvd_mul_right v a)⟩
  · rintro ⟨ha, hguard⟩
    rw [tangentPaperPairNumericalGuards, Finset.mem_filter] at hguard
    exact ⟨ha, hguard.1⟩

theorem tangentEndpointGuardDeletedMultipliers_numericalGuardSet_eq_pair
    {c : ℝ} {depth n M K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) :
    tangentEndpointGuardDeletedMultipliers u v
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
        (tangentCommonMultiplierInterval n K h u v) =
      tangentEndpointGuardDeletedMultipliers u v
        (R.tangentPaperPairNumericalGuards certificate fixedExceptional
          K h u v)
        (tangentCommonMultiplierInterval n K h u v) := by
  unfold tangentEndpointGuardDeletedMultipliers
  rw [R.tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_left
      certificate fixedExceptional hu hv hvu,
    R.tangentLabelGuardDeletedMultipliers_numericalGuardSet_eq_pair_right
      certificate fixedExceptional hu hv hvu]

/-- The actual five-family guard set deletes at most four multipliers plus
four per precharged bank component for a permitted pair. -/
theorem card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentEndpointGuardDeletedMultipliers u v
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      (tangentCommonMultiplierInterval n K h u v)).card ≤
        4 + 4 * Fintype.card (BankPaperMarkerRequest n) := by
  rw [R.tangentEndpointGuardDeletedMultipliers_numericalGuardSet_eq_pair
    certificate fixedExceptional huPrime.pos hvPrime.pos hvu]
  have hguard := card_tangentEndpointGuardDeletedMultipliers_le
    huPrime.pos hvPrime.pos
    (R.tangentPaperPairNumericalGuards certificate fixedExceptional
      K h u v)
    (tangentCommonMultiplierInterval n K h u v)
  have hpair := R.tangentPaperPairNumericalGuards_card_le_componentCount
    (W := W) (K := K) (h := h) (u := u) (v := v)
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
        hyCutoff huPrime hvPrime
  omega

theorem card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_budget
    {c : ℝ} {depth n M W K h u v : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentEndpointGuardDeletedMultipliers u v
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      (tangentCommonMultiplierInterval n K h u v)).card ≤
        4 + 4 * bankPaperAnchorMarkerBudget n := by
  have hguard :=
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le
      (W := W) (K := K) (h := h) (u := u) (v := v)
        certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
          hyCutoff huPrime hvPrime
  have hcomponent := R.prechargeComponentCount_le_anchorMarkerBudget
  omega

/-! ## The actual deterministic common-list ledger -/

/-- The Section 9 finite-deletion ledger after inserting the literal
`Γ_num` and `D_row`.  Only the head-residue and terminal-exceptional-row
cardinalities remain as analytic inputs. -/
theorem tangentPaperCommonMultiplier_finite_deletion_ledger
    {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (huPrime : u.Prime) (hvPrime : v.Prime) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate fixedExceptional)).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card +
      4 + 4 * bankPaperAnchorMarkerBudget n := by
  let interval := tangentCommonMultiplierInterval n K h u v
  let numericalGuards :=
    R.tangentPaperNumericalGuardSet certificate fixedExceptional
  let dedicatedRows := R.tangentPaperDedicatedRows
  let bad := tangentCommonMultiplierBadSet
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  let clean := tangentCleanCommonMultiplierList
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  have hpartition : clean.card + bad.card = interval.card := by
    dsimp only [clean, bad, interval]
    rw [tangentCleanCommonMultiplierList_eq_sdiff_badSet]
    exact Finset.card_sdiff_add_card_eq_card
      (tangentCommonMultiplierBadSet_subset_interval
        n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards)
  have hbad := card_tangentCommonMultiplierBadSet_le
    n K h Phead X0 (yNat n) u v dedicatedRows numericalGuards
  have hdedicated :
      (tangentDedicatedRowMultipliers (yNat n) dedicatedRows
        interval).card = 0 := by
    dsimp only [dedicatedRows, interval]
    simp
  have hguard :=
    R.card_tangentEndpointGuardDeletedMultipliers_numericalGuardSet_le_budget
      (W := W) (K := K) (h := h) (u := u) (v := v)
        certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
          hyCutoff huPrime hvPrime
  dsimp only [interval, numericalGuards, dedicatedRows, bad, clean] at hpartition hbad hdedicated hguard ⊢
  omega

end BankPaperRealization

end

end Erdos390.WholePaper
