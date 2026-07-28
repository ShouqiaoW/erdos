import Erdos390.WholePaper.TangentExceptionalSelbergReduction

/-!
# Cardinality bridge for the tangent clean common list

This file performs the final finite-cardinality assembly around the tangent
common list.  The head-coprime candidates are the literal reduced residues in
the common-multiplier interval.  Their complement is exactly the already
defined head-bad set, so the head-bad term cancels from the finite-deletion
ledger.

The resulting theorems turn a supplied lower bound for those interval
candidates, supplied upper bounds for the exceptional and remaining deletion
losses, and one explicit natural-number comparison into

`lowerCard ≤ cleanList.card`.

This is the bridge which discharges the `hlower` input of the later
collision-counting terminal when supplied the paper's analytic estimates.
It does not prove any reduced-residue density estimate, exceptional-row
estimate, or final numerical comparison.  Those inputs remain visible in the
statements below.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal head-coprime interval candidates -/

/-- Multipliers in the common interval which survive the fixed head-coprimality
test.  This is just a named presentation of the relevant reduced-residue
interval. -/
def tangentHeadCoprimeCandidates
    (n K h Phead u v : ℕ) : Finset ℕ :=
  (tangentCommonMultiplierInterval n K h u v).filter fun a ↦
    Nat.Coprime a Phead

/-- The head-coprime candidates are literally the fixed-modulus
reduced-residue count on `(n / v, (2n-Kh) / u]`. -/
theorem tangentHeadCoprimeCandidates_eq_reducedResidueIoc
    (n K h Phead u v : ℕ) :
    tangentHeadCoprimeCandidates n K h Phead u v =
      reducedResidueIoc Phead (n / v) (tangentBroadUpper n K h / u) := by
  rfl

/-- The head-coprime candidates and the head-bad multipliers partition the
literal common interval. -/
theorem card_tangentHeadCoprimeCandidates_add_headBad
    (n K h Phead u v : ℕ) :
    (tangentHeadCoprimeCandidates n K h Phead u v).card +
        (tangentHeadBadMultipliers Phead
          (tangentCommonMultiplierInterval n K h u v)).card =
      (tangentCommonMultiplierInterval n K h u v).card := by
  simpa only [tangentHeadCoprimeCandidates,
    tangentHeadBadMultipliers] using
    (Finset.card_filter_add_card_filter_not
      (s := tangentCommonMultiplierInterval n K h u v)
      (fun a : ℕ ↦ Nat.Coprime a Phead))

/-! ## Generic finite-deletion assembly -/

/-- A lower bound for the head-coprime interval candidates survives all common
list deletions once the exceptional and deterministic losses fit inside the
declared arithmetic budget.

The theorem deliberately does not manufacture any of its three quantitative
inputs: `hcandidate` is the interval candidate estimate, `hexceptional` is the
exceptional-row estimate, and `hdeletion` bounds the dedicated-row and
two-endpoint guard losses. -/
theorem tangentCleanCommonMultiplierList_card_lower_of_headCandidate
    {n K h Phead X0 y u v : ℕ}
    (dedicatedRows numericalGuards : Finset ℕ)
    {candidateLower exceptionalUpper deletionUpper lowerCard : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (hcandidate :
      candidateLower ≤
        (tangentHeadCoprimeCandidates n K h Phead u v).card)
    (hexceptional :
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card ≤
          exceptionalUpper)
    (hdeletion :
      (tangentDedicatedRowMultipliers y dedicatedRows
          (tangentCommonMultiplierInterval n K h u v)).card +
        2 * numericalGuards.card ≤ deletionUpper)
    (harithmetic :
      lowerCard + exceptionalUpper + deletionUpper ≤ candidateLower) :
    lowerCard ≤
      (tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards).card := by
  have hledger := tangentCommonMultiplier_finite_deletion_ledger
    (n := n) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (y := y) (u := u) (v := v) hu hv dedicatedRows numericalGuards
  have hpartition := card_tangentHeadCoprimeCandidates_add_headBad
    n K h Phead u v
  omega

/-! ## Actual-paper sharp specializations -/

/-- Paper-bank specialization of the cardinality bridge.  The dedicated-row
loss has already vanished in the sharp ledger and the numerical-guard loss is
the audited `4 + 4 * bankPaperSharpMarkerBudget n`.  Among deletion counts,
only an explicit exceptional upper bound remains; the candidate lower bound
and the final natural-number comparison are also explicit premises. -/
theorem BankPaperRealization.tangentPaperCleanCommonMultiplierList_card_lower_of_headCandidate
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
    (huPrime : u.Prime) (hvPrime : v.Prime)
    {candidateLower exceptionalUpper lowerCard : ℕ}
    (hcandidate :
      candidateLower ≤
        (tangentHeadCoprimeCandidates n K h Phead u v).card)
    (hexceptional :
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card ≤
          exceptionalUpper)
    (harithmetic :
      lowerCard + exceptionalUpper + 4 +
          4 * bankPaperSharpMarkerBudget n ≤ candidateLower) :
    lowerCard ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet
          certificate fixedExceptional)).card := by
  have hledger :=
    R.tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
      (W := W) (K := K) (h := h) (Phead := Phead) (X0 := X0)
        (u := u) (v := v) certificate fixedExceptional hfixedTail hTwoW
          hPrefix hWv hvu huy hyCutoff huPrime hvPrime
  have hpartition := card_tangentHeadCoprimeCandidates_add_headBad
    n K h Phead u v
  omega

/-- The same paper-bank bridge with the exceptional upper bound instantiated
by the verified abstract Selberg natural majorant.  An admissible upper-Moebius
coefficient function is supplied through `hmuPlus`; the adequacy of its
resulting majorant, the candidate lower bound, and the final arithmetic remain
the explicit inputs `harithmetic` and `hcandidate`.  This theorem does not
claim their construction. -/
theorem BankPaperRealization.tangentPaperCleanCommonMultiplierList_card_lower_of_abstractSelberg
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
    (huPrime : u.Prime) (hvPrime : v.Prime)
    (muPlus : ℕ → ℝ)
    (hmuPlus : BoundingSieve.IsUpperMoebius muPlus)
    {candidateLower lowerCard : ℕ}
    (hcandidate :
      candidateLower ≤
        (tangentHeadCoprimeCandidates n K h Phead u v).card)
    (harithmetic :
      lowerCard +
          tangentExceptionalAbstractSelbergNatMajorant
            n K h X0 (yNat n) u v muPlus +
          4 + 4 * bankPaperSharpMarkerBudget n ≤ candidateLower) :
    lowerCard ≤
      (tangentCleanCommonMultiplierList n K h Phead X0 (yNat n) u v
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet
          certificate fixedExceptional)).card := by
  have hledger :=
    R.tangentPaperCommonMultiplier_abstractSelberg_sharp_ledger
      (W := W) (K := K) (h := h) (Phead := Phead) (X0 := X0)
        (u := u) (v := v) certificate fixedExceptional hfixedTail hTwoW
          hPrefix hWv hvu huy hyCutoff huPrime hvPrime muPlus hmuPlus
  have hpartition := card_tangentHeadCoprimeCandidates_add_headBad
    n K h Phead u v
  omega

end

end Erdos390.WholePaper
