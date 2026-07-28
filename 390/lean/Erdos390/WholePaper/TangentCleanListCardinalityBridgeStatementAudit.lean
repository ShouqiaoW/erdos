import Erdos390.WholePaper.TangentCleanListCardinalityBridge

/-!
# Expanded statement audit for the tangent clean-list cardinality bridge

These examples make the analytic boundary explicit.  In particular, the
bridge consumes a candidate lower bound, an exceptional upper bound (or the
abstract Selberg majorant), and final arithmetic; it proves none of those
estimates itself.
-/

namespace Erdos390.WholePaper.TangentCleanListCardinalityBridgeStatementAudit

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Definition audit -/

example (n K h Phead u v : ℕ) :
    tangentHeadCoprimeCandidates n K h Phead u v =
      (tangentCommonMultiplierInterval n K h u v).filter fun a ↦
        Nat.Coprime a Phead :=
  rfl

/-! ## Theorem audit -/

example (n K h Phead u v : ℕ) :
    tangentHeadCoprimeCandidates n K h Phead u v =
      reducedResidueIoc Phead (n / v)
        (tangentBroadUpper n K h / u) :=
  tangentHeadCoprimeCandidates_eq_reducedResidueIoc n K h Phead u v

example (n K h Phead u v : ℕ) :
    (tangentHeadCoprimeCandidates n K h Phead u v).card +
        (tangentHeadBadMultipliers Phead
          (tangentCommonMultiplierInterval n K h u v)).card =
      (tangentCommonMultiplierInterval n K h u v).card :=
  card_tangentHeadCoprimeCandidates_add_headBad n K h Phead u v

example {n K h Phead X0 y u v : ℕ}
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
        n K h Phead X0 y u v dedicatedRows numericalGuards).card :=
  tangentCleanCommonMultiplierList_card_lower_of_headCandidate
    (n := n) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (y := y) (u := u) (v := v) dedicatedRows numericalGuards hu hv
        hcandidate hexceptional hdeletion harithmetic

example {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
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
          certificate fixedExceptional)).card :=
  R.tangentPaperCleanCommonMultiplierList_card_lower_of_headCandidate
    (W := W) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (u := u) (v := v) certificate fixedExceptional hfixedTail hTwoW
        hPrefix hWv hvu huy hyCutoff huPrime hvPrime hcandidate hexceptional
          harithmetic

example {c : ℝ} {depth n M W K h Phead X0 u v : ℕ}
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
          certificate fixedExceptional)).card :=
  R.tangentPaperCleanCommonMultiplierList_card_lower_of_abstractSelberg
    (W := W) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (u := u) (v := v) certificate fixedExceptional hfixedTail hTwoW
        hPrefix hWv hvu huy hyCutoff huPrime hvPrime muPlus hmuPlus
          hcandidate harithmetic

end

end Erdos390.WholePaper.TangentCleanListCardinalityBridgeStatementAudit
