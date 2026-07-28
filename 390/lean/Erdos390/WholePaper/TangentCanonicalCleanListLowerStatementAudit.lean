import Erdos390.WholePaper.TangentCanonicalCleanListLower

/-!
# Expanded statement audit for the canonical tangent clean-list lower bound

The examples expose the three quantitative layers without abbreviating the
critical scales:

* candidates live in `(n/v, tangentBroadUpper/u]` and lose the literal
  modulus `roughHeadModulus W`;
* the accumulated exceptional remainder contains `(X0/u)*y^4/log(y)^2`;
* the effective lower card is the ceiling of `density*n/v`, so its scale
  inequality is proved rather than assumed.

The generic bridge retains the displayed deterministic-deletion bound and
the final comparison saying that the candidate floor absorbs the effective
lower-card ceiling, canonical exceptional ceiling, and deletion budget.  In
the sharp paper wrapper the deletion census is discharged internally, so its
only cardinality premise is that final comparison.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper.TangentCanonicalCleanListLowerStatementAudit

open Erdos390.Full.ArithmeticModel

noncomputable section

example {W n K h u v : ℕ}
    (hinterval : n / v ≤ tangentBroadUpper n K h / u) :
    ⌊max 0
      (roughHeadDensity W *
          (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) -
        roughHeadModulus W)⌋₊ ≤
      (tangentHeadCoprimeCandidates
        n K h (roughHeadModulus W) u v).card := by
  simpa only [tangentRoughHeadCandidateLower,
    tangentRoughHeadCandidateMain] using
      tangentRoughHeadCandidateLower_le_card
        (W := W) (n := n) (K := K) (h := h) (u := u) (v := v)
          hinterval

example :
    ∀ᶠ y : ℕ in atTop, ∀ n K h X0 u v : ℕ,
      0 < u → 0 < v →
      ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        (∑ b ∈ tangentExceptionalSmoothIndices X0 u,
            (((tangentBroadUpper n K h / (u * b) -
              n / (v * b) : ℕ) : ℝ))) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          ((X0 / u : ℕ) : ℝ) *
            (tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
              Real.log (y : ℝ) ^ 2) := by
  simpa only [tangentCanonicalExceptionalUpper,
    tangentCanonicalExceptionalLengthSum,
    tangentCanonicalExceptionalRemainder] using
      eventually_tangentExceptionalMultipliers_card_cast_le_canonicalUpper

example :
    ∀ᶠ y : ℕ in atTop, ∀ n K h X0 u v : ℕ,
      0 < u → 0 < v →
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card ≤
        ⌈
          (∑ b ∈ tangentExceptionalSmoothIndices X0 u,
              (((tangentBroadUpper n K h / (u * b) -
                n / (v * b) : ℕ) : ℝ))) *
              (tangentSelbergCanonicalMainConstant /
                Real.log (y : ℝ)) +
            ((X0 / u : ℕ) : ℝ) *
              (tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
                Real.log (y : ℝ) ^ 2)
        ⌉₊ := by
  simpa only [tangentCanonicalExceptionalNatUpper,
    tangentCanonicalExceptionalUpper,
    tangentCanonicalExceptionalLengthSum,
    tangentCanonicalExceptionalRemainder] using
      eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper

example {n X0 y u : ℕ} (hn : 0 < n) (hu : 0 < u) :
    (u : ℝ) / n *
        (((X0 / u : ℕ) : ℝ) *
          (tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2)) ≤
      tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((X0 : ℝ) * (y : ℝ) ^ 4 / n) /
          Real.log (y : ℝ) ^ 2 := by
  simpa only [tangentCanonicalExceptionalRemainder] using
    tangentCanonicalExceptionalRemainder_normalized_le hn hu

example {density : ℝ} {n v : ℕ} (hv : 0 < v) :
    density * n ≤ (⌈density * n / v⌉₊ : ℝ) * v := by
  simpa only [tangentEffectiveLowerCard] using
    tangentEffectiveLowerCard_scale
      (density := density) (n := n) (smallerLabel := v) hv

example :
    ∀ᶠ n : ℕ in atTop, ∀ K h X0 u v : ℕ,
      0 < u → 0 < v →
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card ≤
        ⌈
          (∑ b ∈ tangentExceptionalSmoothIndices X0 u,
              (((tangentBroadUpper n K h / (u * b) -
                n / (v * b) : ℕ) : ℝ))) *
              (tangentSelbergCanonicalMainConstant /
                Real.log (yNat n : ℝ)) +
            ((X0 / u : ℕ) : ℝ) *
              (tangentSelbergCanonicalLambdaConstant ^ 2 *
                  (yNat n : ℝ) ^ 4 /
                Real.log (yNat n : ℝ) ^ 2)
        ⌉₊ := by
  simpa only [tangentCanonicalExceptionalNatUpper,
    tangentCanonicalExceptionalUpper,
    tangentCanonicalExceptionalLengthSum,
    tangentCanonicalExceptionalRemainder] using
      eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper_yNat

/-- This is the generic bridge with every quantitative definition expanded.
The final natural inequality is exactly the remaining interval/log-scale
comparison. -/
example :
    ∀ᶠ n : ℕ in atTop,
      ∀ K h W X0 u v : ℕ,
      ∀ dedicatedRows numericalGuards : Finset ℕ,
      ∀ deletionUpper : ℕ, ∀ density : ℝ,
      0 < density → 0 < u → 0 < v → v ≤ u →
      n / v ≤ tangentBroadUpper n K h / u →
      (tangentDedicatedRowMultipliers (yNat n) dedicatedRows
          (tangentCommonMultiplierInterval n K h u v)).card +
          2 * numericalGuards.card ≤ deletionUpper →
      ⌈density * n / v⌉₊ +
          ⌈
            (∑ b ∈ tangentExceptionalSmoothIndices X0 u,
                (((tangentBroadUpper n K h / (u * b) -
                  n / (v * b) : ℕ) : ℝ))) *
                (tangentSelbergCanonicalMainConstant /
                  Real.log (yNat n : ℝ)) +
              ((X0 / u : ℕ) : ℝ) *
                (tangentSelbergCanonicalLambdaConstant ^ 2 *
                    (yNat n : ℝ) ^ 4 /
                  Real.log (yNat n : ℝ) ^ 2)
          ⌉₊ + deletionUpper ≤
        ⌊
          max 0
            (roughHeadDensity W *
                (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) -
              roughHeadModulus W)
        ⌋₊ →
      0 < ⌈density * n / v⌉₊ ∧
        ⌈density * n / v⌉₊ ≤
          (tangentCleanCommonMultiplierList n K h
            (roughHeadModulus W) X0 (yNat n) u v
              dedicatedRows numericalGuards).card ∧
        density * n ≤ (⌈density * n / v⌉₊ : ℝ) * u ∧
        density * n ≤ (⌈density * n / v⌉₊ : ℝ) * v := by
  simpa only [tangentEffectiveLowerCard,
    tangentCanonicalExceptionalNatUpper,
    tangentCanonicalExceptionalUpper,
    tangentCanonicalExceptionalLengthSum,
    tangentCanonicalExceptionalRemainder,
    tangentRoughHeadCandidateLower,
    tangentRoughHeadCandidateMain] using
      eventually_tangentCleanCommonMultiplierList_card_lower_canonical

/-- Sharp-bank wrapper: the only cardinality premise is the displayed final
comparison; neither candidate nor exceptional cardinality is assumed. -/
example :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : ℝ) (depth M W K h X0 u v : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional : Finset ℕ) (density : ℝ),
      fixedExceptional ⊆ Finset.Ioc (2 * n) M →
      2 ≤ W → 2 * depth + 1 ≤ W →
      W < v → v ≤ u → u ≤ yNat n →
      yNat n < centralAnchorCutoff depth n →
      u.Prime → v.Prime → 0 < density →
      n / v ≤ tangentBroadUpper n K h / u →
      tangentEffectiveLowerCard density n v +
          tangentCanonicalExceptionalNatUpper
            n K h X0 (yNat n) u v +
          4 + 4 * bankPaperSharpMarkerBudget n ≤
        tangentRoughHeadCandidateLower W n K h u v →
      0 < tangentEffectiveLowerCard density n v ∧
        tangentEffectiveLowerCard density n v ≤
          (tangentCleanCommonMultiplierList n K h
            (roughHeadModulus W) X0 (yNat n) u v
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional)).card ∧
        density * n ≤
          (tangentEffectiveLowerCard density n v : ℝ) * u ∧
        density * n ≤
          (tangentEffectiveLowerCard density n v : ℝ) * v :=
  BankPaperRealization.eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical

end

end Erdos390.WholePaper.TangentCanonicalCleanListLowerStatementAudit
