import Erdos390.WholePaper.TangentPaperCleanListAbsorption

/-! # Statement audit for the literal paper-scale tangent absorption

This covers all three public definitions and all 17 public theorem
statements from `TangentPaperCleanListAbsorption`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper.TangentPaperCleanListAbsorptionStatementAudit

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! The head choices are definitionally the Section 9 ones, while the real
exceptional threshold is represented by its least safe natural ceiling. -/

example (deltaStar : ℝ) (n : ℕ) :
    tangentPaperExceptionalCutoff deltaStar n =
      ⌈(n : ℝ) ^ deltaStar⌉₊ := rfl

example (W : ℕ) (r0 : ℝ) :
    tangentPaperHeadGap W r0 = roughHeadDensity W * (2 - r0) := rfl

example (W : ℕ) (r0 : ℝ) :
    tangentPaperCleanListDensity W r0 =
      roughHeadDensity W * (2 - r0) / 16 := rfl

example (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperHeadGap W r0 :=
  tangentPaperHeadGap_pos W hr0

example (W : ℕ) {r0 : ℝ} (hr0 : r0 < 2) :
    0 < tangentPaperCleanListDensity W r0 :=
  tangentPaperCleanListDensity_pos W hr0

/-! ## A3--A5: safe integral cutoff contracts -/

example (deltaStar : ℝ) (n : ℕ) :
    (n : ℝ) ^ deltaStar ≤
      (tangentPaperExceptionalCutoff deltaStar n : ℝ) :=
  tangentPaperExceptionalCutoff_cast_ge deltaStar n

example (deltaStar : ℝ) (n : ℕ) :
    (tangentPaperExceptionalCutoff deltaStar n : ℝ) <
      (n : ℝ) ^ deltaStar + 1 :=
  tangentPaperExceptionalCutoff_cast_lt_add_one deltaStar n

/-- The integral clean test is a strengthening of the literal paper test,
not merely an asymptotically nearby surrogate. -/
example {deltaStar : ℝ} {n y a : ℕ}
    (hscale : tangentPaperExceptionalCutoff deltaStar n ≤
      tangentRoughScale n y a) :
    (n : ℝ) ^ deltaStar ≤
      2 * (n : ℝ) / (completeRoughLabel y a : ℝ) :=
  tangentPaperExceptionalCutoff_le_roughScale_implies_real hscale

example {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    0 < tangentPaperExceptionalCutoff deltaStar n :=
  tangentPaperExceptionalCutoff_pos hdelta hn

example {deltaStar : ℝ} (hdelta : 0 ≤ deltaStar)
    {n : ℕ} (hn : 1 ≤ n) :
    Real.log (tangentPaperExceptionalCutoff deltaStar n : ℝ) ≤
      deltaStar * L n + Real.log 2 :=
  tangentPaperExceptionalCutoff_log_le hdelta hn

/-! ## A6--A11: exceptional and deterministic loss contracts -/

example {n K h X0 u v : ℕ} (hu : 0 < u) :
    tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      (2 * (n : ℝ) / (u : ℝ)) *
        (1 + Real.log (X0 : ℝ)) :=
  tangentCanonicalExceptionalLengthSum_le_harmonic hu

example {n K h X0 u v : ℕ} (hn : 0 < n) (hu : 0 < u) :
    (u : ℝ) / (n : ℝ) *
        tangentCanonicalExceptionalLengthSum n K h X0 u v ≤
      2 * (1 + Real.log (X0 : ℝ)) :=
  tangentCanonicalExceptionalLengthSum_normalized_le_harmonic hn hu

example :
    Tendsto (fun n : ℕ ↦ (yNat n : ℝ) / (n : ℝ))
      atTop (nhds 0) :=
  tangentPaper_yNat_div_self_tendsto_zero

example :
    Tendsto
      (fun n : ℕ ↦
        (((4 + 4 * bankPaperSharpMarkerBudget n : ℕ) : ℝ) *
          (yNat n : ℝ)) / (n : ℝ))
      atTop (nhds 0) :=
  tangentPaperSharpDeletion_mul_yNat_div_self_tendsto_zero

/-- Expanded canonical main loss: the only fixed loss is the explicit
`80 * C_main * deltaStar < gap` parameter choice. -/
example {W : ℕ} {r0 deltaStar : ℝ}
    (hdelta : 0 < deltaStar)
    (hsmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ K h u v : ℕ, 0 < u →
      (u : ℝ) / (n : ℝ) *
          ((∑ b ∈ tangentExceptionalSmoothIndices
                (tangentPaperExceptionalCutoff deltaStar n) u,
              (((tangentBroadUpper n K h / (u * b) -
                n / (v * b) : ℕ) : ℝ))) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (yNat n : ℝ))) ≤
        tangentPaperHeadGap W r0 / 4 := by
  simpa only [tangentCanonicalExceptionalLengthSum] using
    eventually_tangentCanonicalExceptionalMain_normalized_le_paperGap
      hdelta hsmall

/-- Expanded Lambda-squared loss: the ceiling cutoff contributes at most a
factor two to `n^(deltaStar+8/9-1)`, which remains absorbed in `gap/16`. -/
example {W : ℕ} {r0 deltaStar : ℝ}
    (hdeltaNonneg : 0 ≤ deltaStar)
    (hdelta : deltaStar < 1 / 18)
    (hgap : 0 < tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ u : ℕ, 0 < u →
      (u : ℝ) / (n : ℝ) *
          (((tangentPaperExceptionalCutoff deltaStar n / u : ℕ) : ℝ) *
            (tangentSelbergCanonicalLambdaConstant ^ 2 *
                (yNat n : ℝ) ^ 4 /
              Real.log (yNat n : ℝ) ^ 2)) ≤
        tangentPaperHeadGap W r0 / 16 := by
  simpa only [tangentCanonicalExceptionalRemainder] using
    eventually_tangentCanonicalExceptionalRemainder_normalized_le_paperGap
      hdeltaNonneg hdelta hgap

/-! ## A12--A13: pointwise and uniform candidate contracts -/

example {W n K h u v : ℕ} {r0 : ℝ}
    (hn : 0 < n) (hu : 0 < u) (hv : 0 < v)
    (hr0one : 1 < r0) (hr0two : r0 < 2)
    (hratio : (u : ℝ) / (v : ℝ) ≤ r0)
    (htail :
      roughHeadDensity W *
          (((K * h : ℕ) : ℝ) / (n : ℝ)) ≤
        tangentPaperHeadGap W r0 / 16)
    (hhead :
      (u : ℝ) / (n : ℝ) *
          (roughHeadDensity W + (roughHeadModulus W : ℝ)) ≤
        tangentPaperHeadGap W r0 / 16) :
    n / v ≤ tangentBroadUpper n K h / u ∧
      3 * tangentPaperHeadGap W r0 / 4 ≤
        (u : ℝ) / (n : ℝ) *
          tangentRoughHeadCandidateMain W n K h u v :=
  tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    hn hu hv hr0one hr0two hratio htail hhead

example (W K : ℕ) {c r0 : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ u v : ℕ,
      0 < u → 0 < v → u ≤ yNat n →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      n / v ≤ tangentBroadUpper n K (upperTailLength c n) / u ∧
        3 * tangentPaperHeadGap W r0 / 4 ≤
          (u : ℝ) / (n : ℝ) *
            tangentRoughHeadCandidateMain
              W n K (upperTailLength c n) u v :=
  eventually_tangentRoughHeadCandidateMain_normalized_ge_three_quarters
    W K hc hr0one hr0three

/-! The terminal arithmetic statement fixes `h`, `X0`, `y`, the head
modulus, and the retained density, and assumes no copy of its conclusion. -/

example (W K : ℕ) {c r0 deltaStar : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop, ∀ u v : ℕ,
      0 < u → 0 < v → v ≤ u → u ≤ yNat n →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      n / v ≤ tangentBroadUpper n K (upperTailLength c n) / u ∧
        tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n v +
            tangentCanonicalExceptionalNatUpper n K
              (upperTailLength c n)
              (tangentPaperExceptionalCutoff deltaStar n)
              (yNat n) u v +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K
            (upperTailLength c n) u v :=
  eventually_tangentPaper_candidateFloor_absorbs_canonicalLosses
    W K hc hr0one hr0three hdelta hdeltaUpper hmainSmall

/-! The bank-facing wrapper exposes only structural endpoint hypotheses and
the paper's ratio bound; interval geometry and the loss comparison have
disappeared. -/

example (W K : ℕ) {tailC r0 deltaStar : ℝ}
    (htailC : 0 < tailC) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (anchorC : ℝ) (depth M u v : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate anchorC depth n
          left right changed)
        (fixedExceptional : Finset ℕ),
      fixedExceptional ⊆ Finset.Ioc (2 * n) M →
      2 ≤ W → 2 * depth + 1 ≤ W →
      W < v → v ≤ u → u ≤ yNat n →
      yNat n < centralAnchorCutoff depth n →
      u.Prime → v.Prime →
      (u : ℝ) / (v : ℝ) ≤ r0 →
      0 < tangentEffectiveLowerCard
        (tangentPaperCleanListDensity W r0) n v ∧
      tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v ≤
        (tangentCleanCommonMultiplierList n K (upperTailLength tailC n)
          (roughHeadModulus W)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n) u v
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional)).card ∧
      tangentPaperCleanListDensity W r0 * n ≤
        (tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v : ℝ) * u ∧
      tangentPaperCleanListDensity W r0 * n ≤
        (tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n v : ℝ) * v :=
  BankPaperRealization.eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed
      W K htailC hr0one hr0three hdelta hdeltaUpper hmainSmall

end


end Erdos390.WholePaper.TangentPaperCleanListAbsorptionStatementAudit
