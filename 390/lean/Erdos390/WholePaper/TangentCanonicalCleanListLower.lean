import Erdos390.WholePaper.TangentCleanListCardinalityBridge
import Erdos390.WholePaper.TangentExceptionalCanonicalBounds

/-!
# Canonical eventual lower bounds for tangent clean lists

This file composes the three previously separate parts of the tangent-list
cardinality argument.

* `FixedModulusReducedResidueCount` gives a lower bound for the literal
  candidate interval

  `(n / v, tangentBroadUpper n K h / u]`

  with modulus `roughHeadModulus W`.  The endpoint loss is the literal
  modulus, not an absorbed constant.
* `TangentExceptionalCanonicalBounds` is applied to every rough-label
  interval indexed by a smooth factor `b`.  The resulting exceptional upper
  bound is assumption-free eventually in `y` and then in `yNat n`.
* `TangentCleanListCardinalityBridge` subtracts that exceptional bound and
  the declared deterministic deletion budget from the candidate lower bound.

The accumulated canonical remainder is displayed as

`(X0 / u) * C_lambda^2 * y^4 / log(y)^2`.

After normalization by the candidate scale `n/u`, it is bounded by the
explicit quantity

`C_lambda^2 * (X0 * y^4 / n) / log(y)^2`.

Thus the power-saving input is genuinely `X0*y^4/n`; the logarithmic square
does not conceal the required scale.  The final paper wrappers leave only an
explicit comparison between the candidate floor and the effective lower-card
ceiling plus the exceptional and deterministic losses.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal candidate lower bound -/

/-- The real fixed-head candidate main term, including its exact one-period
endpoint loss. -/
def tangentRoughHeadCandidateMain
    (W n K h u v : ℕ) : ℝ :=
  roughHeadDensity W *
      (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ)) -
    roughHeadModulus W

/-- A natural lower bound obtained by flooring the nonnegative part of the
literal fixed-head candidate main term. -/
def tangentRoughHeadCandidateLower
    (W n K h u v : ℕ) : ℕ :=
  ⌊max 0 (tangentRoughHeadCandidateMain W n K h u v)⌋₊

/-- Fixed-modulus periodicity supplies the candidate lower bound on the
literal common-multiplier interval. -/
theorem tangentRoughHeadCandidateLower_le_card
    {W n K h u v : ℕ}
    (hinterval : n / v ≤ tangentBroadUpper n K h / u) :
    tangentRoughHeadCandidateLower W n K h u v ≤
      (tangentHeadCoprimeCandidates
        n K h (roughHeadModulus W) u v).card := by
  have herror := reducedResidueIoc_card_error_le_modulus
    (roughHeadModulus_pos W) hinterval
  have herror' :
      abs (((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) -
        roughHeadDensity W *
          (((tangentBroadUpper n K h / u - n / v : ℕ) : ℝ))) ≤
        (roughHeadModulus W : ℝ) := by
    simpa only [fixedModulusReducedResidueDensity, roughHeadDensity]
      using herror
  have hmainLower :
      tangentRoughHeadCandidateMain W n K h u v ≤
        ((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) := by
    unfold tangentRoughHeadCandidateMain
    linarith [(abs_le.mp herror').1]
  have hnonneg :
      (0 : ℝ) ≤
        ((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) :=
    Nat.cast_nonneg _
  have hmax :
      max 0 (tangentRoughHeadCandidateMain W n K h u v) ≤
        ((reducedResidueIoc (roughHeadModulus W) (n / v)
          (tangentBroadUpper n K h / u)).card : ℝ) :=
    max_le hnonneg hmainLower
  have hfloor :
      (tangentRoughHeadCandidateLower W n K h u v : ℝ) ≤
        max 0 (tangentRoughHeadCandidateMain W n K h u v) := by
    unfold tangentRoughHeadCandidateLower
    exact Nat.floor_le (le_max_left _ _)
  rw [tangentHeadCoprimeCandidates_eq_reducedResidueIoc]
  exact_mod_cast (hfloor.trans hmax)

/-! ## Assumption-free canonical exceptional upper bound -/

/-- Sum of the literal rough-label interval lengths over the exact smooth
factor index set. -/
def tangentCanonicalExceptionalLengthSum
    (n K h X0 u v : ℕ) : ℝ :=
  ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
    (((tangentBroadUpper n K h / (u * b) - n / (v * b) : ℕ) : ℝ))

/-- Accumulated endpoint remainder in the canonical exceptional-row sieve.
The factor `X0/u` is the exact smooth-index census upper bound. -/
def tangentCanonicalExceptionalRemainder
    (X0 y u : ℕ) : ℝ :=
  ((X0 / u : ℕ) : ℝ) *
    (tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
      Real.log (y : ℝ) ^ 2)

/-- The complete canonical exceptional upper bound: summed interval main
term plus the accumulated `y^4` endpoint remainder. -/
def tangentCanonicalExceptionalUpper
    (n K h X0 y u v : ℕ) : ℝ :=
  tangentCanonicalExceptionalLengthSum n K h X0 u v *
      (tangentSelbergCanonicalMainConstant / Real.log (y : ℝ)) +
    tangentCanonicalExceptionalRemainder X0 y u

/-- Natural ceiling of the canonical exceptional upper bound, in the exact
form consumed by the finite-cardinality bridge. -/
def tangentCanonicalExceptionalNatUpper
    (n K h X0 y u v : ℕ) : ℕ :=
  ⌈tangentCanonicalExceptionalUpper n K h X0 y u v⌉₊

/-- Applying the assumption-free canonical interval theorem to every smooth
factor gives the complete exceptional-row estimate, uniformly in all finite
interval parameters. -/
theorem eventually_tangentExceptionalMultipliers_card_cast_le_canonicalUpper :
    ∀ᶠ y : ℕ in atTop, ∀ n K h X0 u v : ℕ,
      0 < u → 0 < v →
      ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        tangentCanonicalExceptionalUpper n K h X0 y u v := by
  filter_upwards
    [eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead]
      with y hy
  intro n K h X0 u v hu hv
  let mainTerm :=
    tangentSelbergCanonicalMainConstant / Real.log (y : ℝ)
  let remainderTerm :=
    tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
      Real.log (y : ℝ) ^ 2
  have hremainderNonneg : 0 ≤ remainderTerm := by
    dsimp only [remainderTerm]
    positivity
  have hcount := card_tangentExceptionalMultipliers_le_sieveSum
    (n := n) (K := K) (h := h) (X0 := X0) (y := y)
      (u := u) (v := v) hu hv
  have hindexCard :
      ((tangentExceptionalSmoothIndices X0 u).card : ℝ) ≤
        ((X0 / u : ℕ) : ℝ) := by
    exact_mod_cast card_tangentExceptionalSmoothIndices_le_div hu
  calc
    ((tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card : ℝ) ≤
        ((∑ b ∈ tangentExceptionalSmoothIndices X0 u,
          (tangentExceptionalRoughCandidates
            n K h y u v b).card : ℕ) : ℝ) := by
      exact_mod_cast hcount
    _ = ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        ((tangentExceptionalRoughCandidates
          n K h y u v b).card : ℝ) := by
      push_cast
      rfl
    _ ≤ ∑ b ∈ tangentExceptionalSmoothIndices X0 u,
        (((tangentBroadUpper n K h / (u * b) -
            n / (v * b) : ℕ) : ℝ) * mainTerm + remainderTerm) := by
      apply Finset.sum_le_sum
      intro b _hb
      simpa only [tangentExceptionalRoughCandidates, mainTerm,
        remainderTerm] using
          hy (n / (v * b)) (tangentBroadUpper n K h / (u * b))
    _ = tangentCanonicalExceptionalLengthSum n K h X0 u v * mainTerm +
        ((tangentExceptionalSmoothIndices X0 u).card : ℝ) *
          remainderTerm := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [Finset.sum_const, nsmul_eq_mul,
        tangentCanonicalExceptionalLengthSum]
    _ ≤ tangentCanonicalExceptionalLengthSum n K h X0 u v * mainTerm +
        ((X0 / u : ℕ) : ℝ) * remainderTerm := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hindexCard hremainderNonneg) _
    _ = tangentCanonicalExceptionalUpper n K h X0 y u v := by
      simp only [tangentCanonicalExceptionalUpper,
        tangentCanonicalExceptionalRemainder, mainTerm, remainderTerm]

/-- Natural-cardinality form of the preceding eventual estimate. -/
theorem eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper :
    ∀ᶠ y : ℕ in atTop, ∀ n K h X0 u v : ℕ,
      0 < u → 0 < v →
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card ≤
        tangentCanonicalExceptionalNatUpper n K h X0 y u v := by
  filter_upwards
    [eventually_tangentExceptionalMultipliers_card_cast_le_canonicalUpper]
      with y hy
  intro n K h X0 u v hu hv
  have hreal := hy n K h X0 u v hu hv
  have hceil := hreal.trans
    (Nat.le_ceil (tangentCanonicalExceptionalUpper n K h X0 y u v))
  unfold tangentCanonicalExceptionalNatUpper
  exact_mod_cast hceil

/-- The accumulated remainder really has relative scale `X0*y^4/n` after
normalization by `n/u`.  No logarithmic or floor loss is hidden here. -/
theorem tangentCanonicalExceptionalRemainder_normalized_le
    {n X0 y u : ℕ} (hn : 0 < n) (hu : 0 < u) :
    (u : ℝ) / n * tangentCanonicalExceptionalRemainder X0 y u ≤
      tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((X0 : ℝ) * (y : ℝ) ^ 4 / n) /
          Real.log (y : ℝ) ^ 2 := by
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have huReal : 0 < (u : ℝ) := by exact_mod_cast hu
  have hfloorDiv :
      ((X0 / u : ℕ) : ℝ) ≤ (X0 : ℝ) / u :=
    Nat.cast_div_le
  let endpointTerm :=
    tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
      Real.log (y : ℝ) ^ 2
  have hendpointNonneg : 0 ≤ endpointTerm := by
    dsimp only [endpointTerm]
    positivity
  have hcancel : ∀ z : ℝ,
      (u : ℝ) / n * (((X0 : ℝ) / u) * z) =
        (X0 : ℝ) / n * z := by
    intro z
    field_simp [hnReal.ne', huReal.ne']
  calc
    (u : ℝ) / n * tangentCanonicalExceptionalRemainder X0 y u =
        (u : ℝ) / n * (((X0 / u : ℕ) : ℝ) * endpointTerm) := by
      rfl
    _ ≤ (u : ℝ) / n * (((X0 : ℝ) / u) * endpointTerm) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right hfloorDiv hendpointNonneg
      · exact div_nonneg huReal.le hnReal.le
    _ = (X0 : ℝ) / n * endpointTerm := hcancel endpointTerm
    _ = tangentSelbergCanonicalLambdaConstant ^ 2 *
        ((X0 : ℝ) * (y : ℝ) ^ 4 / n) /
          Real.log (y : ℝ) ^ 2 := by
      dsimp only [endpointTerm]
      ring

/-! ## Effective lower cards and eventual bridge theorems -/

/-- The lower-card choice suited to the pair-arithmetic scale at the smaller
endpoint label. -/
def tangentEffectiveLowerCard
    (density : ℝ) (n smallerLabel : ℕ) : ℕ :=
  ⌈density * n / smallerLabel⌉₊

/-- Multiplying the effective ceiling by its defining endpoint label
recovers at least the requested real density scale. -/
theorem tangentEffectiveLowerCard_scale
    {density : ℝ} {n smallerLabel : ℕ}
    (hsmaller : 0 < smallerLabel) :
    density * n ≤
      (tangentEffectiveLowerCard density n smallerLabel : ℝ) *
        smallerLabel := by
  unfold tangentEffectiveLowerCard
  apply (div_le_iff₀ (by exact_mod_cast hsmaller)).mp
  exact Nat.le_ceil (density * (n : ℝ) / smallerLabel)

private theorem tangentCanonicalClean_yNat_tendsto_atTop :
    Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

/-- Assumption-free exceptional-cardinality estimate on the paper's moving
cutoff `yNat n`. -/
theorem eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper_yNat :
    ∀ᶠ n : ℕ in atTop, ∀ K h X0 u v : ℕ,
      0 < u → 0 < v →
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h u v)).card ≤
        tangentCanonicalExceptionalNatUpper
          n K h X0 (yNat n) u v := by
  have hevent := tangentCanonicalClean_yNat_tendsto_atTop.eventually
    eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper
  filter_upwards [hevent] with n hn
  intro K h X0 u v hu hv
  exact hn n K h X0 u v hu hv

/-- Generic eventual clean-list theorem.  Candidate and exceptional
cardinality estimates are proved internally.  The remaining premise is the
literal natural-number comparison between the effective lower-card ceiling,
canonical exceptional ceiling, deterministic deletions, and fixed-head
candidate floor. -/
theorem eventually_tangentCleanCommonMultiplierList_card_lower_canonical :
    ∀ᶠ n : ℕ in atTop,
      ∀ K h W X0 u v : ℕ,
      ∀ dedicatedRows numericalGuards : Finset ℕ,
      ∀ deletionUpper : ℕ, ∀ density : ℝ,
      0 < density → 0 < u → 0 < v → v ≤ u →
      n / v ≤ tangentBroadUpper n K h / u →
      (tangentDedicatedRowMultipliers (yNat n) dedicatedRows
          (tangentCommonMultiplierInterval n K h u v)).card +
          2 * numericalGuards.card ≤ deletionUpper →
      tangentEffectiveLowerCard density n v +
          tangentCanonicalExceptionalNatUpper
            n K h X0 (yNat n) u v + deletionUpper ≤
        tangentRoughHeadCandidateLower W n K h u v →
      0 < tangentEffectiveLowerCard density n v ∧
        tangentEffectiveLowerCard density n v ≤
          (tangentCleanCommonMultiplierList n K h
            (roughHeadModulus W) X0 (yNat n) u v
              dedicatedRows numericalGuards).card ∧
        density * n ≤
          (tangentEffectiveLowerCard density n v : ℝ) * u ∧
        density * n ≤
          (tangentEffectiveLowerCard density n v : ℝ) * v := by
  filter_upwards
    [eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper_yNat,
      eventually_gt_atTop 0]
      with n hexceptional hn
  intro K h W X0 u v dedicatedRows numericalGuards deletionUpper density
    hdensity hu hv hvu hinterval hdeletion harithmetic
  have hcandidate := tangentRoughHeadCandidateLower_le_card
    (W := W) (n := n) (K := K) (h := h) (u := u) (v := v) hinterval
  have hlower := tangentCleanCommonMultiplierList_card_lower_of_headCandidate
    (n := n) (K := K) (h := h) (Phead := roughHeadModulus W)
      (X0 := X0) (y := yNat n) (u := u) (v := v)
      dedicatedRows numericalGuards
      (candidateLower := tangentRoughHeadCandidateLower W n K h u v)
      (exceptionalUpper := tangentCanonicalExceptionalNatUpper
        n K h X0 (yNat n) u v)
      (deletionUpper := deletionUpper)
      (lowerCard := tangentEffectiveLowerCard density n v)
      hu hv hcandidate
      (hexceptional K h X0 u v hu hv) hdeletion harithmetic
  have hscaleV := tangentEffectiveLowerCard_scale
    (density := density) (n := n) (smallerLabel := v) hv
  have hlowerPos : 0 < tangentEffectiveLowerCard density n v := by
    unfold tangentEffectiveLowerCard
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos hdensity (by exact_mod_cast hn))
      (by exact_mod_cast hv)
  have hscaleU :
      density * (n : ℝ) ≤
        (tangentEffectiveLowerCard density n v : ℝ) * u := by
    exact hscaleV.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hvu) (Nat.cast_nonneg _))
  exact ⟨hlowerPos, hlower, hscaleU, hscaleV⟩

namespace BankPaperRealization

/-- Sharp-paper-facing eventual theorem.  The actual canonical exceptional
estimate and fixed-head candidate count are invoked internally; only the
displayed interval geometry and the final density-versus-loss comparison
remain. -/
theorem eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical :
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
          (tangentEffectiveLowerCard density n v : ℝ) * v := by
  filter_upwards
    [eventually_tangentExceptionalMultipliers_card_le_canonicalNatUpper_yNat,
      eventually_gt_atTop 0]
      with n hexceptional hn
  intro c depth M W K h X0 u v left right changed R certificate
    fixedExceptional density hfixedTail hTwoW hPrefix hWv hvu huy
    hyCutoff huPrime hvPrime hdensity hinterval harithmetic
  have hcandidate := tangentRoughHeadCandidateLower_le_card
    (W := W) (n := n) (K := K) (h := h) (u := u) (v := v) hinterval
  have hlower :=
    R.tangentPaperCleanCommonMultiplierList_card_lower_of_headCandidate
      (W := W) (K := K) (h := h) (Phead := roughHeadModulus W)
        (X0 := X0) (u := u) (v := v) certificate fixedExceptional
        hfixedTail hTwoW hPrefix hWv hvu huy hyCutoff huPrime hvPrime
        (candidateLower := tangentRoughHeadCandidateLower W n K h u v)
        (exceptionalUpper := tangentCanonicalExceptionalNatUpper
          n K h X0 (yNat n) u v)
        (lowerCard := tangentEffectiveLowerCard density n v)
        hcandidate (hexceptional K h X0 u v huPrime.pos hvPrime.pos)
        harithmetic
  have hscaleV := tangentEffectiveLowerCard_scale
    (density := density) (n := n) (smallerLabel := v) hvPrime.pos
  have hlowerPos : 0 < tangentEffectiveLowerCard density n v := by
    unfold tangentEffectiveLowerCard
    apply Nat.ceil_pos.mpr
    exact div_pos (mul_pos hdensity (by exact_mod_cast hn))
      (by exact_mod_cast hvPrime.pos)
  have hscaleU :
      density * (n : ℝ) ≤
        (tangentEffectiveLowerCard density n v : ℝ) * u := by
    exact hscaleV.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hvu) (Nat.cast_nonneg _))
  exact ⟨hlowerPos, hlower, hscaleU, hscaleV⟩

end BankPaperRealization

end

end Erdos390.WholePaper
