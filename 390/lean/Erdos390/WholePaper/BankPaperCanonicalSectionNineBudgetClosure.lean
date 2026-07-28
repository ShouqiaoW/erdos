import Erdos390.WholePaper.BankPaperCanonicalDistributedCleanListAdapter
import Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalGeometry
import Erdos390.WholePaper.BankPaperCanonicalSectionNineParameterSynchronization

/-!
# Canonical Section 9 budget closure

This connector discharges the three literal clean-list hypotheses and the
three scalar paper budgets left visible by the final Section 9 geometry
theorem.  It also turns one narrow upper estimate for the actual
Proposition 8.7 mass,

`q_n <= Cq * secondOrderScale n`,

into the exact paper-scale domination used by that theorem.

The clean density is the canonical
`tangentPaperCleanListDensity W r0`.  The main budget is finite once the
mesh width is below its explicit choice; the error and ceiling budgets are
eventual consequences of the canonical ratio-cell estimates.  The only new
analytic input is the displayed upper estimate for `q_n`, together with its
fixed scalar coefficient comparison.

The existing parameter-synchronization theorem supplies the fixed
`depth`, `W`, and `r0` facts consumed by the closure; a projection below
records this interface explicitly.  For the clean triplet we use its
distributed clean-list adapter.  That adapter reindexes the same absorbed
clean-list terminal to the literal ratio-cell earthmover, whereas the older
star-flow Section 9 absorbed wrapper has the wrong flow type here.

The Post-Hfit nonsmooth slack package is deliberately not repeated here.
It is an independent finite premise of the final geometry connector, while
the estimates below depend only on clean-list absorption, canonical cell
geometry, and scalar asymptotics.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Synchronized core parameters -/

/-- The existing Section 9 parameter synchronization supplies precisely the
fixed width, anchor-prefix, ratio, and eventual cutoff facts used by the
budget closure.  Its stronger reciprocal-sum, moment, tangent-choice, and
combined-charge conclusions remain available from the source theorem. -/
theorem exists_bankPaperCanonicalSectionNineBudgetCoreSynchronization
    {c : Real} (hc : C0 < c) :
    ∃ depth W : Nat, ∃ r0 : Real,
      2 <= W ∧
      2 * depth + 1 <= W ∧
      1 < r0 ∧
      r0 < 3 / 2 ∧
      ∀ᶠ n : Nat in atTop,
        yNat n < centralAnchorCutoff depth n := by
  obtain ⟨depth, _hdepth, W, hWtwo, hprefix, _hreciprocal,
      _hMertens, _hMoment, r0, hr0one, hr0three, _hr0two,
      _hchoice, _hterminal, hscale⟩ :=
    exists_bankPaperCanonicalSectionNineParameterSynchronization hc
  refine ⟨depth, W, r0, hWtwo, hprefix, hr0one, hr0three, ?_⟩
  filter_upwards [hscale] with n hn
  exact hn.2.2.1

/-! ## Exact logarithmic and actual-mass reductions -/

/-- The literal bridge logarithm cancels the second-order denominator once
the bridge sample index is synchronized with the ambient index. -/
theorem bankPaperCanonical_bridgeL_mul_secondOrderScale_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {n : Nat}
    (hBn : B.sampleData.n = n) :
    B.L * secondOrderScale n = (n : Real) := by
  subst n
  change
    Real.log (B.sampleData.n : Real) *
        ((B.sampleData.n : Real) /
          Real.log (B.sampleData.n : Real)) =
      (B.sampleData.n : Real)
  have hlog : Real.log (B.sampleData.n : Real) ≠ 0 := by
    simpa only [BridgeData.L] using B.L_pos.ne'
  field_simp [hlog]

/-- A pointwise actual-P87 mass upper bound implies the exact Section 9
paper-scale comparison.  No bound on `q` other than the displayed one is
used. -/
theorem bankPaperCanonical_actualP87Scale_le_secondOrderScale_of_q_upper
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {n : Nat}
    {Cpost Cq tangentConstant : Real}
    (hBn : B.sampleData.n = n)
    (hCpost : 0 <= Cpost)
    (hqUpper : B.q <= Cq * secondOrderScale n)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq <= tangentConstant) :
    Cpost * B.q / B.L <=
      tangentConstant * secondOrderScale n / Real.log (y n) := by
  have hn : 1 < n := by
    simpa only [hBn] using B.n_gt_one
  have hN : 0 <= secondOrderScale n :=
    (secondOrderScale_pos (by omega)).le
  have hqScaled :
      Cpost * B.q <= Cpost * (Cq * secondOrderScale n) :=
    mul_le_mul_of_nonneg_left hqUpper hCpost
  have hqNormalized :
      (2 / 9 : Real) * (Cpost * B.q) <=
        (2 / 9 : Real) * (Cpost * (Cq * secondOrderScale n)) :=
    mul_le_mul_of_nonneg_left hqScaled (by norm_num)
  have hcoefficientScaled :
      ((2 / 9 : Real) * Cpost * Cq) * secondOrderScale n <=
        tangentConstant * secondOrderScale n :=
    mul_le_mul_of_nonneg_right hcoefficient hN
  have hnormalized :
      (2 / 9 : Real) * (Cpost * B.q) <=
        tangentConstant * secondOrderScale n := by
    calc
      (2 / 9 : Real) * (Cpost * B.q) <=
          (2 / 9 : Real) *
            (Cpost * (Cq * secondOrderScale n)) := hqNormalized
      _ = ((2 / 9 : Real) * Cpost * Cq) * secondOrderScale n := by
        ring
      _ <= tangentConstant * secondOrderScale n := hcoefficientScaled
  have hscale :=
    bankPaperCanonical_actualP87Scale_le_paperScale_of_normalized
      B hnormalized
  simpa only [hBn] using hscale

/-! ## The exact downstream package -/

/-- The literal clean-list, budget, and scale hypotheses consumed by
`bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack`.

The first two fields record synchronization of the actual bridge sample
with the ambient canonical index and width.  After rewriting by those
equalities, every remaining field has exactly the type of the corresponding
premise in the final geometry theorem: three clean-list fields, three paper
budgets, the actual-scale domination, and the logarithmic scale identity,
with
`N = secondOrderScale n` and
`density = tangentPaperCleanListDensity W r0`. -/
def BankPaperCanonicalSectionNineBudgetClosure
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : BridgeData Head (BankPaperCanonicalExponentBand M))
    {c : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma : Real)
    (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W)
    (r0 rho tangentConstant Cpost : Real)
    (endpoint : Nat -> Real) : Prop :=
  B.sampleData.n = n ∧
  B.sampleData.W = W ∧
  let density := tangentPaperCleanListDensity W r0
  let flow :=
    R.bankPaperCanonicalSectionNineRatioCellFlow
      M certificate deltaStar (K0 + 1) hdelta hn hW S rho endpoint
  (∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
    0 < bankPaperCanonicalDistributedTangentLowerCard
      (density := density) request) ∧
  (∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
    bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request <=
      (tangentSplitCleanMultiplierLists
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        B.L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2)
        n (K0 + 1) (upperTailLength c n) (roughHeadModulus W)
        (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar)) request).card) ∧
  (∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
    ∀ side,
      density * n <=
        (bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request : Real) *
          tangentEndpointLabel
            bankPaperCanonicalDistributedTangentRequestSource
            bankPaperCanonicalDistributedTangentRequestTarget
            side request) ∧
  tangentDistributedPaperMainBudget
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio) sigma <= density ^ 2 / 48 ∧
  tangentDistributedPaperErrorBudget
      (bankPaperCanonicalRatioCellTrafficErrorCoefficient
        M n W rho tangentConstant)
      (bankPaperCanonicalRatioCellIncidentErrorCoefficient
        W n rho tangentConstant)
      sigma <= density ^ 2 / 96 ∧
  tangentDistributedPaperCeilingBudget n (yNat n)
      (tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime n W)) <= density ^ 2 / 96 ∧
  Cpost * B.q / B.L <=
      tangentConstant * secondOrderScale n / Real.log (y n) ∧
  B.L * secondOrderScale n = (n : Real)

/-! ## Eventual closure -/

/-- Close the seven requested clean-list/budget/scale estimates, together
with the exact logarithmic scale identity, for synchronized actual bridge
data.

The one external asymptotic premise is `hqUpper`.  It is deliberately a
bound only for the actual active mass `B n |>.q`; all clean-list bounds,
the main/error/ceiling budgets, the normalized paper-scale domination, and
the identity `B.L * secondOrderScale n = n` are derived. -/
theorem eventually_bankPaperCanonicalSectionNineBudgetClosure
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : Nat -> BridgeData Head (BankPaperCanonicalExponentBand M))
    (W K0 depth : Nat)
    {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
    (hdelta : 0 < delta)
    (hc : 0 < c)
    (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hcleanMainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0)
    (hWtwo : 2 <= W) (hprefix : 2 * depth + 1 <= W)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hwidth :
      delta + M.ratio <=
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant)
    (hCpost : 0 <= Cpost)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq <= tangentConstant)
    (hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W)
    (hqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q <= Cq * secondOrderScale n) :
    ∀ᶠ n : Nat in atTop,
      ∀ (hn : 1 < n) (hW : W ≠ 0)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (S : ScaleSeparation M n W)
        (endpoint : Nat -> Real),
      BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M (B n) R certificate deltaStar sigma
        hdelta hn hW S r0 rho tangentConstant Cpost endpoint := by
  have hr0two : r0 < 2 := hr0three.trans (by norm_num)
  have hdensity :
      0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W hr0two
  have hclean :=
    BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed
      W (K0 + 1) hc hr0one hr0three
      hdeltaStar hdeltaUpper hcleanMainSmall
  have herror :=
    eventually_bankPaperCanonical_paperErrorBudget_le
      M W rho tangentConstant
      (tangentPaperCleanListDensity W r0) sigma hdensity hsigma
  have hceiling :=
    eventually_tangentDistributedPaperCeilingBudget_canonical_le
      W hdensity
  have hcutoff :=
    eventually_yNat_lt_centralAnchorCutoff depth
  filter_upwards [hclean, herror, hceiling, hcutoff, hsync, hqUpper] with
    n hcleanN herrorN hceilingN hcutoffN hsyncN hqN
  obtain ⟨hBnN, hBWN⟩ := hsyncN
  intro hn hW R certificate S endpoint
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1)
  let lastCell :=
    bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
  let residual :=
    bankPaperCanonicalTangentResidual (W := W) R certificate
      fixed candidates endpoint
  let bandOf :=
    bankPaperCanonicalExponentBandOf M hdelta hn hW S
  let cellIndex :=
    bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho
  have hfixedTail :
      fixed ⊆ Finset.Ioc (2 * n)
        (upperEndpoint n (upperTailLength c n)) := by
    simpa only [fixed] using
      R.paperFixedExceptionalFactors_subset_tail deltaStar
  have hgeometry :
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        bandOf cellIndex r0 := by
    dsimp only [bandOf, cellIndex]
    exact bankPaperCanonical_tangentRatioCellGeometry
      (rho := rho) (r0 := r0) M hdelta hn hW S hrho hratio
  have hcleanData :=
    hcleanN depth
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)
      R certificate fixed
      (Band := BankPaperCanonicalExponentBand M)
      lastCell residual bandOf cellIndex (B n).L sigma
      hfixedTail hWtwo hprefix hcutoffN hgeometry
  have hmain :
      tangentDistributedPaperMainBudget
          (bankPaperCanonicalRatioCellTrafficConstant rho)
          (bankPaperCanonicalRatioCellIncidentConstant rho)
          tangentConstant (delta + M.ratio) sigma <=
        (tangentPaperCleanListDensity W r0) ^ 2 / 48 :=
    bankPaperCanonical_paperMainBudget_le
      hsigma hrho htangent hwidth
  have htrafficCoefficient :=
    bankPaperCanonical_ratioCellTrafficErrorCoefficient_le_upper
      M hn hWtwo herrorN.1 hrho htangent.le
  have htrafficWeighted :
      16 * bankPaperCanonicalRatioCellTrafficErrorCoefficient
          M n W rho tangentConstant <=
        16 * bankPaperCanonicalRatioCellTrafficErrorUpperCoefficient
          M W n rho tangentConstant :=
    mul_le_mul_of_nonneg_left htrafficCoefficient (by norm_num)
  have herrorRaw :
      tangentDistributedPaperErrorBudget
          (bankPaperCanonicalRatioCellTrafficErrorCoefficient
            M n W rho tangentConstant)
          (bankPaperCanonicalRatioCellIncidentErrorCoefficient
            W n rho tangentConstant)
          sigma <=
        (tangentPaperCleanListDensity W r0) ^ 2 / 96 := by
    apply le_trans ?_ herrorN.2
    unfold tangentDistributedPaperErrorBudget
    exact div_le_div_of_nonneg_right
      (add_le_add htrafficWeighted (le_refl _)) hsigma.le
  have hscaleDom :
      Cpost * (B n).q / (B n).L <=
        tangentConstant * secondOrderScale n / Real.log (y n) :=
    bankPaperCanonical_actualP87Scale_le_secondOrderScale_of_q_upper
      (B n) hBnN hCpost hqN hcoefficient
  have hscale :
      (B n).L * secondOrderScale n = (n : Real) :=
    bankPaperCanonical_bridgeL_mul_secondOrderScale_eq (B n) hBnN
  unfold BankPaperCanonicalSectionNineBudgetClosure
  refine ⟨hBnN, hBWN, ?_, ?_, ?_, hmain, herrorRaw,
    hceilingN, hscaleDom, hscale⟩
  · simpa only [fixed, candidates, lastCell, residual, bandOf, cellIndex,
      BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow] using
      hcleanData.1
  · simpa only [fixed, candidates, lastCell, residual, bandOf, cellIndex,
      BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow] using
      hcleanData.2.1
  · simpa only [fixed, candidates, lastCell, residual, bandOf, cellIndex,
      BankPaperRealization.bankPaperCanonicalSectionNineRatioCellFlow] using
      hcleanData.2.2

end

end Erdos390.WholePaper
