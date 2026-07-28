import Erdos390.WholePaper.BankPaperCanonicalRawBroadSurplusAsymptotic
import Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale
import Erdos390.WholePaper.BankPaperCanonicalActualEndpointSlackConnector

/-!
# Canonical nonsmooth endpoint-slack closure

This module connects the sharp balanced raw-row estimate to the literal
guarded constant-pool correction used at the actual Proposition 8.7
endpoint.

There are two finite guard estimates.  The sharp one assumes the usual
raw-point box and proves that passing through all numerical guards changes
one active row discrepancy by at most `2`.  The assumption-free one uses
the already proved uniform absolute bound for the balanced coefficient and
gives a fixed (slightly larger) numerator constant.  The latter is the
version used in the eventual theorem, so no unproved eventual feasibility
of `roughHeadBalancedAlpha` is hidden in the endpoint-slack conclusion.

The final bounds use the paper split

`beta = betaProt + betaAct`, `0 < betaAct`, `sigma <= betaProt`.

Thus the lower nonsmooth margin has the fixed strict reserve `betaAct/L`.
The upper margin follows once `L` exceeds the fixed sum of the parameters.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.Scale
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Filter Topology
open scoped BigOperators

noncomputable section

namespace BankPaperRealization

/-! ## Active rows contain no fixed exceptional factor -/

/-- A fixed exceptional factor has the strict exceptional inequality, so
its complete-row multiplicity vanishes on an active nonexceptional row. -/
theorem paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) (label : Nat)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label = 0 := by
  unfold completeLabelMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a haFixed haLabel
  have haData := (R.mem_paperFixedExceptionalFactors (a := a)).mp haFixed
  have hexceptional :
      2 * (n : Real) / (label : Real) < (n : Real) ^ deltaStar := by
    simpa only [haLabel] using haData.2.1
  exact (not_lt_of_ge hactive.2) hexceptional

/-- Injectivity of the base marker map gives at most one bank base in each
complete rough row. -/
theorem prechargeBaseState_completeLabelMultiplicity_le_one
    {n M label : Nat} (R : BankPaperRealization n M) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label <= 1 := by
  have hcard :=
    R.completeRoughRowFiber_inter_prechargeBaseState_card_le_one
      (label := label) R.prechargeBaseState
  change
    ((R.prechargeBaseState.filter
        (fun a => completeRoughLabel (yNat n) a = label)) ∩
      R.prechargeBaseState).card <= 1 at hcard
  rw [Finset.inter_eq_left.mpr (Finset.filter_subset _ _)] at hcard
  simpa only [completeLabelMultiplicity] using hcard

/-- If the base multiplicity is zero, neither a base nor its alternate can
occur in the deleted row.  The alternate exclusion uses the fact that both
states have the same retained prime marker. -/
theorem roughCanonicalGuardDeletedRow_subset_anchorRow_of_baseMultiplicity_zero
    {c : Real} {depth n h K label : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hbase :
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label = 0) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label ⊆
      completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) label ∩
        certificate.anchors := by
  classical
  have hnoBase :
      ∀ b ∈ R.prechargeBaseState,
        completeRoughLabel (yNat n) b ≠ label := by
    intro b hb hblabel
    have hmem :
        b ∈ R.prechargeBaseState.filter
          (fun a => completeRoughLabel (yNat n) a = label) :=
      Finset.mem_filter.mpr ⟨hb, hblabel⟩
    have hpos :
        0 < completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label := by
      unfold completeLabelMultiplicity
      exact Finset.card_pos.mpr ⟨b, hmem⟩
    omega
  intro a ha
  have haDeleted := Finset.mem_inter.mp ha
  have haLabel := (mem_completeRoughRowFiber.mp haDeleted.1).2
  have haSupport :=
    R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
      certificate deltaStar K label ha
  apply Finset.mem_inter.mpr
  refine ⟨haDeleted.1, ?_⟩
  rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
  · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
    · exact haAnchor
    · exact (hnoBase a haBase haLabel).elim
  · rw [prechargeAlternateState, indexedPathState,
      Finset.mem_image] at haAlternate
    obtain ⟨request, _hrequest, rfl⟩ := haAlternate
    have hbaseMem :=
      R.prechargeBaseStateValue_mem_prechargeBaseState request
    exact (hnoBase (R.prechargeBaseStateValue request) hbaseMem (by
      rw [R.prechargeBase_completeRoughLabel_eq_marker,
        ← R.prechargeAlternate_completeRoughLabel_eq_marker]
      exact haLabel)).elim

/-- In the zero-base branch, the local deletion set has cardinality at most
one rather than merely at most three. -/
theorem roughCanonicalGuardDeletedRow_card_le_one_of_baseMultiplicity_zero
    {c : Real} {depth n h K label : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hlabel : label ≠ 1)
    (hbase :
      completeLabelMultiplicity (yNat n) R.prechargeBaseState label = 0) :
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K label).card <=
      1 := by
  have hsubset :=
    R.roughCanonicalGuardDeletedRow_subset_anchorRow_of_baseMultiplicity_zero
      (K := K) certificate deltaStar hbase
  have hcard := Finset.card_le_card hsubset
  have hyTwo : 2 <= yNat n := by
    have hySix := R.six_le_yNat
    omega
  exact hcard.trans
    (completeRoughRowFiber_inter_guardedCentralAnchors_card_le_one
      certificate hnCutoff hyTwo hyCutoff label hlabel)

/-! ## The sharp finite `+2` guard numerator -/

/-- On an active row, deleting the numerical guards and subtracting the
bank-base quota changes the raw discrepancy by at most two, provided the
raw coordinates lie in `[0,1]`.

If the base multiplicity is one, the deleted mass lies in `[0,3]`, so
`|-1 + deletedMass| <= 2`.  If it is zero, the preceding marker argument
reduces the deleted set to at most one anchor. -/
theorem roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_two
    {c : Real} {depth n h K label : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (x : Nat -> Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hx : ∀ a ∈ completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label,
      0 <= x a ∧ x a <= 1) :
    |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x -
      roughCanonicalRawRowDiscrepancy n h K label x| <= 2 := by
  let D :=
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label
  let m :=
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label
  have hfixed :=
    R.paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
      deltaStar label hactive
  have hmLe : m <= 1 := by
    dsimp only [m]
    exact
      R.prechargeBaseState_completeLabelMultiplicity_le_one
        (label := label)
  have hsumNonneg : 0 <= ∑ a ∈ D, x a := by
    apply Finset.sum_nonneg
    intro a ha
    exact (hx a (Finset.mem_inter.mp ha).1).1
  have hledger :=
    R.roughCanonicalGuardLocalDiscrepancyLedger certificate deltaStar
      K label x
  rw [hfixed, Nat.cast_zero, neg_zero, zero_sub] at hledger
  change
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          K label x -
        roughCanonicalRawRowDiscrepancy n h K label x =
      -(m : Real) + ∑ a ∈ D, x a at hledger
  by_cases hmZero : m = 0
  · have hcard : D.card <= 1 := by
      apply R.roughCanonicalGuardDeletedRow_card_le_one_of_baseMultiplicity_zero
        (K := K) certificate deltaStar hnCutoff hyCutoff hactive.1
      simpa only [m] using hmZero
    have hsumUpper : (∑ a ∈ D, x a) <= 1 := by
      calc
        (∑ a ∈ D, x a) <= ∑ _a ∈ D, (1 : Real) := by
          exact Finset.sum_le_sum fun a ha => (hx a
            (Finset.mem_inter.mp ha).1).2
        _ = (D.card : Real) := by simp
        _ <= 1 := by exact_mod_cast hcard
    rw [hmZero, Nat.cast_zero, neg_zero, zero_add] at hledger
    rw [hledger]
    have habs : |∑ a ∈ D, x a| <= (1 : Real) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    exact habs.trans (by norm_num)
  · have hmOne : m = 1 := by omega
    have hcensus :
        RoughCanonicalGuardLocalCensusBound R certificate deltaStar
          K label 3 :=
      R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
        deltaStar K label hnCutoff hyCutoff hactive
    have hsumUpper : (∑ a ∈ D, x a) <= 3 := by
      calc
        (∑ a ∈ D, x a) <= ∑ _a ∈ D, (1 : Real) := by
          exact Finset.sum_le_sum fun a ha => (hx a
            (Finset.mem_inter.mp ha).1).2
        _ = (D.card : Real) := by simp
        _ <= 3 := by
          have hcensusNat : D.card <= 3 := by
            simpa only [D, RoughCanonicalGuardLocalCensusBound] using hcensus
          exact_mod_cast hcensusNat
    rw [hmOne, Nat.cast_one] at hledger
    rw [hledger]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## An assumption-free fixed guard numerator -/

/-- Uniform absolute bound used for every balanced raw coordinate after
writing the high multiplicity as `K0+1`. -/
def roughCanonicalBalancedRawWeightGuardBound
    (W K0 : Nat) (c beta : Real) : Real :=
  roughBalancedAlphaConstant W K0 c beta + |beta|

theorem roughCanonicalBalancedRawWeightGuardBound_nonneg
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 <= roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  unfold roughCanonicalBalancedRawWeightGuardBound
  exact add_nonneg
    (roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc)
    (abs_nonneg beta)

/-- The raw weight is bounded without assuming that the balanced high level
already lies in `[0,1]`. -/
theorem roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
    (W K0 n : Nat) {c beta : Real} (hc : 0 < c)
    (hn : 2 <= n) (hL : 1 <= L n) (a : Nat) :
    |roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n) a| <=
      roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  let alpha :=
    roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n)
  change
    |roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
        alpha beta (L n) a| <=
      roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have halpha :
      |alpha| <= roughBalancedAlphaConstant W K0 c beta := by
    simpa only [alpha, roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 (beta := beta) hc hn
  have hLPos : 0 < L n := zero_lt_one.trans_le hL
  have hbetaDiv : |beta / L n| <= |beta| := by
    rw [abs_div, abs_of_pos hLPos]
    apply (div_le_iff₀ hLPos).2
    nlinarith [abs_nonneg beta]
  by_cases hcop : Nat.Coprime a (roughHeadModulus W)
  · by_cases hhigh : a ∈
        roughHighLowerBlock n (upperTailLength c n) (K0 + 1)
    · have hbroad : a ∉
          roughBroadLowerBlock n (upperTailLength c n) (K0 + 1) := by
        intro hbroad
        exact Finset.disjoint_left.mp
          (roughHighLowerBlock_disjoint_roughBroadLowerBlock
            n (upperTailLength c n) (K0 + 1)) hhigh hbroad
      have hweight :
          roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
              alpha beta (L n) a = alpha := by
        simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
          hcop, hhigh, hbroad]
      rw [hweight]
      unfold roughCanonicalBalancedRawWeightGuardBound
      exact halpha.trans (le_add_of_nonneg_right (abs_nonneg beta))
    · by_cases hbroad : a ∈
          roughBroadLowerBlock n (upperTailLength c n) (K0 + 1)
      · have hweight :
            roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
                alpha beta (L n) a = beta / L n := by
          simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
            hcop, hhigh, hbroad]
        rw [hweight]
        unfold roughCanonicalBalancedRawWeightGuardBound
        exact hbetaDiv.trans
          (le_add_of_nonneg_left
            (roughBalancedAlphaConstant_nonneg W K0 (beta := beta) hc))
      · simp [roughHeadCompatibleRawWeight, roughFiniteIndicator,
          hhigh, hbroad,
          roughCanonicalBalancedRawWeightGuardBound_nonneg
            W K0 (beta := beta) hc]
  · simp [roughHeadCompatibleRawWeight, hcop,
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc]

/-- Fixed numerator constant for the assumption-free guard estimate. -/
def roughCanonicalBalancedGuardNumeratorConstant
    (W K0 : Nat) (c beta : Real) : Real :=
  1 + 3 * roughCanonicalBalancedRawWeightGuardBound W K0 c beta

theorem roughCanonicalBalancedGuardNumeratorConstant_pos
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    0 < roughCanonicalBalancedGuardNumeratorConstant W K0 c beta := by
  unfold roughCanonicalBalancedGuardNumeratorConstant
  have hbound :=
    roughCanonicalBalancedRawWeightGuardBound_nonneg
      W K0 (beta := beta) hc
  positivity

/-- With only an absolute coordinate bound `M`, the active guard ledger has
fixed size `1+3M`: one possible base token and at most three deleted
coordinates. -/
theorem roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_fixed
    {c : Real} {depth n h K label : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar M : Real) (x : Nat -> Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hM : 0 <= M)
    (hx : ∀ a ∈ completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n h K) label, |x a| <= M) :
    |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label x -
      roughCanonicalRawRowDiscrepancy n h K label x| <= 1 + 3 * M := by
  let D :=
    R.roughCanonicalGuardDeletedRow certificate deltaStar K label
  let m :=
    completeLabelMultiplicity (yNat n) R.prechargeBaseState label
  have hfixed :=
    R.paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
      deltaStar label hactive
  have hmLeNat : m <= 1 := by
    dsimp only [m]
    exact
      R.prechargeBaseState_completeLabelMultiplicity_le_one
        (label := label)
  have hmLe : (m : Real) <= 1 := by exact_mod_cast hmLeNat
  have hcensus :
      RoughCanonicalGuardLocalCensusBound R certificate deltaStar
        K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hcensusNat : D.card <= 3 := by
    simpa only [D, RoughCanonicalGuardLocalCensusBound] using hcensus
  have hcensusReal : (D.card : Real) <= 3 := by
    exact_mod_cast hcensusNat
  have hsumAbs : |∑ a ∈ D, x a| <= 3 * M := by
    calc
      |∑ a ∈ D, x a| <= ∑ a ∈ D, |x a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ _a ∈ D, M := by
        exact Finset.sum_le_sum fun a ha =>
          hx a (Finset.mem_inter.mp ha).1
      _ = (D.card : Real) * M := by simp
      _ <= 3 * M := mul_le_mul_of_nonneg_right hcensusReal hM
  have hledger :=
    R.roughCanonicalGuardLocalDiscrepancyLedger certificate deltaStar
      K label x
  rw [hfixed, Nat.cast_zero, neg_zero, zero_sub] at hledger
  rw [hledger]
  calc
    |-(m : Real) + ∑ a ∈ D, x a| <=
        |-(m : Real)| + |∑ a ∈ D, x a| := abs_add_le _ _
    _ = (m : Real) + |∑ a ∈ D, x a| := by
      rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg m)]
    _ <= 1 + 3 * M := add_le_add hmLe hsumAbs

end BankPaperRealization

/-! ## Eventual sharp raw-row estimate on every active canonical row -/

private theorem nonsmoothSlack_L_tendsto_atTop :
    Tendsto L atTop atTop := by
  simpa only [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

private theorem nonsmoothSlack_rpow_tendsto_atTop
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => (n : Real) ^ deltaStar) atTop atTop := by
  exact (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop

/-- A nontrivial intrinsic rough label is at least three once the cutoff
contains the prime two. -/
theorem isCompleteRoughLabel_three_le_of_two_le
    {y label : Nat} (hy : 2 <= y)
    (hlabel : IsCompleteRoughLabel y label) (hlabelNe : label ≠ 1) :
    3 <= label := by
  have hlabelPos : 0 < label := hlabel.1
  have hlabelNeTwo : label ≠ 2 := by
    intro htwo
    subst label
    have hfactor :
        (2 : Nat).factorization 2 ≠ 0 :=
      (Nat.prime_two.factorization_pos_of_dvd (by norm_num)
        (dvd_refl 2)).ne'
    have hhigh := hlabel.2 2 hfactor
    omega
  omega

/-- The theorem `roughCanonicalBalancedRawRowQuotaError_abs_le_unified`
with all of its paper-scale endpoint hypotheses discharged uniformly on
active rows. -/
theorem eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
    (W K0 : Nat) {c beta deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : Nat in atTop,
      forall row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)),
      BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel
          n deltaStar row.1 ->
        |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
            (K0 + 1) (yNat n)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) row| <=
          3 * (roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta *
            ((((n / row.1 : Nat) : Real)) / L n ^ 2 + 1)) := by
  have hLOne : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    nonsmoothSlack_L_tendsto_atTop.eventually (eventually_ge_atTop 1)
  have hpower : ∀ᶠ n : Nat in atTop,
      (12 : Real) <= (n : Real) ^ deltaStar :=
    (nonsmoothSlack_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop 12)
  have htailRatio : ∀ᶠ n : Nat in atTop,
      (K0 + 1 : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := by
    have hT :=
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K0 + 1 : Real)
    exact hT.eventually
      (eventually_lt_nhds (by
        simp : (K0 + 1 : Real) * 0 < 1))
  filter_upwards [
      eventually_ge_atTop 2,
      eventually_bankAnchor_fixed_le_yNat W,
      eventually_bankAnchor_fixed_le_yNat
        (roughSaiasInvLogSqEndpointCutoff
          roughSaiasSharpDefectCutoff),
      eventually_bankBottom_six_le_yNat,
      hLOne,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
      eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc,
      eventually_upperTailLength_pos hc,
      htailRatio,
      hpower]
      with n hn hWy hY hySix hLone hlogFace htailScale htailPos
        htailRatioN hpowerN
  intro row hactive
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hlabelData :=
    isCompleteRoughLabel_of_canonicalCompleteRoughRow row
  have hlabelPos : 0 < row.1 := hlabelData.1
  have hlabelThree : 3 <= row.1 :=
    isCompleteRoughLabel_three_le_of_two_le (by omega) hlabelData hactive.1
  have hlabelSmall : 6 * row.1 <= n :=
    roughCanonical_activeLabel_three_mul_le_half hnPos hlabelPos hactive.2
      hpowerN
  have hrowN : row.1 <= n := by omega
  have hKhReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <
        (n : Real) := by
    have hdiv :
        ((K0 + 1 : Real) * (upperTailLength c n : Real)) /
            (n : Real) < 1 := by
      simpa only [mul_div_assoc] using htailRatioN
    have hcross :=
      (div_lt_iff₀ hnReal).mp hdiv
    push_cast
    simpa only [one_mul] using hcross
  have hKh : (K0 + 1) * upperTailLength c n <= n := by
    exact_mod_cast hKhReal.le
  have htailLe : upperTailLength c n <= n :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < K0 + 1)).trans hKh
  have hdivLe :
      forall numerator : Nat, numerator <= 3 * n ->
        numerator / row.1 <= n := by
    intro numerator hnumerator
    calc
      numerator / row.1 <= (3 * n) / row.1 :=
        Nat.div_le_div_right hnumerator
      _ <= (3 * n) / 3 :=
        Nat.div_le_div_left (a := 3 * n) hlabelThree (by norm_num)
      _ = n := by omega
  have hdivPos :
      forall numerator : Nat, n <= numerator ->
        0 < numerator / row.1 := by
    intro numerator hnumerator
    exact Nat.div_pos (hrowN.trans hnumerator) hlabelPos
  have hendpointLe : forall i : Fin 4,
      roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i <= n := by
    intro i
    fin_cases i <;> simp [roughPhysicalNatEndpoint] <;>
      apply hdivLe <;> omega
  have hendpointPos : forall i : Fin 4,
      0 < roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i := by
    intro i
    fin_cases i
    · change 0 < (2 * n + upperTailLength c n) / row.1
      exact hdivPos _ (by omega)
    · change 0 < (2 * n) / row.1
      exact hdivPos _ (by omega)
    · change
        0 < (2 * n - (K0 + 1) * upperTailLength c n) / row.1
      exact hdivPos _ (by omega)
    · change 0 < n / row.1
      exact hdivPos _ (le_refl n)
  have hlogs : forall i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i : Real) <=
        5 * Real.log (yNat n : Real) := by
    intro i
    have hlogLe : Real.log (roughPhysicalNatEndpoint
        ((2 * n + upperTailLength c n) / row.1)
        ((2 * n) / row.1)
        ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
        (n / row.1) i : Real) <= L n := by
      unfold L
      exact Real.log_le_log
        (by exact_mod_cast hendpointPos i)
        (by exact_mod_cast hendpointLe i)
    nlinarith [hlogFace]
  apply roughCanonicalBalancedRawRowQuotaError_abs_le_unified
    W K0 (beta := beta) hc hn row hrowN hWy hY (by omega) hLone
  · nlinarith [hlogFace]
  · calc
      (upperTailLength c n : Real) <=
          2 * c * secondOrderScale n := htailScale
      _ = 2 * c * (n : Real) / L n := by
        unfold secondOrderScale L
        ring
  · exact hKh
  · exact htailPos
  · exact hlogs

namespace BankPaperRealization

/-! ## From the raw numerator to the guarded correction density -/

/-- The guarded correction density is literally the postcharge discrepancy
divided by the guarded broad-pool cardinality. -/
theorem roughCanonicalGuardedPostchargeCorrectionDensity_eq_discrepancy_div
    {c : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W K label alpha beta ell =
      R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) /
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label).card : Real) := by
  rfl

/-- The raw discrepancy notation in the guard ledger is the same quantity
as the Saias-facing quota error. -/
theorem roughCanonicalRawRowDiscrepancy_eq_quotaError
    (W n h K : Nat) (alpha beta ell : Real)
    (row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n h K)) :
    roughCanonicalRawRowDiscrepancy n h K row.1
        (roughHeadCompatibleRawWeight W n h K alpha beta ell) =
      roughCanonicalRawRowQuotaError W n h K (yNat n)
        alpha beta ell row := by
  rw [roughCanonicalRawRowDiscrepancy,
    roughCanonicalRawRowQuotaError_eq_target_sub_rawRowMass]
  rfl

/-- Assumption-free balanced postcharge numerator bound: the sharp raw
quota error plus one fixed guard constant. -/
theorem roughCanonicalBalancedPostchargeRowDiscrepancy_abs_le_raw_add_guard
    {c deltaStar beta : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hc : 0 < c) (hn : 2 <= n) (hL : 1 <= L n)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar row.1) :
    |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        (K0 + 1) row.1
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n))| <=
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n) row| +
        roughCanonicalBalancedGuardNumeratorConstant W K0 c beta := by
  let x :=
    roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
      (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n))
      beta (L n)
  let M := roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have hM : 0 <= M := by
    dsimp only [M]
    exact
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc
  have hx : ∀ a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) row.1,
      |x a| <= M := by
    intro a _ha
    dsimp only [x, M]
    exact roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
      W K0 n (beta := beta) hc hn hL a
  have hincrement :=
    R.roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_fixed
      certificate deltaStar M x hnCutoff hyCutoff hactive hM hx
  have hraw :
      roughCanonicalRawRowDiscrepancy n (upperTailLength c n) (K0 + 1)
          row.1 x =
        roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n) row := by
    dsimp only [x]
    exact roughCanonicalRawRowDiscrepancy_eq_quotaError
      W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n) row
  have htriangle :
      |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          (K0 + 1) row.1 x| <=
        |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
            (K0 + 1) row.1 x| +
          |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
              (K0 + 1) row.1 x -
            roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
              (K0 + 1) row.1 x| := by
    have hadd := abs_add_le
      (roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
        (K0 + 1) row.1 x)
      (R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          (K0 + 1) row.1 x -
        roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) row.1 x)
    convert hadd using 1; ring
  dsimp only [roughCanonicalBalancedGuardNumeratorConstant]
  have hbound :=
    htriangle.trans (add_le_add (le_refl _) hincrement)
  rw [hraw] at hbound
  exact hbound

/-- Removing at most three guarded coordinates from a raw pool of density
`d` retains half of that linear density as soon as `d*X >= 6`. -/
theorem roughCanonicalGuardedBroadCorrectionPool_linear_half_lower
    {c deltaStar d : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hraw :
      d * ((n / label : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card)
    (hsix : 6 <= d * ((n / label : Nat) : Real)) :
    d / 2 * ((n / label : Nat) : Real) <=
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card := by
  let rawPool :=
    roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
      (yNat n) label
  let guard := R.roughCanonicalGuardSet certificate deltaStar
  have hinterSubset :
      guard ∩ rawPool ⊆
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label := by
    intro a ha
    have haData := Finset.mem_inter.mp ha
    exact Finset.mem_inter.mpr
      ⟨roughCanonicalBroadCorrectionPool_subset_rawRow
        W n (upperTailLength c n) K (yNat n) label haData.2,
        haData.1⟩
  have hcensus :
      RoughCanonicalGuardLocalCensusBound R certificate deltaStar
        K label 3 :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  have hinterNat : (guard ∩ rawPool).card <= 3 :=
    (Finset.card_le_card hinterSubset).trans hcensus
  have hinter : ((guard ∩ rawPool).card : Real) <= 3 := by
    exact_mod_cast hinterNat
  have hinterRight : (guard ∩ rawPool).card <= rawPool.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hcard :
      ((rawPool \ guard).card : Real) =
        (rawPool.card : Real) - ((guard ∩ rawPool).card : Real) := by
    rw [Finset.card_sdiff, Nat.cast_sub hinterRight]
  change
    d / 2 * ((n / label : Nat) : Real) <=
      ((rawPool \ guard).card : Real)
  rw [hcard]
  have hraw' :
      d * ((n / label : Nat) : Real) <= (rawPool.card : Real) := by
    simpa only [rawPool] using hraw
  linarith

/-- Pointwise analytic conversion from a unified raw-row numerator and a
linear raw broad-pool lower bound to the active reserve `betaAct/L`. -/
theorem roughCanonicalBalancedGuardedPostchargeCorrectionDensity_abs_le_reserve
    {c deltaStar beta betaAct C d G : Real}
    {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hc : 0 < c) (hn : 2 <= n) (hLone : 1 <= L n)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar row.1)
    (hd : 0 < d) (hbetaAct : 0 < betaAct)
    (_hC : 0 <= C)
    (hG :
      G = roughCanonicalBalancedGuardNumeratorConstant W K0 c beta)
    (hrawQuota :
      |roughCanonicalRawRowQuotaError W n (upperTailLength c n)
          (K0 + 1) (yNat n)
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n) row| <=
        3 * (C *
          ((((n / row.1 : Nat) : Real)) / L n ^ 2 + 1)))
    (hrawPool :
      d * ((n / row.1 : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n)
          (K0 + 1) (yNat n) row.1).card)
    (hsix : 6 <= d * ((n / row.1 : Nat) : Real))
    (hfirst : 12 * C <= d * betaAct * L n)
    (hsecond :
      4 * (3 * C + G) * L n <=
        d * betaAct * ((n / row.1 : Nat) : Real)) :
    |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W (K0 + 1) row.1
        (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n))
        beta (L n)| <= betaAct / L n := by
  let X : Real := ((n / row.1 : Nat) : Real)
  let pool :=
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W (K0 + 1) row.1
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hX : 0 < X := by
    by_contra hnot
    have hXle : X <= 0 := le_of_not_gt hnot
    have hdXle : d * X <= 0 :=
      mul_nonpos_of_nonneg_of_nonpos hd.le hXle
    dsimp only [X] at hsix hdXle
    linarith
  have hpoolLower :
      d / 2 * X <= (pool.card : Real) := by
    dsimp only [pool, X]
    exact R.roughCanonicalGuardedBroadCorrectionPool_linear_half_lower
      certificate hnCutoff hyCutoff hactive hrawPool hsix
  have hpoolPos : (0 : Real) < (pool.card : Real) :=
    (mul_pos (div_pos hd (by norm_num)) hX).trans_le hpoolLower
  have hpost :
      |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          (K0 + 1) row.1
          (roughHeadCompatibleRawWeight W n (upperTailLength c n)
            (K0 + 1)
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n))
            beta (L n))| <=
        3 * (C * (X / L n ^ 2 + 1)) + G := by
    have hguard :=
      R.roughCanonicalBalancedPostchargeRowDiscrepancy_abs_le_raw_add_guard
        (W := W) (beta := beta)
        certificate row hc hn hLone hnCutoff hyCutoff hactive
    rw [← hG] at hguard
    exact hguard.trans (add_le_add (by
      simpa only [X] using hrawQuota) (le_refl G))
  have hmain :
      3 * C * (X / L n ^ 2) <=
        betaAct / L n * (d / 4 * X) := by
    have hfactor : 0 <= X / (4 * L n ^ 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hfirst hfactor
    calc
      3 * C * (X / L n ^ 2) =
          (12 * C) * (X / (4 * L n ^ 2)) := by ring
      _ <= (d * betaAct * L n) * (X / (4 * L n ^ 2)) := hmul
      _ = betaAct / L n * (d / 4 * X) := by
        field_simp [hL.ne']
  have hconstant :
      3 * C + G <= betaAct / L n * (d / 4 * X) := by
    have hden : 0 < 4 * L n := mul_pos (by norm_num) hL
    rw [show betaAct / L n * (d / 4 * X) =
        (d * betaAct * X) / (4 * L n) by
      field_simp [hL.ne']]
    apply (le_div_iff₀ hden).2
    convert hsecond using 1; ring
  have hnumerator :
      3 * (C * (X / L n ^ 2 + 1)) + G <=
        betaAct / L n * (d / 2 * X) := by
    calc
      3 * (C * (X / L n ^ 2 + 1)) + G =
          3 * C * (X / L n ^ 2) + (3 * C + G) := by ring
      _ <= betaAct / L n * (d / 4 * X) +
          betaAct / L n * (d / 4 * X) :=
        add_le_add hmain hconstant
      _ = betaAct / L n * (d / 2 * X) := by ring
  rw [
    R.roughCanonicalGuardedPostchargeCorrectionDensity_eq_discrepancy_div
      (W := W) (K := K0 + 1) (label := row.1) certificate,
    abs_div, abs_of_pos hpoolPos]
  apply (div_le_iff₀ hpoolPos).2
  exact hpost.trans <| hnumerator.trans <|
    mul_le_mul_of_nonneg_left hpoolLower
      (div_nonneg hbetaAct.le hL.le)

/-! ## The eventual paper beta/sigma nonsmooth bounds -/

/-- Exact nonsmooth-bounds package consumed by the actual endpoint-slack
producer, specialized to the balanced raw level and the paper split
`betaProt + betaAct`. -/
def RoughCanonicalBalancedNonsmoothBounds
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K0 : Nat)
    (betaProt betaAct sigma : Real) : Prop :=
  forall label,
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      sigma / L n +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              (betaProt + betaAct) (L n))
            (betaProt + betaAct) (L n)| <=
        (betaProt + betaAct) / L n ∧
      (betaProt + betaAct) / L n +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              (betaProt + betaAct) (L n))
            (betaProt + betaAct) (L n)| <=
        1 - sigma / L n

/-- Exact numerical content forced by any proposed nonsmooth two-sided
bound.  These are the failure inequalities to inspect if a different
choice of `beta` and `sigma` is supplied:

`ell * |correction| <= beta - sigma` and
`ell * |correction| <= ell - beta - sigma`.
-/
theorem nonsmoothEndpointBounds_force_margin_inequalities
    {ell sigma beta correction : Real} (hell : 0 < ell)
    (hfloor : sigma / ell + |correction| <= beta / ell)
    (hceiling :
      beta / ell + |correction| <= 1 - sigma / ell) :
    ell * |correction| <= beta - sigma ∧
      ell * |correction| <= ell - beta - sigma := by
  have hfloorDiv :
      |correction| <= (beta - sigma) / ell := by
    have : |correction| <= beta / ell - sigma / ell := by linarith
    convert this using 1; ring
  have hceilingDiv :
      |correction| <= (ell - beta - sigma) / ell := by
    have hone : (1 : Real) = ell / ell := by
      exact (div_self hell.ne').symm
    rw [hone] at hceiling
    have :
        |correction| <= ell / ell - beta / ell - sigma / ell := by
      linarith
    convert this using 1; ring
  constructor
  · have := (le_div_iff₀ hell).mp hfloorDiv
    nlinarith
  · have := (le_div_iff₀ hell).mp hceilingDiv
    nlinarith

/-- In particular, a nonzero correction is impossible if `beta <= sigma`;
this is the precise lower-margin obstruction. -/
theorem nonsmoothEndpointBounds_impossible_of_beta_le_sigma
    {ell sigma beta correction : Real} (hell : 0 < ell)
    (hcorrection : correction ≠ 0) (hbetaSigma : beta <= sigma) :
    ¬ (sigma / ell + |correction| <= beta / ell ∧
      beta / ell + |correction| <= 1 - sigma / ell) := by
  rintro ⟨hfloor, hceiling⟩
  have hmargin :=
    nonsmoothEndpointBounds_force_margin_inequalities hell hfloor hceiling
  have hpositive : 0 < ell * |correction| :=
    mul_pos hell (abs_pos.mpr hcorrection)
  linarith

private theorem nonsmoothSlack_L_div_rpow_tendsto_zero
    {deltaStar : Real} (hdelta : 0 < deltaStar) :
    Tendsto (fun n : Nat => L n / (n : Real) ^ deltaStar)
      atTop (nhds 0) := by
  have hreal : Tendsto
      (fun x : Real =>
        Real.log x ^ (1 : Real) / x ^ deltaStar)
      atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : Real) hdelta).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]

/-- The balanced nonsmooth correction has the exact two-sided endpoint
slack required by the actual Proposition 8.7 producer, eventually and
uniformly in the realized bank, guard certificate, and active label.

No alpha-box hypothesis is used.  The finite guards are paid for by the
fixed absolute balanced-weight bound above. -/
theorem eventually_roughCanonicalBalancedNonsmoothBounds
    (W K0 : Nat)
    {c deltaStar betaProt betaAct sigma : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hbetaAct : 0 < betaAct) (hsigma : sigma <= betaProt) :
    ∀ᶠ n : Nat in atTop,
      forall (depth : Nat)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
      centralAnchorCutoffThreshold depth <= n ->
      yNat n < centralAnchorCutoff depth n ->
        RoughCanonicalBalancedNonsmoothBounds R certificate deltaStar
          W K0 betaProt betaAct sigma := by
  let beta := betaProt + betaAct
  let d := roughCanonicalRawBroadPoolDensity W
  let C := roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta
  let G := roughCanonicalBalancedGuardNumeratorConstant W K0 c beta
  let A := 16 * (3 * C + G)
  have hd : 0 < d := by
    dsimp only [d]
    exact roughCanonicalRawBroadPoolDensity_pos W
  have hC : 0 <= C := by
    dsimp only [C]
    exact
      roughCanonicalSharpUnifiedRowScaleConstant_nonneg
        W K0 (beta := beta) hc
  have hG : 0 < G := by
    dsimp only [G, beta]
    exact
      roughCanonicalBalancedGuardNumeratorConstant_pos
        W K0 (beta := betaProt + betaAct) hc
  have hA : 0 < A := by
    dsimp only [A]
    have : 0 < 3 * C + G := by positivity
    positivity
  have hdBeta : 0 < d * betaAct := mul_pos hd hbetaAct
  have hraw :=
    Erdos390.WholePaper.eventually_roughCanonicalBalancedRawRowQuotaError_abs_le_unified_active
      W K0 (beta := beta) hc hdelta
  have hlinear :=
    eventually_roughCanonical_activeRawBroadPool_linear_lower
      W (K0 + 1) hc hdelta
  let Lthreshold :=
    max 1
      (max (12 * C / (d * betaAct))
        (betaProt + 2 * betaAct + sigma))
  have hLlarge : ∀ᶠ n : Nat in atTop, Lthreshold <= L n :=
    nonsmoothSlack_L_tendsto_atTop.eventually
      (eventually_ge_atTop Lthreshold)
  let powerThreshold : Real := max 4 (24 / d)
  have hpower : ∀ᶠ n : Nat in atTop,
      powerThreshold <= (n : Real) ^ deltaStar :=
    (nonsmoothSlack_rpow_tendsto_atTop hdelta).eventually
      (eventually_ge_atTop powerThreshold)
  have hratioZero :=
    nonsmoothSlack_L_div_rpow_tendsto_zero hdelta
  have hratioSmall : ∀ᶠ n : Nat in atTop,
      A * L n <= d * betaAct * (n : Real) ^ deltaStar := by
    have hepsilon : 0 < d * betaAct / A :=
      div_pos hdBeta hA
    have hsmall :=
      hratioZero.eventually (eventually_lt_nhds hepsilon)
    filter_upwards [hsmall, eventually_gt_atTop 1] with n hsmallN hn
    have hnReal : (0 : Real) < n := by exact_mod_cast (show 0 < n by omega)
    have hpowPos : (0 : Real) < (n : Real) ^ deltaStar :=
      Real.rpow_pos_of_pos hnReal deltaStar
    have hcross :
        L n < (d * betaAct / A) * (n : Real) ^ deltaStar :=
      (div_lt_iff₀ hpowPos).mp hsmallN
    have hcross' :
        L n <
          (d * betaAct * (n : Real) ^ deltaStar) / A := by
      calc
        L n < (d * betaAct / A) * (n : Real) ^ deltaStar := hcross
        _ = (d * betaAct * (n : Real) ^ deltaStar) / A := by ring
    have hcross'' := ((lt_div_iff₀ hA).mp hcross').le
    simpa only [mul_comm] using hcross''
  filter_upwards [eventually_ge_atTop 2, hraw, hlinear, hLlarge,
      hpower, hratioSmall]
      with n hn hrawN hlinearN hLlargeN hpowerN hratioN
  have hLone : 1 <= L n :=
    (le_max_left 1
      (max (12 * C / (d * betaAct))
        (betaProt + 2 * betaAct + sigma))).trans hLlargeN
  have hL : 0 < L n := zero_lt_one.trans_le hLone
  have hfirstThreshold :
      12 * C / (d * betaAct) <= L n :=
    (le_max_left (12 * C / (d * betaAct))
      (betaProt + 2 * betaAct + sigma)).trans
        ((le_max_right 1 _).trans hLlargeN)
  have hfirst : 12 * C <= d * betaAct * L n := by
    have hcross := (div_le_iff₀ hdBeta).mp hfirstThreshold
    nlinarith
  have hparameterLarge :
      betaProt + 2 * betaAct + sigma <= L n :=
    (le_max_right (12 * C / (d * betaAct))
      (betaProt + 2 * betaAct + sigma)).trans
        ((le_max_right 1 _).trans hLlargeN)
  have hpowerFour : (4 : Real) <= (n : Real) ^ deltaStar :=
    (le_max_left 4 (24 / d)).trans hpowerN
  have hpowerDensity : 24 / d <= (n : Real) ^ deltaStar :=
    (le_max_right 4 (24 / d)).trans hpowerN
  intro depth R certificate hnCutoff hyCutoff
  unfold RoughCanonicalBalancedNonsmoothBounds
  intro label hactive
  let pool :=
    R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W (K0 + 1) label
  have hdensity :
      |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
          deltaStar W (K0 + 1) label
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
            beta (L n))
          beta (L n)| <= betaAct / L n := by
    by_cases hpool : pool.Nonempty
    · obtain ⟨a, haPool⟩ := hpool
      have haRawPool :
          a ∈ roughCanonicalBroadCorrectionPool W n
            (upperTailLength c n) (K0 + 1) (yNat n) label :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar W (K0 + 1) label haPool
      have haRawRow :=
        roughCanonicalBroadCorrectionPool_subset_rawRow W n
          (upperTailLength c n) (K0 + 1) (yNat n) label haRawPool
      let row : CanonicalCompleteRoughRow (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
        ⟨label, mem_completeRoughLabelSet.mpr
          ⟨a, (mem_completeRoughRowFiber.mp haRawRow).1,
            (mem_completeRoughRowFiber.mp haRawRow).2⟩⟩
      have hlabelData :
          IsCompleteRoughLabel (yNat n) label := by
        simpa only [row] using
          isCompleteRoughLabel_of_canonicalCompleteRoughRow row
      have hlabelPos : 0 < label := hlabelData.1
      have hnPos : 0 < n := by omega
      have hnReal : (0 : Real) < n := by exact_mod_cast hnPos
      have hlabelReal : (0 : Real) < label := by
        exact_mod_cast hlabelPos
      let X : Real := ((n / label : Nat) : Real)
      have hnatUpper :
          (n : Real) / (label : Real) < X + 1 := by
        apply (div_lt_iff₀ hlabelReal).2
        have hnat := (Nat.div_lt_iff_lt_mul hlabelPos).mp
          (Nat.lt_succ_self (n / label))
        dsimp only [X]
        exact_mod_cast hnat
      have hactiveHalf :
          (n : Real) ^ deltaStar / 2 <=
            (n : Real) / (label : Real) := by
        calc
          (n : Real) ^ deltaStar / 2 <=
              (2 * (n : Real) / (label : Real)) / 2 :=
            div_le_div_of_nonneg_right hactive.2 (by norm_num)
          _ = (n : Real) / (label : Real) := by ring
      have hXlower :
          (n : Real) ^ deltaStar / 4 <= X := by
        have hhalfFour :
            (n : Real) ^ deltaStar / 4 <=
              (n : Real) ^ deltaStar / 2 - 1 := by
          linarith [hpowerFour]
        linarith
      have hsix :
          6 <= d * X := by
        have hcross := (div_le_iff₀ hd).mp hpowerDensity
        have hmul :=
          mul_le_mul_of_nonneg_left hXlower hd.le
        nlinarith
      have hsecond :
          4 * (3 * C + G) * L n <= d * betaAct * X := by
        have hpowX :
            (n : Real) ^ deltaStar <= 4 * X := by
          linarith [hXlower]
        have hmul :=
          mul_le_mul_of_nonneg_left hpowX hdBeta.le
        dsimp only [A] at hratioN
        nlinarith
      have hrawPool :
          d * X <=
            (roughCanonicalBroadCorrectionPool W n
              (upperTailLength c n) (K0 + 1) (yNat n) label).card := by
        dsimp only [d, X]
        exact hlinearN label hlabelData hactive
      have hrawQuota := hrawN row (by simpa only [row] using hactive)
      have hdensityRow :=
        R.roughCanonicalBalancedGuardedPostchargeCorrectionDensity_abs_le_reserve
          certificate row hc hn hLone hnCutoff hyCutoff
          (by simpa only [row] using hactive)
          hd hbetaAct hC (by rfl) hrawQuota
          (by simpa only [X] using hrawPool)
          (by simpa only [X] using hsix)
          hfirst (by simpa only [row, X] using hsecond)
      simpa only [row, beta] using hdensityRow
    · have hpoolEmpty : pool = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hpool
      have hcardZero : pool.card = 0 := by rw [hpoolEmpty]; simp
      rw [
        R.roughCanonicalGuardedPostchargeCorrectionDensity_eq_discrepancy_div
          (W := W) (K := K0 + 1) (label := label) certificate]
      change
        |R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
            (K0 + 1) label
            (roughHeadCompatibleRawWeight W n (upperTailLength c n)
              (K0 + 1)
              (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
                beta (L n))
              beta (L n)) / (pool.card : Real)| <= betaAct / L n
      rw [hcardZero, Nat.cast_zero, div_zero, abs_zero]
      exact div_nonneg hbetaAct.le hL.le
  constructor
  · calc
      sigma / L n +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n))
            beta (L n)| <=
        betaProt / L n + betaAct / L n :=
          add_le_add
            (div_le_div_of_nonneg_right hsigma hL.le) hdensity
      _ = beta / L n := by
        dsimp only [beta]
        ring
  · have hdiv :
        (betaProt + 2 * betaAct + sigma) / L n <= 1 := by
      have h :=
        div_le_div_of_nonneg_right hparameterLarge hL.le
      simpa only [div_self hL.ne'] using h
    calc
      beta / L n +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W (K0 + 1) label
            (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n))
            beta (L n)| <=
        beta / L n + betaAct / L n :=
          add_le_add le_rfl hdensity
      _ = (betaProt + 2 * betaAct + sigma) / L n - sigma / L n := by
        dsimp only [beta]
        ring
      _ <= 1 - sigma / L n := sub_le_sub_right hdiv _

/-- Direct handoff to the `hnonsmoothBounds` argument of
`bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve`.
The only conversion is the definitional identity `B.L = Scale.L n`. -/
theorem RoughCanonicalBalancedNonsmoothBounds.to_actualEndpointBounds
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (betaProt betaAct sigma : Real)
    (H : RoughCanonicalBalancedNonsmoothBounds R certificate deltaStar
      B.sampleData.W K0 betaProt betaAct sigma) :
    forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n
          deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W (K0 + 1) label
              (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
                (upperTailLength c B.sampleData.n) (K0 + 1)
                (betaProt + betaAct) B.L)
              (betaProt + betaAct) B.L| <=
          (betaProt + betaAct) / B.L ∧
        (betaProt + betaAct) / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W (K0 + 1) label
              (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
                (upperTailLength c B.sampleData.n) (K0 + 1)
                (betaProt + betaAct) B.L)
              (betaProt + betaAct) B.L| <=
          1 - sigma / B.L := by
  intro label hactive
  have hbounds := H label hactive
  simpa only [Erdos390.Full.PaperBridgeFit.BridgeData.L,
    Erdos390.Full.Scale.L] using hbounds

end BankPaperRealization

end

end Erdos390.WholePaper
