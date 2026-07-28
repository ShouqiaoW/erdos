import Erdos390.WholePaper.BankPaperCanonicalSectionEightTopFrozenSourceConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector
import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure

/-!
# Initial selector mass from the frozen-top smooth-row bridge

This connector is the asymptotic integration boundary for the separate
`qTilde`-stage source constructed in
`BankPaperCanonicalSectionEightTopFrozenSourceConnector`.

The family-facing premise below is an exact construction equation:
the initial selector has the same guarded label-one row sum as the balanced
literal raw selector.  Together with the existing exact nonsmooth-row state,
the charged row ledger reduces the whole selector-mass error to:

* the balanced raw label-one discrepancy;
* the two charged label-one multiplicities; and
* the balanced raw mass deleted by the numerical guard.

The first term is handled by the sharp Saias row theorem.  Fixed exceptional
factors and bank bases have zero label-one multiplicity in the paper range.
The remaining deleted row is contained in the promoted smooth residual
anchors, hence has cardinality at most `yNat`; the existing uniform balanced
raw-weight bound then absorbs it into `secondOrderScale / L`.

No final-selector quota, height displacement, or Section 9 source state is
used here.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The balanced raw selector used by the initial-mass interface -/

/-- The literal balanced raw weight with high multiplicity `K0 + 1`. -/
def bankPaperCanonicalBalancedRawWeight
    (W K0 : Nat) (c beta : Real) (n a : Nat) : Real :=
  roughHeadCompatibleRawWeight W n (upperTailLength c n) (K0 + 1)
    (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n))
    beta (L n) a

/-! ## The two charged smooth-row multiplicities -/

/-- For `deltaStar <= 1`, no fixed exceptional upper factor can have
complete rough label one: its defining strict inequality would say
`2n < n^deltaStar <= n`. -/
theorem paperFixedExceptionalFactors_completeLabelMultiplicity_one_eq_zero
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    {deltaStar : Real} (hn : 0 < n) (hdeltaUpper : deltaStar <= 1) :
    completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) 1 = 0 := by
  unfold completeLabelMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a haFixed haLabel
  have haData := (R.mem_paperFixedExceptionalFactors (a := a)).mp haFixed
  have hexceptional :
      2 * (n : Real) < (n : Real) ^ deltaStar := by
    simpa only [haLabel, Nat.cast_one, div_one] using haData.2.1
  have hnOne : (1 : Real) <= (n : Real) := by
    exact_mod_cast (show 1 <= n by omega)
  have hpower :
      (n : Real) ^ deltaStar <= (n : Real) :=
    Real.rpow_le_self_of_one_le hnOne hdeltaUpper
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hn
  nlinarith

/-- Every precharge base retains its marker prime above `yNat`, so the bank
base state has no complete-label-one coordinate. -/
theorem prechargeBaseState_completeLabelMultiplicity_one_eq_zero
    {n M : Nat} (R : BankPaperRealization n M) :
    completeLabelMultiplicity (yNat n) R.prechargeBaseState 1 = 0 := by
  classical
  unfold completeLabelMultiplicity
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro a haBase haLabel
  rw [BankPaperRealization.prechargeBaseState, indexedPathState,
    Finset.mem_image] at haBase
  obtain ⟨request, _hrequest, rfl⟩ := haBase
  rw [R.prechargeBase_completeRoughLabel_eq_marker] at haLabel
  have hmarker := R.yNat_lt_paperMarker request
  have hy := R.six_le_yNat
  omega

/-! ## Full label-one guard deletion -/

/-- On the full raw label-one row, every deleted coordinate is a central
anchor.  Precharge bases and alternates retain a nontrivial marker label. -/
theorem roughCanonicalGuardDeletedSmoothRow_subset_anchors
    {c : Real} {depth n h K : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) :
    R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 ⊆
      certificate.anchors := by
  classical
  intro a ha
  have haRawRow := (Finset.mem_inter.mp ha).1
  have haSupport :=
    R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
      certificate deltaStar K 1 ha
  rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
  · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
    · exact haAnchor
    · rw [BankPaperRealization.prechargeBaseState, indexedPathState,
        Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at hlabel
      have hmarker := R.yNat_lt_paperMarker request
      have hy := R.six_le_yNat
      omega
  · rw [BankPaperRealization.prechargeAlternateState, indexedPathState,
      Finset.mem_image] at haAlternate
    obtain ⟨request, _hrequest, rfl⟩ := haAlternate
    have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
    rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at hlabel
    have hmarker := R.yNat_lt_paperMarker request
    have hy := R.six_le_yNat
    omega

/-- Every central anchor in the full raw label-one row is a promoted
residual anchor whose base prime is at most `yNat`.  This is the full-row
version of the existing broad-base support theorem. -/
theorem guardedCentralAnchors_inter_rawSmoothRow_subset_smoothResidual
    {c : Real} {depth n h K : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    certificate.anchors ∩
        completeRoughRowFiber (yNat n) (roughRawCandidateSet n h K) 1 ⊆
      bankPaperCanonicalSmoothResidualAnchorPool n
        (centralAnchorCutoff depth n) (yNat n) := by
  intro a ha
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  have haRawRow := (Finset.mem_inter.mp ha).2
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRawRow).2
  have haAnchor : a ∈ fullCentralAnchors n
      (centralAnchorCutoff depth n) certificate.q := by
    simpa only [certificate.anchors_eq] using
      (Finset.mem_inter.mp ha).1
  rw [fullCentralAnchors] at haAnchor
  rcases Finset.mem_union.mp haAnchor with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hyp : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel : p ∣
        completeRoughLabel (yNat n) (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hyp
        (Nat.zero_lt_of_lt (promotedCentralFactor_gt hn)).ne'
        hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPPos : 0 < largeCentralAnchor certificate.q P :=
      Nat.zero_lt_of_lt
        (Finset.mem_Ioc.mp
          (largeCentralAnchor_mem_centralInterval
            certificate.isCofactorChoice hP)).1
    have hPDvdLabel : P ∣
        completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        hPPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim

/-- The full raw label-one deletion set contains at most `yNat n`
coordinates. -/
theorem roughCanonicalGuardDeletedSmoothRow_card_le_yNat
    {c : Real} {depth n h K : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K 1).card <=
      yNat n := by
  have hsubset :
      R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 ⊆
        certificate.anchors ∩
          completeRoughRowFiber (yNat n)
            (roughRawCandidateSet n h K) 1 := by
    intro a ha
    exact Finset.mem_inter.mpr
      ⟨R.roughCanonicalGuardDeletedSmoothRow_subset_anchors
          certificate deltaStar ha,
        (Finset.mem_inter.mp ha).1⟩
  calc
    (R.roughCanonicalGuardDeletedRow certificate deltaStar K 1).card <=
        (certificate.anchors ∩
          completeRoughRowFiber (yNat n)
            (roughRawCandidateSet n h K) 1).card :=
      Finset.card_le_card hsubset
    _ <=
        (bankPaperCanonicalSmoothResidualAnchorPool n
          (centralAnchorCutoff depth n) (yNat n)).card :=
      Finset.card_le_card
        (guardedCentralAnchors_inter_rawSmoothRow_subset_smoothResidual
          certificate hnCutoff hyCutoff)
    _ <= yNat n :=
      bankPaperCanonicalSmoothResidualAnchorPool_card_le n
        (centralAnchorCutoff depth n) (yNat n)

/-- The deleted balanced raw mass is bounded by the smooth-anchor count
times the existing realization-independent raw-coordinate bound. -/
theorem abs_sum_roughCanonicalGuardDeletedSmoothRow_balancedRawWeight_le
    {c deltaStar beta : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hc : 0 < c) (hn : 2 <= n) (hL : 1 <= L n)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    |∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
        (K0 + 1) 1,
      bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
      (yNat n : Real) *
        roughCanonicalBalancedRawWeightGuardBound W K0 c beta := by
  let D :=
    R.roughCanonicalGuardDeletedRow certificate deltaStar (K0 + 1) 1
  let M := roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have hM : 0 <= M := by
    dsimp only [M]
    exact
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc
  have hcardNat : D.card <= yNat n := by
    dsimp only [D]
    exact R.roughCanonicalGuardDeletedSmoothRow_card_le_yNat
      certificate deltaStar hnCutoff hyCutoff
  have hcardReal : (D.card : Real) <= (yNat n : Real) := by
    exact_mod_cast hcardNat
  calc
    |∑ a ∈ D, bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
        ∑ a ∈ D,
          |bankPaperCanonicalBalancedRawWeight W K0 c beta n a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ _a ∈ D, M := by
      exact Finset.sum_le_sum fun a _ha => by
        dsimp only [bankPaperCanonicalBalancedRawWeight, M]
        exact roughHeadCompatibleBalancedRawWeight_abs_le_guardBound
          W K0 n (beta := beta) hc hn hL a
    _ = (D.card : Real) * M := by simp
    _ <= (yNat n : Real) * M :=
      mul_le_mul_of_nonneg_right hcardReal hM

/-! ## Paper-scale bounds for the smooth row -/

private theorem topFrozenInitialMass_L_tendsto_atTop :
    Tendsto L atTop atTop := by
  simpa only [L] using
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Eventually the logarithm of every possible label-one quotient endpoint
(which is at most `3n`) lies in the five-log-`yNat` analytic chamber. -/
theorem eventually_log_three_mul_natCast_le_five_log_yNat :
    ∀ᶠ n : Nat in atTop,
      Real.log (3 * (n : Real)) <=
        5 * Real.log (yNat n : Real) := by
  have hLlarge : ∀ᶠ n : Nat in atTop,
      9 * Real.log 3 + 45 * Real.log 2 <= L n :=
    topFrozenInitialMass_L_tendsto_atTop.eventually
      (eventually_ge_atTop
        (9 * Real.log 3 + 45 * Real.log 2))
  filter_upwards [eventually_gt_atTop 0,
      eventually_bankBottom_six_le_yNat, hLlarge]
      with n hn hySix hLlargeN
  have hyPos : 0 < y n := y_pos hn
  have hyFloor : (yNat n : Real) <= y n :=
    Nat.floor_le hyPos.le
  have hyRealTwo : (2 : Real) <= y n := by
    exact
      (by exact_mod_cast (show 2 <= yNat n by omega) :
        (2 : Real) <= (yNat n : Real)).trans hyFloor
  have hyNatLower : y n / 2 <= (yNat n : Real) := by
    have hfloor : y n < (yNat n : Real) + 1 :=
      Nat.lt_floor_add_one _
    linarith
  have hlogLower :
      Real.log (y n / 2) <= Real.log (yNat n : Real) :=
    Real.log_le_log (div_pos hyPos (by norm_num)) hyNatLower
  have hlogDiv :
      Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hyPos.ne' (by norm_num : (2 : Real) ≠ 0)]
  calc
    Real.log (3 * (n : Real)) = Real.log 3 + L n := by
      rw [Real.log_mul (by norm_num : (3 : Real) ≠ 0)
        (by exact_mod_cast hn.ne')]
      rfl
    _ <= 5 * Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      nlinarith
    _ <= 5 * Real.log (yNat n : Real) := by
      gcongr

/-- The smooth anchor count is eventually bounded pointwise by the exact
initial-mass error scale `secondOrderScale / L`. -/
theorem eventually_yNat_cast_le_secondOrderScale_div_L :
    ∀ᶠ n : Nat in atTop,
      (yNat n : Real) <= secondOrderScale n / L n := by
  have hratio := tendsto_endpointRatio_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hratio, eventually_ge_atTop 2,
      eventually_bankBottom_six_le_yNat] with n hratioN hn hySix
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < n := by exact_mod_cast hnPos
  have hL : 0 < L n := L_pos hn
  have hyNonneg : 0 <= y n := (y_pos hnPos).le
  have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hyNonneg
  have hySq : (yNat n : Real) ^ 2 <= y n ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hyNonneg).2 hyFloor
  have hratioNat :
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <= 1 := by
    calc
      (yNat n : Real) ^ 2 * L n ^ 2 / (n : Real) <=
          y n ^ 2 * L n ^ 2 / (n : Real) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hySq (sq_nonneg _)) hnReal.le
      _ = endpointRatio n := by rfl
      _ <= 1 := hratioN.le
  have hySqScale :
      (yNat n : Real) ^ 2 <= (n : Real) / L n ^ 2 := by
    apply (le_div_iff₀ (pow_pos hL 2)).2
    have hcross := (div_le_iff₀ hnReal).1 hratioNat
    simpa only [one_mul] using hcross
  have hyLeSq :
      (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    have hyOne : (1 : Real) <= (yNat n : Real) := by
      exact_mod_cast (show 1 <= yNat n by omega)
    nlinarith [sq_nonneg ((yNat n : Real) - 1)]
  have htarget :
      (n : Real) / L n ^ 2 = secondOrderScale n / L n := by
    unfold secondOrderScale L
    ring
  exact hyLeSq.trans (hySqScale.trans_eq htarget)

/-- Big-O form of the preceding pointwise estimate. -/
theorem bankPaperCanonical_yNat_isBigO_secondOrderScale_div_L :
    (fun n : Nat => (yNat n : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_yNat_cast_le_secondOrderScale_div_L,
      eventually_gt_atTop 1] with n hy hn
  have htarget : 0 < secondOrderScale n / L n :=
    div_pos (secondOrderScale_pos (by omega)) (L_pos hn)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_pos htarget, one_mul]
  exact hy

/-- The balanced raw complete-label-one discrepancy is already at the
required `N / L = secondOrderScale / L` scale. -/
theorem bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO
    (W K0 : Nat) {c beta : Real} (hc : 0 < c) :
    (fun n =>
      roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
        (K0 + 1) 1
          (bankPaperCanonicalBalancedRawWeight W K0 c beta n)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  let C := roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta
  have hC : 0 <= C := by
    dsimp only [C]
    exact
      roughCanonicalSharpUnifiedRowScaleConstant_nonneg
        W K0 (beta := beta) hc
  have hLOne : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    topFrozenInitialMass_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  have htailRatio : ∀ᶠ n : Nat in atTop,
      (K0 + 1 : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := by
    have hT :=
      (upperTailLength_ratio_tendsto_zero hc).const_mul
        (K0 + 1 : Real)
    exact hT.eventually
      (eventually_lt_nhds (by
        simp : (K0 + 1 : Real) * 0 < 1))
  have htargetOne : ∀ᶠ n : Nat in atTop,
      (1 : Real) <= secondOrderScale n / L n :=
    secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  apply IsBigO.of_bound (6 * C)
  filter_upwards [
      eventually_ge_atTop 2,
      eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower
        W (K0 + 1) hc,
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
      eventually_log_three_mul_natCast_le_five_log_yNat,
      htargetOne]
      with n hn hpool hWy hY hySix hLone hlogFace htailScale
        htailPos htailRatioN hlogThree htargetOneN
  have hnPos : 0 < n := by omega
  have hnReal : (0 : Real) < (n : Real) := by exact_mod_cast hnPos
  have hpoolPos :
      0 < ((bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) (K0 + 1)).card : Real) := by
    exact
      (mul_pos (roughCanonicalRawBroadPoolDensity_pos W) hnReal).trans_le
        hpool
  have hpoolNonempty :
      (bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) (K0 + 1)).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hpoolPos
  have hrowNonempty :
      (completeRoughRowFiber (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1))
          1).Nonempty := by
    obtain ⟨a, ha⟩ := hpoolNonempty
    refine ⟨a, ?_⟩
    exact roughCanonicalBroadCorrectionPool_subset_rawRow
      W n (upperTailLength c n) (K0 + 1) (yNat n) 1 ha
  have hrowMem :
      1 ∈ completeRoughLabelSet (yNat n)
        (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
    mem_completeRoughLabelSet_iff_rowFiber_nonempty.mpr hrowNonempty
  let row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)) :=
    ⟨1, hrowMem⟩
  have hKhReal :
      (((K0 + 1) * upperTailLength c n : Nat) : Real) <
        (n : Real) := by
    have hdiv :
        ((K0 + 1 : Real) * (upperTailLength c n : Real)) /
            (n : Real) < 1 := by
      simpa only [mul_div_assoc] using htailRatioN
    have hcross := (div_lt_iff₀ hnReal).mp hdiv
    push_cast
    simpa only [one_mul] using hcross
  have hKh :
      (K0 + 1) * upperTailLength c n <= n := by
    exact_mod_cast hKhReal.le
  have htailLe : upperTailLength c n <= n :=
    (Nat.le_mul_of_pos_left _ (by omega : 0 < K0 + 1)).trans hKh
  have hendpointLe : forall i : Fin 4,
      roughPhysicalNatEndpoint
          (2 * n + upperTailLength c n)
          (2 * n)
          (2 * n - (K0 + 1) * upperTailLength c n)
          n i <= 3 * n := by
    intro i
    fin_cases i <;> simp [roughPhysicalNatEndpoint] <;> omega
  have hendpointPos : forall i : Fin 4,
      0 < roughPhysicalNatEndpoint
          (2 * n + upperTailLength c n)
          (2 * n)
          (2 * n - (K0 + 1) * upperTailLength c n)
          n i := by
    intro i
    fin_cases i <;> simp [roughPhysicalNatEndpoint] <;> omega
  have hlogs : forall i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i : Real) <=
        5 * Real.log (yNat n : Real) := by
    intro i
    have hrowOne : row.1 = 1 := rfl
    simp only [hrowOne, Nat.div_one]
    exact
      (Real.log_le_log
        (by exact_mod_cast hendpointPos i)
        (by exact_mod_cast hendpointLe i)).trans hlogThree
  have htail :
      (upperTailLength c n : Real) <=
        2 * c * (n : Real) / L n := by
    calc
      (upperTailLength c n : Real) <=
          2 * c * secondOrderScale n := htailScale
      _ = 2 * c * (n : Real) / L n := by
        unfold secondOrderScale L
        ring
  have hlogFace' : L n / 5 <= Real.log (yNat n : Real) := by
    convert hlogFace using 1; ring
  have hquota :=
    roughCanonicalBalancedRawRowQuotaError_abs_le_unified
      W K0 (beta := beta) hc hn row
        (by simpa only [row] using (show 1 <= n by omega))
        hWy hY (by omega) hLone hlogFace' htail hKh htailPos hlogs
  have hraw :=
    BankPaperRealization.roughCanonicalRawRowDiscrepancy_eq_quotaError
      W n (upperTailLength c n) (K0 + 1)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row
  have htargetPos : 0 < secondOrderScale n / L n := by
    exact zero_lt_one.trans_le htargetOneN
  have htargetEq :
      (n : Real) / L n ^ 2 = secondOrderScale n / L n := by
    unfold secondOrderScale L
    ring
  have hrawBound :
      |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| <=
        3 * (C * (secondOrderScale n / L n + 1)) := by
    have hrowOne : row.1 = 1 := rfl
    have hrawOne :
        roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
            (K0 + 1) 1
              (bankPaperCanonicalBalancedRawWeight W K0 c beta n) =
          roughCanonicalRawRowQuotaError W n (upperTailLength c n)
            (K0 + 1) (yNat n)
            (roughHeadBalancedAlpha W n (upperTailLength c n)
              (K0 + 1) beta (L n))
            beta (L n) row := by
      simpa only [bankPaperCanonicalBalancedRawWeight, hrowOne] using hraw
    rw [hrawOne]
    simpa only [C, hrowOne, Nat.div_one, htargetEq] using hquota
  rw [Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos htargetPos]
  calc
    |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
        (K0 + 1) 1
          (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| <=
        3 * (C * (secondOrderScale n / L n + 1)) := hrawBound
    _ <= (6 * C) * (secondOrderScale n / L n) := by
      nlinarith [mul_nonneg hC
        (sub_nonneg.mpr htargetOneN)]

/-! ## Exact construction boundary and the charged mass ledger -/

/-- The exact finite witness consumed by the initial-mass theorem.

It identifies the three observable finite sets with one paper realization,
installs the already-constructed charged nonsmooth rows, and records only
the one additional fact needed on the smooth row: the initial selector and
the balanced literal raw selector have the same guarded label-one mass. -/
def BankPaperCanonicalTopFrozenBalancedInitialRealization
    (depth W K0 n : Nat) (c deltaStar beta : Real)
    (fixed bankBase candidates : Finset Nat)
    (initialSelector : Nat -> Real) : Prop :=
  ∃ Rn : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)),
  ∃ certn : GuardedCentralAnchorCertificate c depth n
      Rn.anchorGuardLeftCore Rn.anchorGuardRightCore
      (Rn.centralChangedMarkers depth),
    fixed = Rn.paperFixedExceptionalFactors deltaStar ∧
    bankBase = Rn.prechargeBaseState ∧
    candidates =
      Rn.roughCanonicalGuardedCandidateSet certn deltaStar (K0 + 1) ∧
    BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K0 + 1) Rn certn deltaStar initialSelector ∧
    (∑ a ∈ Rn.roughCanonicalGuardedRow certn deltaStar
        (K0 + 1) 1, initialSelector a) =
      ∑ a ∈ Rn.roughCanonicalGuardedRow certn deltaStar
        (K0 + 1) 1,
          bankPaperCanonicalBalancedRawWeight W K0 c beta n a

/-- Once the exact smooth-row mass is installed, the charged all-row
identity has only two terms left: the balanced raw discrepancy and the raw
mass removed by the numerical guard. -/
theorem chargedSelectorMass_sub_height_eq_neg_balancedRawDiscrepancy_sub_deleted
    {c deltaStar beta : Real} {depth n W K0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (selector : Nat -> Real)
    (hn : 0 < n) (hdeltaUpper : deltaStar <= 1)
    (hrows : BankPaperCanonicalChargedNonsmoothRowRealization
      (K := K0 + 1) R certificate deltaStar selector)
    (hcapacity : forall label,
      IsCompleteRoughLabel (yNat n) label ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar
          (K0 + 1) label)
    (hsmooth :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
          (K0 + 1) 1, selector a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a) :
    ((R.paperFixedExceptionalFactors deltaStar).card : Real) +
        (R.prechargeBaseState.card : Real) +
        (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1), selector a) -
          (upperTailLength c n : Real) =
      -roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n) -
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a := by
  have hledger :=
    bankPaperCanonical_chargedSelectorMass_sub_height_eq_rawSmoothLedger
      R certificate deltaStar
        (bankPaperCanonicalBalancedRawWeight W K0 c beta n)
        selector hrows.1 hrows.2 hcapacity
  rw [
    R.paperFixedExceptionalFactors_completeLabelMultiplicity_one_eq_zero
      hn hdeltaUpper,
    R.prechargeBaseState_completeLabelMultiplicity_one_eq_zero,
    hsmooth] at hledger
  simpa only [Nat.cast_zero, add_zero, zero_add, sub_self] using hledger

/-! ## Asymptotic initial-selector mass theorem -/

/-- The frozen-top construction closes the actual initial-selector mass
estimate.

The premise is only an eventual family of exact finite witnesses.  All
analytic inputs—raw quota error, guard capacity, cutoff geometry, and the
size of the deleted smooth row—are discharged internally. -/
theorem bankPaperCanonicalActualSelectorMassEstimate_of_topFrozenBalancedInitial
    (depth W K0 poolMinimum : Nat)
    {c deltaStar beta : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector : Nat -> Nat -> Real)
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalTopFrozenBalancedInitialRealization
        depth W K0 n c deltaStar beta
          (fixed n) (bankBase n) (candidates n)
          (initialSelector n)) :
    BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates initialSelector := by
  have Hraw :=
    bankPaperCanonicalBalancedRawSmoothRowDiscrepancy_isBigO
      W K0 hc (beta := beta)
  rcases (isBigO_iff').mp Hraw with
    ⟨Craw, hCraw, HrawBound⟩
  let M := roughCanonicalBalancedRawWeightGuardBound W K0 c beta
  have hM : 0 <= M := by
    dsimp only [M]
    exact
      roughCanonicalBalancedRawWeightGuardBound_nonneg
        W K0 (beta := beta) hc
  have HcapacityRaw :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W (K0 + 1) poolMinimum hc hdelta
  have Hthreshold :=
    eventually_ge_atTop (centralAnchorCutoffThreshold depth)
  have HyCutoff :=
    eventually_yNat_lt_centralAnchorCutoff depth
  have HLOne : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    topFrozenInitialMass_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  unfold BankPaperCanonicalActualSelectorMassEstimate
  apply IsBigO.of_bound (Craw + M)
  filter_upwards [Hconstructed, HrawBound, HcapacityRaw,
      Hthreshold, HyCutoff, eventually_ge_atTop 2, HLOne,
      eventually_yNat_cast_le_secondOrderScale_div_L]
      with n hwitness hrawBoundN hcapacityRaw hnCutoff hyCutoff
        hn hLone hyNatScale
  rcases hwitness with
    ⟨Rn, certn, hfixed, hbankBase, hcandidates, hrows, hsmooth⟩
  have hcapacity :
      forall label, IsCompleteRoughLabel (yNat n) label ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity Rn certn deltaStar
            (K0 + 1) label := by
    intro label hcomplete hactive
    exact
      (hcapacityRaw depth Rn.anchorGuardLeftCore
        Rn.anchorGuardRightCore (Rn.centralChangedMarkers depth)
        Rn certn hnCutoff hyCutoff label hcomplete hactive).2.2
  have hmass :=
    Rn.chargedSelectorMass_sub_height_eq_neg_balancedRawDiscrepancy_sub_deleted
      certn (initialSelector n) (by omega) hdeltaUpper.le
        hrows hcapacity hsmooth
  have hmassObserved :
      ((fixed n).card : Real) + ((bankBase n).card : Real) +
          (∑ a ∈ candidates n, initialSelector n a) -
            bankPaperCanonicalUpperTailHeight c n =
        -roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
            (K0 + 1) 1
              (bankPaperCanonicalBalancedRawWeight W K0 c beta n) -
          ∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
            (K0 + 1) 1,
              bankPaperCanonicalBalancedRawWeight W K0 c beta n a := by
    simpa only [hfixed, hbankBase, hcandidates,
      bankPaperCanonicalUpperTailHeight] using hmass
  have htargetPos : 0 < secondOrderScale n / L n :=
    div_pos (secondOrderScale_pos (by omega)) (L_pos hn)
  have hrawAbs :
      |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| <=
        Craw * (secondOrderScale n / L n) := by
    simpa only [Real.norm_eq_abs, abs_of_pos htargetPos] using hrawBoundN
  have hdeleted :=
    Rn.abs_sum_roughCanonicalGuardDeletedSmoothRow_balancedRawWeight_le
      certn hc hn hLone hnCutoff hyCutoff
      (deltaStar := deltaStar) (beta := beta) (W := W) (K0 := K0)
  have hdeletedScale :
      |∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
        bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
          (secondOrderScale n / L n) * M := by
    apply hdeleted.trans
    exact mul_le_mul_of_nonneg_right hyNatScale hM
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos htargetPos,
    hmassObserved]
  calc
    |-roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n) -
        ∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a| <=
      |-roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| +
        |∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a| :=
      abs_sub _ _
    _ = |roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
          (K0 + 1) 1
            (bankPaperCanonicalBalancedRawWeight W K0 c beta n)| +
        |∑ a ∈ Rn.roughCanonicalGuardDeletedRow certn deltaStar
          (K0 + 1) 1,
            bankPaperCanonicalBalancedRawWeight W K0 c beta n a| := by
      rw [abs_neg]
    _ <= Craw * (secondOrderScale n / L n) +
          (secondOrderScale n / L n) * M :=
      add_le_add hrawAbs hdeletedScale
    _ = (Craw + M) * (secondOrderScale n / L n) := by ring

/-! ## The concrete WithTop/scaled-seed constructor -/

/-- The exact scaled-seed smooth-row theorem from the frozen-top source
constructs the finite witness required above, provided the same selector
already carries the charged nonsmooth rows.

This deliberately remains a finite constructor: turning an arbitrary
family of `BridgeData` into a family indexed definitionally by its sample
integer requires a separate synchronization interface. -/
theorem bankPaperCanonicalTopFrozenBalancedInitialRealization_of_scaledSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct q : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hq :
      q = bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
        B.sampleData.W (K0 + 1) betaAct)
    (hrows :
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K0 + 1) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) B R certificate deltaStar betaProt
              (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
                (upperTailLength c B.sampleData.n) (K0 + 1)
                  (betaProt + betaAct) B.L)
              (betaProt + betaAct)
              (bankPaperCanonicalScaledActiveSeed T q))) :
    BankPaperCanonicalTopFrozenBalancedInitialRealization
      depth B.sampleData.W K0 B.sampleData.n c deltaStar
        (betaProt + betaAct)
        (R.paperFixedExceptionalFactors deltaStar)
        R.prechargeBaseState
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar
          (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
          (K := K0 + 1) B R certificate deltaStar betaProt
            (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) (K0 + 1)
                (betaProt + betaAct) B.L)
            (betaProt + betaAct)
            (bankPaperCanonicalScaledActiveSeed T q)) := by
  refine ⟨R, certificate, rfl, rfl, rfl, hrows, ?_⟩
  simpa only [bankPaperCanonicalBalancedRawWeight,
    BridgeData.L, Scale.L] using
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_scaledSeed_smoothRow_eq_balancedRaw
      (K := K0 + 1) B R certificate T deltaStar betaProt betaAct
        (roughHeadBalancedAlpha B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) (K0 + 1)
            (betaProt + betaAct) B.L)
        q hvalues hq

end BankPaperRealization

end

end Erdos390.WholePaper
