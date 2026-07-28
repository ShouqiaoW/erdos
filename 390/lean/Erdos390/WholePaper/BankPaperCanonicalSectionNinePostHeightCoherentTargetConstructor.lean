import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal
import Erdos390.WholePaper.BankPaperPrechargeUniformCapacityAsymptotic
import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic
import Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightHeadMarginAlgebra
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPhysicalMarginAlgebra

/-!
# The coherent finite post-height target constructor

This file closes the finite choice boundary between the depth-first
combined-charge terminal and the fresh Section 9 post-height bridge.

There are two deliberately separate pieces.

* The first theorem turns the eventual existential output of
  `BankPaperCombinedChargeTerminalAtDepth` into one honest tail family.  Its
  conclusion repeats the six literal terminal properties pointwise; no
  conclusion-bearing structure is introduced.
* The bridge definitions below start from an actual
  `StructuredSampleData`, build a harmless scaffold bridge, form the
  paper's literal head/physical barycentric target on that sample, and then
  install that same target in a canonical bridge.  This removes the
  otherwise circular-looking dependence of `barycentricTargetOfPaperData`
  on an already supplied `BridgeData`.

The eventual head and physical interior estimates are proved in the
remaining sections of this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

/-! ## One coherent family chosen from the eventual terminal -/

/-- Choose one realization/certificate pair on a genuine tail from the
depth-first combined-charge terminal.

The six conjuncts are the terminal's literal finite conclusions, retained
for the very same fiber selected by `F`.  In particular this theorem does
not hide any capacity estimate in a new record or contract. -/
theorem
    exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth
    {c deltaStar : Real} {depth : Nat}
    (H : BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) :
    ∃ N : Nat, ∃ F : BankPaperCanonicalGuardedTailFamily c depth N,
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n) := by
  simp only [BankPaperCombinedChargeTerminalAtDepth] at H
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp H
  choose R hR using hN
  choose certificate hcertificate using hR
  let F : BankPaperCanonicalGuardedTailFamily c depth N :=
    { fiber := fun n hn => ⟨R n hn, certificate n hn⟩ }
  refine ⟨N, F, ?_⟩
  intro n hn
  simpa only [F, BankPaperCanonicalGuardedTailFamily.realization,
    BankPaperCanonicalGuardedTailFamily.certificate] using
      hcertificate n hn

/-! ## Uniform finite head bounds from the same fibers -/

/-- A fixed positive coefficient retained for every head prime at most
`W`.  The denominator `48 W` leaves ample room for both pieces of the
combined charge outside the stationary anchor support. -/
def bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
    (c : Real) (W : Nat) : Real :=
  (c - C0) / (48 * (W : Real))

theorem bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos
    {c : Real} (hc : C0 < c) {W : Nat} (hW : 0 < W) :
    0 < bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W := by
  unfold bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
  exact div_pos (sub_pos.mpr hc)
    (mul_pos (by norm_num) (by exact_mod_cast hW))

/-- The fixed-prime upper coefficient used for the head-simplex
zero-coordinate estimate. -/
def bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
    (c : Real) (p : Nat) : Real :=
  c / (((p - 1 : Nat) : Real)) + 1

/-- Simultaneous upper tail estimate on an arbitrary fixed finite prime
set. -/
theorem
    eventually_upperTailValuation_le_postHeightHeadUpperCoefficient_on_finset
    {c : Real} (hc : 0 < c) (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) :
    ∀ᶠ n : Nat in atTop, ∀ p ∈ P,
      (upperTailValuation c n p : Real) ≤
        bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p *
          secondOrderScale n := by
  have hratio :
      ∀ᶠ n : Nat in atTop, ∀ p ∈ P,
        (upperTailValuation c n p : Real) / secondOrderScale n ≤
          bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p := by
    rw [Finset.eventually_all]
    intro p hp
    exact
      (upperTailValuation_normalized_tendsto hc (hprime p hp)).eventually
        (eventually_le_nhds (by
          unfold
            bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
          linarith))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with
      n hn hscale
  intro p hp
  exact (div_le_iff₀ hscale).mp (hn p hp)

set_option maxHeartbeats 1600000 in
/-- On every fixed finite head set, the residual selector target from one
coherent combined-charge tail family has a uniform positive linear lower
bound and the fixed-prime factorial-tail upper bound.

Only the three literal fiber facts used in the proof are hypotheses:
charge divisibility, retained reserve on the stationary prefix, and the
exact precharged-target times anchor-divisor identity.  They are direct
conjuncts of
`exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth`.
-/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
    {c deltaStar : Real} (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    {depth N W : Nat} (hW : 0 < W)
    (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime)
    (hPLe : ∀ p ∈ P, p ≤ W)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hfiber :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n)) :
    ∀ᶠ n : Nat in atTop, ∀ (hn : N ≤ n) (p : {p : Nat // p ∈ P}),
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
            secondOrderScale n ≤
          ((F.certificate n hn).selectorTailTarget
              (F.realization n hn)
              ((F.realization n hn).paperFixedExceptionalFactors
                deltaStar)).factorization p.1 ∧
        (((F.certificate n hn).selectorTailTarget
              (F.realization n hn)
              ((F.realization n hn).paperFixedExceptionalFactors
                deltaStar)).factorization p.1 : Real) ≤
          bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
              c p.1 *
            secondOrderScale n := by
  have hC0 : (0 : Real) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0.trans hc
  have hgap : 0 < c - C0 := sub_pos.mpr hc
  have hgapLt : c - C0 < c := by linarith
  have hy := eventually_bankAnchor_fixed_le_yNat W
  have hfixed :=
    eventually_paperFixedExceptionalFactors_charge_le_combinedReserve
      hc hdeltaStar
  have hbase :=
    eventually_bankPaperPrecharge_perPrimeCapacity
      (delta := (c - C0) / 24) (by positivity)
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  have hlower :=
    eventually_upperTailValuation_ge_mul_scale_on_finset
      hcPos P
        (fun p => (c / 2) / (((p - 1 : Nat) : Real)))
        hprime (by
          intro p hp
          have hpred :
              0 < (((p - 1 : Nat) : Real)) := by
            exact_mod_cast Nat.sub_pos_of_lt (hprime p hp).one_lt
          exact
            (div_lt_div_iff_of_pos_right hpred).2 (by linarith))
  have hupper :=
    eventually_upperTailValuation_le_postHeightHeadUpperCoefficient_on_finset
      hcPos P hprime
  filter_upwards [hy, hfixed, hbase, hendpoint, hlower, hupper,
      eventually_secondOrderScale_pos] with
      n hyN hfixedN hbaseN hendpointN hlowerN hupperN hscale
  intro hn p
  let R := F.realization n hn
  let certificate := F.certificate n hn
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let charge := R.selectorTailCharge fixed
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  let tail := centralTailProduct n (upperTailLength c n)
  have hpPrime : p.1.Prime := hprime p.1 p.2
  have hpLeW : p.1 ≤ W := hPLe p.1 p.2
  have hpY : p.1 ≤ yNat n := hpLeW.trans hyN
  have hpPos : 0 < p.1 := hpPrime.pos
  have hpReal : (0 : Real) < p.1 := by exact_mod_cast hpPos
  have hpredNat : 0 < p.1 - 1 :=
    Nat.sub_pos_of_lt hpPrime.one_lt
  have hpred : (0 : Real) < ((p.1 - 1 : Nat) : Real) := by
    exact_mod_cast hpredNat
  have hpredLeP : ((p.1 - 1 : Nat) : Real) ≤ (p.1 : Real) := by
    exact_mod_cast Nat.sub_le p.1 1
  have hpredLeW : ((p.1 - 1 : Nat) : Real) ≤ (W : Real) := by
    exact_mod_cast (Nat.sub_le p.1 1).trans hpLeW
  have hWReal : (0 : Real) < W := by exact_mod_cast hW
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htailMem := R.paperFixedExceptionalFactors_subset_tail
      deltaStar (by simpa only [fixed] using ha)
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htailMem).1
  have hfixedProdPos : 0 < fixed.prod id := by
    apply Finset.prod_pos
    intro a ha
    simpa only [id_eq] using hfixedPositive a ha
  have hbasePos : 0 < R.prechargeBaseStateProduct := by
    rw [BankPaperRealization.prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hchargePos : 0 < charge := by
    exact R.selectorTailCharge_pos fixed hfixedPositive
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailPos : 0 < tail :=
    centralTailProduct_pos n (upperTailLength c n)
  obtain ⟨hchargeDvd, hretained, htargetTail⟩ := hfiber n hn
  have hselectorPos :
      0 < certificate.selectorTailTarget R fixed :=
    certificate.selectorTailTarget_pos R fixed hfixedPositive hchargeDvd
  have hchargeLe : ∀ q,
      charge.factorization q ≤
        certificate.prechargedTailTarget.factorization q := by
    exact
      (Nat.factorization_le_iff_dvd hchargePos.ne'
        certificate.prechargedTailTarget_pos.ne').mpr hchargeDvd
  have hselectorIdentity :
      certificate.selectorTailTarget R fixed * charge =
        certificate.prechargedTailTarget :=
    certificate.selectorTailTarget_mul_selectorTailCharge
      R fixed hchargeDvd
  have hselectorDvdTail :
      certificate.selectorTailTarget R fixed ∣ tail := by
    exact dvd_trans
      ⟨charge, hselectorIdentity.symm⟩
      ⟨divisor, (by simpa only [divisor, tail] using htargetTail.symm)⟩
  have hselectorUpperNat :
      (certificate.selectorTailTarget R fixed).factorization p.1 ≤
        tail.factorization p.1 :=
    ((Nat.factorization_le_iff_dvd hselectorPos.ne' htailPos.ne').mpr
      hselectorDvdTail) p.1
  have hselectorUpper :
      ((certificate.selectorTailTarget R fixed).factorization p.1 :
          Real) ≤
        bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
            c p.1 *
          secondOrderScale n := by
    calc
      ((certificate.selectorTailTarget R fixed).factorization p.1 :
          Real) ≤ (tail.factorization p.1 : Real) := by
        exact_mod_cast hselectorUpperNat
      _ = (upperTailValuation c n p.1 : Real) := by
        rw [upperTailValuation_eq_centralTailProduct_factorization]
      _ ≤
          bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
              c p.1 *
            secondOrderScale n :=
        hupperN p.1 p.2
  constructor
  · by_cases hpSupport : p.1 ∈ primesUpTo (2 * depth + 1)
    · have hfloorCoefficient :
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W ≤
            (c - C0) /
              (24 * (((p.1 - 1 : Nat) : Real))) := by
        unfold bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
        apply (div_le_div_iff₀
          (mul_pos (by norm_num) hWReal)
          (mul_pos (by norm_num) hpred)).2
        nlinarith
      have hfloorScaled :
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                secondOrderScale n ≤
            (c - C0) /
                  (24 * (((p.1 - 1 : Nat) : Real))) *
                secondOrderScale n :=
        mul_le_mul_of_nonneg_right hfloorCoefficient hscale.le
      have hretainedP := hretained p.1 hpSupport
      rw [certificate.selectorTailTarget_factorization_eq_sub
        R fixed hchargeDvd p.1,
        Nat.cast_sub (hchargeLe p.1)]
      linarith
    · have hdivisorZero : divisor.factorization p.1 = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hpDvd
        exact hpSupport
          (certificate.divisor_prime_support p.1 hpPrime
            (by simpa only [divisor] using hpDvd))
      have hprechargedFactorization :
          certificate.prechargedTailTarget.factorization p.1 =
            upperTailValuation c n p.1 := by
        rw [upperTailValuation_eq_centralTailProduct_factorization,
          ← htargetTail,
          Nat.factorization_mul certificate.prechargedTailTarget_pos.ne'
            hdivisorPos.ne',
          Finsupp.add_apply, hdivisorZero, add_zero]
      have hchargeFactorization :
          charge.factorization p.1 =
            (fixed.prod id).factorization p.1 +
              R.prechargeBaseStateProduct.factorization p.1 := by
        dsimp only [charge]
        rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
          Nat.factorization_mul hfixedProdPos.ne' hbasePos.ne',
          Finsupp.add_apply]
      have hfixedBound :=
        hfixedN R p.1 hpPrime hpY
      have hfixedPredCoefficient :
          (c - C0) / 24 / (p.1 : Real) ≤
            ((c - C0) / 24) /
              (((p.1 - 1 : Nat) : Real)) := by
        exact div_le_div_of_nonneg_left
          (by positivity) hpred hpredLeP
      have hfixedPred :
          ((fixed.prod id).factorization p.1 : Real) ≤
            ((c - C0) / 24) /
                (((p.1 - 1 : Nat) : Real)) *
              secondOrderScale n := by
        calc
          ((fixed.prod id).factorization p.1 : Real) ≤
              (c - C0) / 24 * secondOrderScale n / (p.1 : Real) := by
            simpa only [fixed] using hfixedBound
          _ = ((c - C0) / 24 / (p.1 : Real)) *
                secondOrderScale n := by ring
          _ ≤ ((c - C0) / 24 /
                  (((p.1 - 1 : Nat) : Real))) *
                secondOrderScale n :=
            mul_le_mul_of_nonneg_right hfixedPredCoefficient hscale.le
      have hbaseNat :=
        R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
          hpPrime hendpointN.2
      have hbaseCastLog2 :
          (R.prechargeBaseStateProduct.factorization p.1 : Real) ≤
            ((bankPaperAnchorMarkerBudget n *
              Nat.log2 (3 * n) : Nat) : Real) := by
        exact_mod_cast hbaseNat
      have hbaseCast :
          (R.prechargeBaseStateProduct.factorization p.1 : Real) ≤
            ((bankPaperAnchorMarkerBudget n *
              Nat.log 2 (3 * n) : Nat) : Real) := by
        simpa only [Nat.log2_eq_log_two] using hbaseCastLog2
      have hbasePred :
          (R.prechargeBaseStateProduct.factorization p.1 : Real) ≤
            ((c - C0) / 24) /
                (((p.1 - 1 : Nat) : Real)) *
              secondOrderScale n :=
        hbaseCast.trans (hbaseN p.1 hpPrime hpY)
      have hfloorPredCoefficient :
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W ≤
            ((c - C0) / 48) /
              (((p.1 - 1 : Nat) : Real)) := by
        unfold bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
        apply (div_le_div_iff₀
          (mul_pos (by norm_num) hWReal) hpred).2
        nlinarith
      have hfloorPred :
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                secondOrderScale n ≤
            (((c - C0) / 48) /
                (((p.1 - 1 : Nat) : Real))) *
              secondOrderScale n :=
        mul_le_mul_of_nonneg_right hfloorPredCoefficient hscale.le
      have hcoefficientBudget :
          ((c - C0) / 48) /
                (((p.1 - 1 : Nat) : Real)) +
              ((c - C0) / 24) /
                (((p.1 - 1 : Nat) : Real)) +
              ((c - C0) / 24) /
                (((p.1 - 1 : Nat) : Real)) ≤
            (c / 2) /
              (((p.1 - 1 : Nat) : Real)) := by
        rw [show
            (c - C0) / 48 /
                  (((p.1 - 1 : Nat) : Real)) +
                (c - C0) / 24 /
                  (((p.1 - 1 : Nat) : Real)) +
                (c - C0) / 24 /
                  (((p.1 - 1 : Nat) : Real)) =
              (5 * (c - C0) / 48) /
                (((p.1 - 1 : Nat) : Real)) by ring]
        exact
          (div_le_div_iff_of_pos_right hpred).2 (by nlinarith)
      have hcombinedBudget :
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                secondOrderScale n +
              ((fixed.prod id).factorization p.1 : Real) +
              (R.prechargeBaseStateProduct.factorization p.1 : Real) ≤
            (upperTailValuation c n p.1 : Real) := by
        calc
          _ ≤
              ((((c - C0) / 48) /
                    (((p.1 - 1 : Nat) : Real))) +
                (((c - C0) / 24) /
                    (((p.1 - 1 : Nat) : Real))) +
                (((c - C0) / 24) /
                    (((p.1 - 1 : Nat) : Real)))) *
                  secondOrderScale n := by
            rw [add_mul]
            rw [add_mul]
            linarith
          _ ≤ ((c / 2) /
                  (((p.1 - 1 : Nat) : Real))) *
                secondOrderScale n :=
            mul_le_mul_of_nonneg_right hcoefficientBudget hscale.le
          _ ≤ (upperTailValuation c n p.1 : Real) :=
            hlowerN p.1 p.2
      rw [certificate.selectorTailTarget_factorization_eq_sub
        R fixed hchargeDvd p.1,
        Nat.cast_sub (hchargeLe p.1),
        hprechargedFactorization, hchargeFactorization, Nat.cast_add]
      linarith
  · simpa only [R, certificate, fixed] using hselectorUpper

/-! ## One pair of source/post-height mass envelopes -/

/-- The final active mass inherits an `O(secondOrderScale)` upper bound from
the guarded smooth mass and the logarithmically smaller integer height
adjustment. -/
theorem bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
    (W K : Nat) (c betaAct : Real)
    {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde =O[atTop]
      secondOrderScale := by
  have hraw :=
    bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have hqTilde :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde hraw Hledger.1
  have hq0 :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde hqTilde
  have hdLog :=
    bankPaperCanonicalSectionEight_d_isBigO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hd :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =O[atTop]
        secondOrderScale :=
    hdLog.trans
      secondOrderScale_div_L_isLittleO_secondOrderScale.isBigO
  exact (hq0.sub hd).congr_left fun n => rfl

/-- The guarded source mass and the final post-height mass admit one common
positive lower coefficient and one common positive upper coefficient on
the paper scale.  These constants are selected before the later exponent
and before the asymptotic index. -/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceAndFinalMass_linearBounds
    (W K : Nat) {c betaAct : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∃ cLower cUpper : Real,
      0 < cLower ∧ 0 < cUpper ∧
        ∀ᶠ n : Nat in atTop,
          cLower * secondOrderScale n ≤ qTilde n ∧
            qTilde n ≤ cUpper * secondOrderScale n ∧
            cLower * secondOrderScale n ≤
              bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n ∧
            bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n ≤
              cUpper * secondOrderScale n := by
  have hrawLower :=
    bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
      W K hc hbeta
  have hqTildeLower :=
    bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde hrawLower Hledger.1
  have hfinalLower :=
    bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
      W K hc hbeta
        bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      logY Lambda0 mFrozen qTilde Hledger
  have hrawUpper :=
    bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have hqTildeUpper :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde hrawUpper Hledger.1
  have hfinalUpper :=
    bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
      W K c betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      logY Lambda0 mFrozen qTilde Hledger
  rcases hqTildeLower with ⟨cq, hcq, hqLower⟩
  rcases hfinalLower with ⟨cf, hcf, hfLower⟩
  obtain ⟨Cq, hCq, hqUpper⟩ := hqTildeUpper.exists_pos
  obtain ⟨Cf, hCf, hfUpper⟩ := hfinalUpper.exists_pos
  let cLower := min cq cf
  let cUpper := max Cq Cf
  have hcLower : 0 < cLower := by
    dsimp only [cLower]
    exact lt_min hcq hcf
  have hcUpper : 0 < cUpper := by
    dsimp only [cUpper]
    exact hCq.trans_le (le_max_left _ _)
  refine ⟨cLower, cUpper, hcLower, hcUpper, ?_⟩
  filter_upwards [hqLower, hfLower, hqUpper.bound, hfUpper.bound,
      eventually_secondOrderScale_pos] with
      n hqLowerN hfLowerN hqUpperN hfUpperN hscale
  have hqUpperAbs :
      qTilde n ≤ Cq * secondOrderScale n := by
    calc
      qTilde n ≤ |qTilde n| := le_abs_self _
      _ = ‖qTilde n‖ := (Real.norm_eq_abs _).symm
      _ ≤ Cq * ‖secondOrderScale n‖ := hqUpperN
      _ = Cq * secondOrderScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hscale]
  have hfUpperAbs :
      bankPaperCanonicalSmoothFinalActiveMassFamily
          bankPaperCanonicalSectionNinePostHeightPhysicalMu
          logY Lambda0 mFrozen qTilde n ≤
        Cf * secondOrderScale n := by
    calc
      bankPaperCanonicalSmoothFinalActiveMassFamily
          bankPaperCanonicalSectionNinePostHeightPhysicalMu
          logY Lambda0 mFrozen qTilde n ≤
          |bankPaperCanonicalSmoothFinalActiveMassFamily
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            logY Lambda0 mFrozen qTilde n| :=
        le_abs_self _
      _ =
          ‖bankPaperCanonicalSmoothFinalActiveMassFamily
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            logY Lambda0 mFrozen qTilde n‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ Cf * ‖secondOrderScale n‖ := hfUpperN
      _ = Cf * secondOrderScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hscale]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      (mul_le_mul_of_nonneg_right (min_le_left cq cf) hscale.le).trans
        hqLowerN
  · exact hqUpperAbs.trans
      (mul_le_mul_of_nonneg_right (le_max_left Cq Cf) hscale.le)
  · exact
      (mul_le_mul_of_nonneg_right (min_le_right cq cf) hscale.le).trans
        hfLowerN
  · exact hfUpperAbs.trans
      (mul_le_mul_of_nonneg_right (le_max_right Cq Cf) hscale.le)

/-! ## Exact synchronization of the local and family physical means -/

/-- If the local rounded `q0`, frozen height `A0`, and integer adjustment
are the three literal Section 8 family values at the sample index, then the
local post-height physical mean is exactly the family height-to-mass ratio.

This is an exact finite identity.  It is the required bridge from the
family-level physical-margin theorem to
`BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs`; equality of
the final masses alone would not suffice. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPhysicalMean_eq_smoothFamilyRatio
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (q0 A0 : Real) (d : Int)
    (hq0 :
      q0 =
        bankPaperCanonicalSmoothQ0Family
          mFrozen qTilde B.sampleData.n)
    (hA0 :
      A0 =
        bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde B.sampleData.n)
    (hd :
      d =
        bankPaperCanonicalSmoothDIntFamily
          bankPaperCanonicalSectionNinePostHeightPhysicalMu
          logY Lambda0 mFrozen qTilde B.sampleData.n) :
    bankPaperCanonicalSectionNinePostHeightPhysicalMean B q0 A0 d =
      bankPaperCanonicalSmoothFinalActiveHeightFamily
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            logY Lambda0 mFrozen qTilde B.sampleData.n /
        bankPaperCanonicalSmoothFinalActiveMassFamily
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            logY Lambda0 mFrozen qTilde B.sampleData.n := by
  rw [hq0, hA0, hd]
  unfold bankPaperCanonicalSectionNinePostHeightPhysicalMean
    bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
    bankPaperCanonicalSectionNinePostHeightActiveHeight
    bankPaperCanonicalSectionNinePostHeightActiveMass
    bankPaperCanonicalSmoothFinalActiveHeightFamily
    bankPaperCanonicalSmoothFinalActiveMassFamily
    bankPaperCanonicalSmoothDRealFamily
  rw [bankPaperCanonicalSmoothActiveHeightAt_eq_defect_add]
  rfl

/-! ## A non-circular bridge built from structured sample data -/

/-- A harmless positive baseline used only to give the sample a temporary
`BridgeData` wrapper while the genuine barycentric target is constructed. -/
def bankPaperCanonicalSectionNineTargetScaffoldBaseline
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) :
    BaselineAllocation D where
  cellMass := fun _ => 1
  cellMass_pos := fun _ => by norm_num

/-- Temporary bridge on an already constructed sample.  Its baseline is
irrelevant: `barycentricTargetOfPaperData` depends on the structured sample
and the displayed head/physical data, not on this baseline. -/
def bankPaperCanonicalSectionNineTargetScaffoldBridge
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) where
  sampleData := D
  baseline := bankPaperCanonicalSectionNineTargetScaffoldBaseline D
  partition :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
  lowBand := RegularMeshPrimeCutoffs.Mesh.lowBand M
  referenceHead := none
  w := delta + eta
  w_pos := hw
  n_gt_one := hn

@[simp] theorem
    bankPaperCanonicalSectionNineTargetScaffoldBridge_sampleData
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    (bankPaperCanonicalSectionNineTargetScaffoldBridge
      M D hdelta hn hW S hw).sampleData = D :=
  rfl

/-- The source head reserve obtained from the already proved simultaneous
head-margin inequalities. -/
def bankPaperCanonicalSectionNineCoherentSourceHeadReserve
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource)) :
    HeadSimplexReserve P where
  exponent := E
  exponent_pos := hE
  activeMass := qSource
  activeMass_pos := hqSource
  target := target
  margin := margin
  margin_pos := hmargin
  vertex_margin := hvertex
  zero_margin := hzero

@[simp] theorem
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve_exponent
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource)) :
    (bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin hvertex hzero).exponent =
        E :=
  rfl

@[simp] theorem
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve_activeMass
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource)) :
    (bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin hvertex hzero).activeMass =
        qSource :=
  rfl

@[simp] theorem
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve_target
    {P : Finset Nat}
    (E : Nat) (qSource : Real)
    (target : {p : Nat // p ∈ P} → Real)
    (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource)
    (hmargin : 0 < margin)
    (hvertex :
      ∀ p, margin ≤ target p / ((E : Real) * qSource))
    (hzero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          target p / ((E : Real) * qSource))
    (p : {p : Nat // p ∈ P}) :
    (bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin hvertex hzero).target p =
        target p :=
  rfl

/-- The genuine source target, formed directly on the supplied structured
sample through the temporary bridge. -/
def bankPaperCanonicalSectionNineCoherentSourceTarget
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    BarycentricTarget D :=
  (bankPaperCanonicalSectionNineTargetScaffoldBridge
    M D hdelta hn hW S hw).barycentricTargetOfPaperData
      I hlo hhi Rhead Kphysical

/-- Install the directly constructed source target into the canonical mesh
bridge on the same structured sample. -/
def bankPaperCanonicalSectionNineCoherentSourceBridge
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) :=
  bankPaperCanonicalBridgeData D
    (bankPaperCanonicalSectionNineCoherentSourceTarget
      M D I hlo hhi Rhead Kphysical hdelta hn hW S hw)
    M hdelta hn hW S none hw

@[simp] theorem bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    (bankPaperCanonicalSectionNineCoherentSourceBridge
      M D I hlo hhi Rhead Kphysical hdelta hn hW S hw).sampleData = D :=
  rfl

/-- The target installed in the constructed source bridge is exactly the
paper's head/physical barycentric target when viewed from that bridge.
This is the equality consumed by the rounded-source residual connector. -/
theorem bankPaperCanonicalSectionNineCoherentSourceTarget_eq_bridgeTarget
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta) :
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D I hlo hhi Rhead Kphysical hdelta hn hW S hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D I hlo hhi Rhead Kphysical hdelta hn hW S hw
    Tsource =
      Bsource.barycentricTargetOfPaperData
        I hlo hhi Rhead Kphysical := by
  rfl

/-! ## Finite coherent assembly of the fresh bridge inputs -/

/-- The literal finite head set used by the coherent constructor consists
only of primes. -/
theorem bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
    (W : Nat) :
    ∀ p ∈ primesUpTo W, p.Prime := by
  intro p hp
  exact (mem_primesUpTo.mp hp).1

namespace BankPaperRealization

/-- Assemble the literal source head reserve, the fixed source physical
target, the constructed `Bsource`, and the fresh post-height bridge inputs
from the simultaneous head margins and the local physical margin.

The last two arrows are exact ledger synchronizations, not analytic
estimates: the rounded local values must be the displayed `q0` and `A0`.
The conclusion retains those identities together with `q_n = q0-d` and
the exact geometry-facing equalities consumed by the rounded-source
residual theorem. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_coherentMargins
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (hdelta : 0 < delta) (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W) (hw : 0 < delta + eta)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower sigma)
        D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound
        (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper sigma)
        D.n)
    (hprime : ∀ p ∈ P, p.Prime)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization D.n
      (upperEndpoint D.n (upperTailLength c D.n)))
    (certificate : GuardedCentralAnchorCertificate c depth D.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct qSource q0 A0 qn : Real)
    (d : Int) (E : Nat) (margin : Real)
    (hE : 0 < E) (hqSource : 0 < qSource) (hqn : 0 < qn)
    (hmargin : 0 < margin)
    (hpattern : D.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (hsourceVertex :
      ∀ p : {p : Nat // p ∈ P},
        margin ≤
          ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real) /
            ((E : Real) * qSource))
    (hsourceZero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real) /
            ((E : Real) * qSource))
    (hpostVertex :
      ∀ p : {p : Nat // p ∈ P},
        margin ≤
          ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real) /
            ((E : Real) * qn))
    (hpostZero :
      margin ≤
        1 - ∑ p : {p : Nat // p ∈ P},
          ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real) /
            ((E : Real) * qn))
    (hqnEq : qn = q0 - (d : Real))
    (hphysical :
      Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
            .minus) ≤
        (A0 + (d : Real) * L D.n) / qn -
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
      (A0 + (d : Real) * L D.n) / qn +
            bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
        Real.log
          (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
            .plus)) :
    let target : {p : Nat // p ∈ P} → Real :=
      fun p =>
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
            Real)
    let Rhead : HeadSimplexReserve P :=
      bankPaperCanonicalSectionNineCoherentSourceHeadReserve
        E qSource target margin hE hqSource hmargin
          hsourceVertex hsourceZero
    let Kphysical :=
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          hlo hhi Rhead Kphysical hdelta hn hW S hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          hlo hhi Rhead Kphysical hdelta hn hW S hw
    (bankPaperCanonicalSectionNinePostHeightRoundedQ0
          (K0 + 1) Bsource R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            qSource =
        q0) →
    (bankPaperCanonicalSectionNinePostHeightA0
          (K0 + 1) Bsource R certificate Tsource deltaStar
            betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            (betaProt + betaAct) qSource =
        A0) →
    ∃ J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
        (K0 := K0) M Bsource R certificate
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          deltaStar hdelta,
      J.Tsource =
          J.postHeightBridge.barycentricTargetOfPaperData
            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
            J.postHeightHlo J.postHeightHhi Rhead Kphysical ∧
        J.qTilde = Rhead.activeMass ∧
        J.exponent = E ∧
        J.d = d ∧
        J.betaProt = betaProt ∧
        J.betaAct = betaAct ∧
        J.q0 = q0 ∧
        J.A0 = A0 ∧
        J.qn = qn ∧
        J.targetInputs.headMargin = margin ∧
        J.targetInputs.physicalEta =
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
        J.postHeightBridge.sampleData.pattern =
          PaperHeadSimplex.pattern P hprime Rhead.exponent ∧
        (∀ p : {p : Nat // p ∈ P},
          Rhead.target p =
            ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
                Real)) := by
  dsimp only
  intro hq0Sync hA0Sync
  let target : {p : Nat // p ∈ P} → Real :=
    fun p =>
      ((certificate.selectorTailTarget R
        (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 : Real)
  let Rhead : HeadSimplexReserve P :=
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSource hmargin
        hsourceVertex hsourceZero
  let Kphysical :=
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
  let Tsource :=
    bankPaperCanonicalSectionNineCoherentSourceTarget
      M D bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        hlo hhi Rhead Kphysical hdelta hn hW S hw
  let Bsource :=
    bankPaperCanonicalSectionNineCoherentSourceBridge
      M D bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        hlo hhi Rhead Kphysical hdelta hn hW S hw
  have hq0Sync' :
      bankPaperCanonicalSectionNinePostHeightRoundedQ0
          (K0 + 1) Bsource R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            qSource =
        q0 := by
    simpa only [Bsource, Tsource, Rhead, Kphysical, target] using hq0Sync
  have hA0Sync' :
      bankPaperCanonicalSectionNinePostHeightA0
          (K0 + 1) Bsource R certificate Tsource deltaStar
            betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            (betaProt + betaAct) qSource =
        A0 := by
    simpa only [Bsource, Tsource, Rhead, Kphysical, target] using hA0Sync
  have hactiveMass :
      0 <
        bankPaperCanonicalSectionNinePostHeightActiveMass
          (bankPaperCanonicalSectionNinePostHeightRoundedQ0
            (K0 + 1) Bsource R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              qSource)
          d := by
    rw [bankPaperCanonicalSectionNinePostHeightActiveMass_eq, hq0Sync',
      ← hqnEq]
    exact hqn
  have hmean :
      bankPaperCanonicalSectionNinePostHeightPhysicalMean
          Bsource
          (bankPaperCanonicalSectionNinePostHeightRoundedQ0
            (K0 + 1) Bsource R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              qSource)
          (bankPaperCanonicalSectionNinePostHeightA0
            (K0 + 1) Bsource R certificate Tsource deltaStar
              betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              (betaProt + betaAct) qSource)
          d =
        (A0 + (d : Real) * L D.n) / qn := by
    unfold bankPaperCanonicalSectionNinePostHeightPhysicalMean
      bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
      bankPaperCanonicalSectionNinePostHeightActiveHeight
      bankPaperCanonicalSectionNinePostHeightActiveMass
    rw [hq0Sync', hA0Sync', ← hqnEq]
    rfl
  let Htarget :
      BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
        Bsource bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        (bankPaperCanonicalSectionNinePostHeightRoundedQ0
          (K0 + 1) Bsource R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            qSource)
        (bankPaperCanonicalSectionNinePostHeightA0
          (K0 + 1) Bsource R certificate Tsource deltaStar
            betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            (betaProt + betaAct) qSource)
        d E
        (bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
          Bsource R certificate deltaStar) :=
    { exponent_pos := hE
      activeMass_pos := hactiveMass
      headMargin := margin
      headMargin_pos := hmargin
      vertex_margin := by
        intro p
        simpa only [
          bankPaperCanonicalSectionNinePostHeightActiveHeadTarget,
          bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
          hq0Sync', ← hqnEq] using hpostVertex p
      zero_margin := by
        simpa only [
          bankPaperCanonicalSectionNinePostHeightActiveHeadTarget,
          bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
          hq0Sync', ← hqnEq] using hpostZero
      physicalEta :=
        bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2
      physicalEta_pos := by
        exact half_pos
          bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos
      minus_below := by
        rw [hmean]
        exact hphysical.1
      plus_above := by
        rw [hmean]
        exact hphysical.2 }
  let J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        deltaStar hdelta :=
    { Tsource := Tsource
      betaProt := betaProt
      betaAct := betaAct
      qTilde := qSource
      d := d
      exponent := E
      hW := hW
      scaleSeparation := S
      hlo := hlo
      hhi := hhi
      targetInputs := Htarget }
  refine ⟨J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hq0Sync'
  · exact hA0Sync'
  · change
      bankPaperCanonicalSectionNinePostHeightRoundedQ0
            (K0 + 1) Bsource R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                Bsource c K0 betaProt betaAct)
              qSource -
          (d : Real) =
        qn
    rw [hq0Sync']
    exact hqnEq.symm
  · rfl
  · rfl
  · simpa only [J, Rhead,
      bankPaperCanonicalSectionNineCoherentSourceHeadReserve_exponent] using
      hpattern
  · intro p
    rfl

/-! ## Eventual coherent target construction on supplied sample geometry -/

set_option maxHeartbeats 2400000 in
/-- Choose one exponent and one positive head margin before the mesh, then
construct the genuine source bridge and fresh post-height bridge inputs on
every sufficiently large supplied structured sample.

The three final arrows are the exact upstream family identifications needed
to compare the local frozen ledger with the Section 8 analytic families.
The rounded `q0`, the physical defect `A0`, the integer height, and the final
mass are not hypotheses: they are chosen literally in the proof.  The
result exposes precisely the target slice consumed by the coherent residual
connector, together with the two terminal divisibilities needed downstream.
-/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeightCoherentTarget_of_guardedTailFamily
    {c deltaStar betaProt betaAct : Real}
    {depth Ntail W K0 : Nat}
    (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    (hW : 0 < W) (hbetaAct : 0 < betaAct)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (hterminal :
      ∀ n (hn : Ntail ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n))
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar))) :
    ∃ E : Nat, ∃ margin : Real,
      0 < E ∧ 0 < margin ∧
        0 <
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
        ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta),
          ∀ᶠ n : Nat in atTop,
            ∀ (hdelta : 0 < delta)
              (D : StructuredSampleData
                (PaperHeadSimplex.Tag (primesUpTo W))),
              D.n = n →
              D.W = W →
              ∃ hnD : 1 < D.n,
              ∃ hWD : D.W ≠ 0,
              ∃ hw : 0 < delta + eta,
              ∀ (S : ScaleSeparation M D.n D.W)
                (_hpattern :
                  D.pattern =
                    PaperHeadSimplex.pattern (primesUpTo W)
                      (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                        W) E)
                (hlo : ∀ sigma, D.lo sigma =
                  physicalBound
                    (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                      sigma) D.n)
                (hhi : ∀ sigma, D.hi sigma =
                  physicalBound
                    (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                      sigma) D.n),
                ∃ hnTail : Ntail ≤ D.n,
                  let R := F.realization D.n hnTail
                  let certificate := F.certificate D.n hnTail
                  let qSource :=
                    F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar D.n
                  let target : {p : Nat // p ∈ primesUpTo W} → Real :=
                    fun p =>
                      ((certificate.selectorTailTarget R
                        (R.paperFixedExceptionalFactors
                          deltaStar)).factorization p.1 : Real)
                  ∃ Rhead : HeadSimplexReserve (primesUpTo W),
                    Rhead.exponent = E ∧
                      Rhead.activeMass = qSource ∧
                      Rhead.margin = margin ∧
                      (∀ p, Rhead.target p = target p) ∧
                      (let Kphysical :=
                        bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
                       let Tsource :=
                        bankPaperCanonicalSectionNineCoherentSourceTarget
                          M D
                            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                            hlo hhi Rhead Kphysical hdelta
                            hnD hWD S hw
                       let Bsource :=
                        bankPaperCanonicalSectionNineCoherentSourceBridge
                          M D
                            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                            hlo hhi Rhead Kphysical hdelta
                            hnD hWD S hw
                       let alpha :=
                        bankPaperCanonicalPostHfitBalancedAlpha
                          Bsource c K0 betaProt betaAct
                       mFrozen D.n =
                            bankPaperCanonicalTopFrozenSmoothFrozenMass
                              (K := K0 + 1) Bsource R certificate
                                deltaStar betaProt alpha →
                         logY D.n =
                            bankPaperCanonicalSectionNinePostHeightLogY
                              Bsource R certificate →
                         Lambda0 D.n =
                            bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                              (K0 + 1) Bsource R certificate Tsource
                                deltaStar betaProt alpha
                                (betaProt + betaAct) qSource →
                         ∃ J :
                            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                              (K0 := K0) M Bsource R certificate
                                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                deltaStar hdelta,
                           J.Tsource =
                                J.postHeightBridge.barycentricTargetOfPaperData
                                  bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                  J.postHeightHlo J.postHeightHhi
                                  Rhead Kphysical ∧
                             J.qTilde = Rhead.activeMass ∧
                             J.qTilde =
                                bankPaperCanonicalGuardedSmoothBaseMass
                                  R certificate deltaStar W
                                    (K0 + 1) betaAct ∧
                             J.exponent = E ∧
                             J.d =
                                bankPaperCanonicalSmoothDIntFamily
                                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                                  logY Lambda0 mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.betaProt = betaProt ∧
                             J.betaAct = betaAct ∧
                             J.q0 =
                                bankPaperCanonicalSmoothQ0Family
                                  mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.A0 =
                                bankPaperCanonicalSmoothA0Family
                                  logY Lambda0 mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.qn =
                                bankPaperCanonicalSmoothFinalActiveMassFamily
                                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                                  logY Lambda0 mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.targetInputs.headMargin = margin ∧
                             J.targetInputs.physicalEta =
                                bankPaperCanonicalSectionNinePostHeightPhysicalEta /
                                  2 ∧
                             J.postHeightBridge.sampleData.pattern =
                                PaperHeadSimplex.pattern (primesUpTo W)
                                  (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                                    W) Rhead.exponent ∧
                             primesUpTo J.postHeightBridge.sampleData.W ⊆
                                primesUpTo W ∧
                             (∀ p : {p : Nat // p ∈ primesUpTo W},
                                p.1 ≤ J.postHeightBridge.sampleData.W →
                                  Rhead.target p =
                                    ((certificate.selectorTailTarget R
                                      (R.paperFixedExceptionalFactors
                                        deltaStar)).factorization p.1 :
                                      Real)) ∧
                             centralAnchorDivisor D.n
                                    (centralAnchorCutoff depth D.n)
                                    certificate.q *
                                  R.prechargeBaseStateProduct ∣
                                centralTailProduct D.n
                                  (upperTailLength c D.n) ∧
                             R.selectorTailCharge
                                  (R.paperFixedExceptionalFactors deltaStar) ∣
                                certificate.prechargedTailTarget) := by
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  have hC0Pos : (0 : Real) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  obtain ⟨cLower, cUpper, hcLower, hcUpper, hmass⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceAndFinalMass_linearBounds
      W (K0 + 1) hcPos hbetaAct logY Lambda0 mFrozen qTilde
        (by simpa only [qTilde] using Hledger)
  let a : {p : Nat // p ∈ primesUpTo W} → Real :=
    fun _ => bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W
  let b : {p : Nat // p ∈ primesUpTo W} → Real :=
    fun p =>
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p.1
  have hprime :
      ∀ p ∈ primesUpTo W, p.Prime :=
    bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W
  have hPLe : ∀ p ∈ primesUpTo W, p ≤ W := by
    intro p hp
    exact (mem_primesUpTo.mp hp).2
  have ha : ∀ p, 0 < a p := by
    intro p
    simpa only [a] using
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos hc hW
  have hb : ∀ p, 0 ≤ b p := by
    intro p
    have hpPrime : p.1.Prime := hprime p.1 p.2
    have hpredNat : 0 < p.1 - 1 :=
      Nat.sub_pos_of_lt hpPrime.one_lt
    have hpredReal :
        (0 : Real) < ((p.1 - 1 : Nat) : Real) := by
      exact_mod_cast hpredNat
    dsimp only [b,
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient]
    exact
      (add_pos (div_pos hcPos hpredReal) (by norm_num)).le
  obtain ⟨E, hE, hElarge⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_headExponent_large
      b cLower hcLower
  let margin :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper
  have hmarginPos : 0 < margin := by
    simpa only [margin] using
      bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
        E a cUpper hE ha hcUpper
  have hfiberHead :
      ∀ n (hn : Ntail ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n) := by
    intro n hn
    dsimp only
    have h := hterminal n hn
    dsimp only at h
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩
  have hhead :=
    eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
      (W := W) hc hdeltaStar hW (primesUpTo W)
        hprime hPLe F hfiberHead
  have hphysical :=
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin_of_analyticLedger
      W (K0 + 1) hcPos hbetaAct logY Lambda0 mFrozen qTilde
        (by simpa only [qTilde] using Hledger)
  refine ⟨E, margin, hE, hmarginPos,
    half_pos bankPaperCanonicalSectionNinePostHeightPhysicalEta_pos, ?_⟩
  intro delta eta M
  filter_upwards [hmass, hhead, hphysical,
      eventually_secondOrderScale_pos, eventually_ge_atTop Ntail,
      eventually_ge_atTop 2] with
      n hmassN hheadN hphysicalN hscale hnTail hnTwo
  intro hdelta D hDn hDW
  subst n
  have hnD : 1 < D.n := by omega
  have hWD : D.W ≠ 0 := by omega
  have hetaPos : 0 < eta :=
    M.ratio_pos.trans_le M.ratio_le_eta
  have hw : 0 < delta + eta := by linarith
  refine ⟨hnD, hWD, hw, ?_⟩
  intro S hpattern hlo hhi
  let R := F.realization D.n hnTail
  let certificate := F.certificate D.n hnTail
  let qSource := qTilde D.n
  let target : {p : Nat // p ∈ primesUpTo W} → Real :=
    fun p =>
      ((certificate.selectorTailTarget R
        (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 : Real)
  have hqSourceLower :
      cLower * secondOrderScale D.n ≤ qSource := by
    simpa only [qSource] using hmassN.1
  have hqSourceUpper :
      qSource ≤ cUpper * secondOrderScale D.n := by
    simpa only [qSource] using hmassN.2.1
  let qn :=
    bankPaperCanonicalSmoothFinalActiveMassFamily
      bankPaperCanonicalSectionNinePostHeightPhysicalMu
        logY Lambda0 mFrozen qTilde D.n
  have hqnLower :
      cLower * secondOrderScale D.n ≤ qn := by
    simpa only [qn] using hmassN.2.2.1
  have hqnUpper :
      qn ≤ cUpper * secondOrderScale D.n := by
    simpa only [qn] using hmassN.2.2.2
  have hqSourcePos : 0 < qSource :=
    (mul_pos hcLower hscale).trans_le hqSourceLower
  have hqnPos : 0 < qn :=
    (mul_pos hcLower hscale).trans_le hqnLower
  have htargetLower :
      ∀ p, a p * secondOrderScale D.n ≤ target p := by
    intro p
    change
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
            secondOrderScale D.n ≤
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
          Real)
    simpa only [R, certificate] using (hheadN hnTail p).1
  have htargetUpper :
      ∀ p, target p ≤ b p * secondOrderScale D.n := by
    intro p
    change
      ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
          Real) ≤
        bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p.1 *
          secondOrderScale D.n
    simpa only [R, certificate] using (hheadN hnTail p).2
  have hMargins :=
    bankPaperCanonicalSectionNinePostHeight_sourceAndPostHeadMargins_of_linearBounds
      (P := primesUpTo W) E hE a b cLower cUpper
        (secondOrderScale D.n) qSource qn target target
        ha hb hcLower hcUpper hscale hqSourcePos hqnPos
        htargetLower htargetUpper htargetLower htargetUpper
        hqSourceLower hqSourceUpper hqnLower hqnUpper hElarge
  dsimp only at hMargins
  rcases hMargins with
    ⟨_hmarginPos,
      ⟨hsourceVertex, hsourceZero⟩,
      ⟨hpostVertex, hpostZero⟩⟩
  let Rhead : HeadSimplexReserve (primesUpTo W) :=
    bankPaperCanonicalSectionNineCoherentSourceHeadReserve
      E qSource target margin hE hqSourcePos hmarginPos
        hsourceVertex hsourceZero
  let Kphysical :=
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
  let Tsource :=
    bankPaperCanonicalSectionNineCoherentSourceTarget
      M D bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        hlo hhi Rhead Kphysical hdelta hnD hWD S hw
  let Bsource :=
    bankPaperCanonicalSectionNineCoherentSourceBridge
      M D bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        hlo hhi Rhead Kphysical hdelta hnD hWD S hw
  let alpha :=
    bankPaperCanonicalPostHfitBalancedAlpha
      Bsource c K0 betaProt betaAct
  refine ⟨hnTail, ?_⟩
  dsimp only
  refine ⟨Rhead, rfl, rfl, rfl, ?_, ?_⟩
  · intro p
    rfl
  · intro hmFrozenSync hlogYSync hLambda0Sync
    let q0 :=
      bankPaperCanonicalSectionNinePostHeightRoundedQ0
        (K0 + 1) Bsource R certificate deltaStar betaProt alpha qSource
    let A0 :=
      bankPaperCanonicalSectionNinePostHeightA0
        (K0 + 1) Bsource R certificate Tsource deltaStar betaProt
          alpha (betaProt + betaAct) qSource
    let d :=
      bankPaperCanonicalSmoothDIntFamily
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
          logY Lambda0 mFrozen qTilde D.n
    have hq0Family :
        q0 =
          bankPaperCanonicalSmoothQ0Family
            mFrozen qTilde D.n := by
      dsimp only [q0]
      unfold bankPaperCanonicalSectionNinePostHeightRoundedQ0
        bankPaperCanonicalTopFrozenRoundedActiveMass
        bankPaperCanonicalSmoothQ0Family
      rw [hmFrozenSync]
    have hA0Family :
        A0 =
          bankPaperCanonicalSmoothA0Family
            logY Lambda0 mFrozen qTilde D.n := by
      dsimp only [A0]
      unfold bankPaperCanonicalSectionNinePostHeightA0
        bankPaperCanonicalSmoothA0Family
        bankPaperCanonicalSmoothFrozenHeightDefect
      rw [hlogYSync, hLambda0Sync, ← hq0Family]
      rfl
    have hqnEq :
        qn = q0 - (d : Real) := by
      dsimp only [qn, d]
      unfold bankPaperCanonicalSmoothFinalActiveMassFamily
        bankPaperCanonicalSmoothDRealFamily
      rw [← hq0Family]
    have hmean :=
      bankPaperCanonicalSectionNinePostHeightPhysicalMean_eq_smoothFamilyRatio
        Bsource logY Lambda0 mFrozen qTilde q0 A0 d
          hq0Family hA0Family rfl
    have hlocalRatio :
        (A0 + (d : Real) * L D.n) / qn =
          bankPaperCanonicalSmoothFinalActiveHeightFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde D.n /
            bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde D.n := by
      calc
        (A0 + (d : Real) * L D.n) / qn =
            bankPaperCanonicalSectionNinePostHeightPhysicalMean
              Bsource q0 A0 d := by
          unfold bankPaperCanonicalSectionNinePostHeightPhysicalMean
            bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
            bankPaperCanonicalSectionNinePostHeightActiveHeight
            bankPaperCanonicalSectionNinePostHeightActiveMass
          rw [hqnEq]
          rfl
        _ =
            bankPaperCanonicalSmoothFinalActiveHeightFamily
                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                  logY Lambda0 mFrozen qTilde D.n /
              bankPaperCanonicalSmoothFinalActiveMassFamily
                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                  logY Lambda0 mFrozen qTilde D.n := hmean
    have hphysicalLocal :
        Real.log
              (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                .minus) ≤
            (A0 + (d : Real) * L D.n) / qn -
              bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
          (A0 + (d : Real) * L D.n) / qn +
                bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
            Real.log
              (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                .plus) := by
      simpa only [hlocalRatio] using hphysicalN
    have hfinite :=
      exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_coherentMargins
        (K0 := K0) M D hdelta hnD hWD S hw hlo hhi hprime R certificate
          deltaStar betaProt betaAct qSource q0 A0 qn d E margin
          hE hqSourcePos hqnPos hmarginPos hpattern
          hsourceVertex hsourceZero hpostVertex hpostZero
          hqnEq hphysicalLocal
    dsimp only at hfinite
    have hJ := hfinite (by rfl) (by rfl)
    rcases hJ with
      ⟨J, hJTsource, hJqTilde, hJexponent, hJd,
        hJbetaProt, hJbetaAct, hJq0, hJA0, hJqn,
        hJmargin, hJeta, hJpattern, hJtarget⟩
    have hqSourceActual :
        qSource =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar W (K0 + 1) betaAct := by
      simp only [qSource, qTilde,
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        dif_pos hnTail, R, certificate]
    have hJW : J.postHeightBridge.sampleData.W = W := by
      calc
        J.postHeightBridge.sampleData.W = D.W := rfl
        _ = W := hDW
    have hheadInclusion :
        primesUpTo J.postHeightBridge.sampleData.W ⊆
          primesUpTo W := by
      intro p hp
      simpa only [hJW] using hp
    have hterm := hterminal D.n hnTail
    dsimp only [R, certificate] at hterm
    refine
      ⟨J, hJTsource, hJqTilde, ?_, hJexponent, ?_,
        hJbetaProt, hJbetaAct, ?_, ?_, ?_, hJmargin, hJeta,
        hJpattern, hheadInclusion, ?_, hterm.1, hterm.2.2.1⟩
    · exact hJqTilde.trans (by
        rw [
          bankPaperCanonicalSectionNineCoherentSourceHeadReserve_activeMass]
        exact hqSourceActual)
    · simpa only [d] using hJd
    · exact hJq0.trans hq0Family
    · exact hJA0.trans hA0Family
    · simpa only [qn] using hJqn
    · intro p _hp
      exact hJtarget p

end BankPaperRealization

end

end Erdos390.WholePaper
