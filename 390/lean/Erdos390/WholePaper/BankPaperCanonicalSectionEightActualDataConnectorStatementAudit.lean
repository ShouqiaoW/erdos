import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector

/-! # Statement audit for the actual-data Section 8 connector -/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

example
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenTotalMass
          D fixed bankBase candidates preSelector activeSeed +
        bankPaperCanonicalLiteralActiveMass D activeSeed =
      (fixed.card : Real) + (bankBase.card : Real) +
        ∑ a ∈ candidates, preSelector a :=
  bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
    D T fixed bankBase candidates preSelector activeSeed H

example
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (fixed bankBase candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (h logY : Nat -> Real)
    (Hconstructor : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (Hestimates : BankPaperCanonicalActualFrozenBaselineEstimates
      D fixed bankBase candidates preSelector activeSeed h logY) :
    BankPaperCanonicalFrozenBaselineSourceLedger
      h logY
      (bankPaperCanonicalActualFrozenLogMassFamily
        D fixed bankBase candidates preSelector activeSeed)
      (bankPaperCanonicalActualFrozenTotalMassFamily
        D fixed bankBase candidates preSelector activeSeed)
      (bankPaperCanonicalLiteralQMass D activeSeed) :=
  bankPaperCanonicalFrozenBaselineSourceLedger_of_actualData
    D T fixed bankBase candidates preSelector activeSeed h logY
      Hconstructor Hestimates

example
    (bankBase : Nat -> Finset Nat)
    (hcardBound : ∀ᶠ n : Nat in atTop,
      (bankBase n).card <= bankPaperAnchorMarkerBudget n) :
    (fun n => ((bankBase n).card : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) :=
  BankPaperRealization.prechargeBaseState_card_family_isBigO_secondOrderScale_div_L
    bankBase hcardBound

example
    {c : Real} (hc : 0 < c)
    (bankBase : Nat -> Finset Nat)
    (hcardBound : ∀ᶠ n : Nat in atTop,
      (bankBase n).card <= bankPaperAnchorMarkerBudget n)
    (hsupport : ∀ᶠ n : Nat in atTop,
      ∀ a ∈ bankBase n,
        n < a ∧ a <= upperEndpoint n (upperTailLength c n)) :
    (fun n => ∑ a ∈ bankBase n,
      Real.log (a : Real)) =O[atTop] secondOrderScale :=
  BankPaperRealization.prechargeBaseState_logMassFamily_isBigO_secondOrderScale
    hc bankBase hcardBound hsupport

example
    (depth W K poolMinimum : Nat)
    {c betaAct deltaStar mu : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar) (hmu : 0 < mu)
    (fixed bankBase candidates : Nat -> Finset Nat)
    (initialSelector finalSelector : Nat -> Nat -> Real)
    (mFrozen qTilde logY Lambda0 : Nat -> Real)
    (HbaselineMass : BankPaperCanonicalActualSelectorMassEstimate c
      fixed bankBase candidates initialSelector)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family logY Lambda0
        mFrozen qTilde))
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      ∃ Rn : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)),
      ∃ certn : GuardedCentralAnchorCertificate c depth n
          Rn.anchorGuardLeftCore Rn.anchorGuardRightCore
          (Rn.centralChangedMarkers depth),
        fixed n = Rn.paperFixedExceptionalFactors deltaStar ∧
        bankBase n = Rn.prechargeBaseState ∧
        candidates n =
          Rn.roughCanonicalGuardedCandidateSet certn deltaStar K ∧
        mFrozen n =
          Rn.bankPaperCanonicalInitialSmoothFrozenMass
            (K := K) certn deltaStar (initialSelector n) (qTilde n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) Rn certn deltaStar (initialSelector n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) Rn certn deltaStar (finalSelector n) ∧
        BankPaperCanonicalGuardedSmoothFlexibleQuota
          Rn certn deltaStar K (finalSelector n)
          (bankPaperCanonicalSmoothFlexibleQuotaAt
            (mFrozen n) (qTilde n)
            (Int.ofNat
              (completeLabelMultiplicity (yNat n) (fixed n) 1 +
                completeLabelMultiplicity (yNat n) (bankBase n) 1))
            (bankPaperCanonicalSmoothDIntFamily
              mu logY Lambda0 mFrozen qTilde n))) :
    BankPaperCanonicalActualSelectorMassEstimate c
      fixed bankBase candidates finalSelector :=
  BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_constructedSmoothQuota
    depth W K poolMinimum hc hdelta hmu fixed bankBase candidates
    initialSelector finalSelector mFrozen qTilde logY Lambda0
    HbaselineMass Hledger Hconstructed

section SameFamilyConstructedContract

variable {Head : Type*} [Fintype Head] [Nonempty Head]
variable {c betaAct deltaStar mu : Real} {N : Nat}
variable (depth W K : Nat)
variable (F : BankPaperCanonicalGuardedTailFamily c depth N)
variable (D : Nat → StructuredSampleData Head)
variable (T : ∀ n, BarycentricTarget (D n))
variable (fixed bankBase candidates : Nat → Finset Nat)
variable (initialSelector finalSelector : Nat → Nat → Real)
variable (mFrozen : Nat → Real)

/- The constructed terminal must use the same guarded tail-family witness
for the analytic mass, both row realizations, and the smooth quota. -/
#check
  let guardedBase : Nat → Real :=
    F.extendedGuardedSmoothBaseMass W K betaAct deltaStar
  let activeSeed : ∀ n, (D n).Sample → Real := fun n =>
    bankPaperCanonicalScaledActiveSeed (T n) (guardedBase n)
  let initialLambda : Nat → Real :=
    bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates initialSelector activeSeed
  fun
    (hc : 0 < c) (hdelta : 0 < deltaStar) (hmu : 0 < mu)
    (poolMinimum : Nat)
    HinitialConstructor HfinalConstructor Hbaseline
    (HinitialMass : BankPaperCanonicalActualSelectorMassEstimate
      c fixed bankBase candidates initialSelector)
    (Hconstructed : ∀ᶠ n : Nat in atTop,
      ∃ hn : N ≤ n,
        fixed n =
            (F.realization n hn).paperFixedExceptionalFactors deltaStar ∧
        bankBase n = (F.realization n hn).prechargeBaseState ∧
        candidates n =
          (F.realization n hn).roughCanonicalGuardedCandidateSet
            (F.certificate n hn) deltaStar K ∧
        mFrozen n =
          (F.realization n hn).bankPaperCanonicalInitialSmoothFrozenMass
            (K := K) (F.certificate n hn) deltaStar (initialSelector n)
              (guardedBase n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) (F.realization n hn) (F.certificate n hn)
              deltaStar (initialSelector n) ∧
        BankPaperCanonicalChargedNonsmoothRowRealization
            (K := K) (F.realization n hn) (F.certificate n hn)
              deltaStar (finalSelector n) ∧
        BankPaperCanonicalGuardedSmoothFlexibleQuota
          (F.realization n hn) (F.certificate n hn) deltaStar K
          (finalSelector n)
          (bankPaperCanonicalSmoothFlexibleQuotaAt
            (mFrozen n) (guardedBase n)
            (Int.ofNat
              (completeLabelMultiplicity (yNat n) (fixed n) 1 +
                completeLabelMultiplicity (yNat n) (bankBase n) 1))
            (bankPaperCanonicalSmoothDIntFamily mu
              (bankPaperCanonicalCentralTailLogTarget c)
              initialLambda mFrozen guardedBase n)))
    (Hgeometry : BankPaperCanonicalActualFrozenIntervalGeometry
      (c := c) fixed bankBase candidates) =>
    And.intro
      (bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_selectorMass_intervalGeometry
        hc hdelta hmu depth W K poolMinimum F D T fixed bankBase candidates
          initialSelector finalSelector mFrozen HinitialConstructor
          HfinalConstructor HinitialMass Hconstructed Hgeometry)
      (bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_intervalGeometry
        hc hdelta hmu depth W K poolMinimum F D T fixed bankBase candidates
          initialSelector finalSelector mFrozen HinitialConstructor
          HfinalConstructor Hbaseline Hconstructed Hgeometry)

end SameFamilyConstructedContract

/-! ## Complete public declaration census -/

#check bankPaperCanonicalActualFrozenTotalMass
#check bankPaperCanonicalActualFrozenLogMass
#check bankPaperCanonicalActualFrozenTotalMass_eq
#check bankPaperCanonicalActualFrozenTotalMass_add_literalActiveMass_eq
#check bankPaperCanonicalActualFrozenTotalMassFamily
#check bankPaperCanonicalActualFrozenLogMassFamily
#check bankPaperCanonicalUpperTailHeight
#check bankPaperCanonicalCentralTailLogTarget
#check bankPaperCanonicalCentralTailLog_eq_sum
#check bankPaperCanonicalCentralTailLog_sub_height_mul_L_eq_sum
#check bankPaperCanonicalFactorLog_sub_L_mem_Icc
#check bankPaperCanonicalUpperTailHeight_isBigO
#check bankPaperCanonicalCentralTailLogTarget_sub_height_mul_L_isBigO
#check bankPaperCanonicalActualFrozenWeight_nonneg
#check bankPaperCanonicalActualFrozenTotalMass_nonneg
#check bankPaperCanonicalActualFrozenLogMass_sub_total_mul
#check BankPaperCanonicalActualFrozenIntervalGeometry
#check BankPaperCanonicalActualSelectorMassEstimate
#check bankPaperCanonicalActualSelectorMassEstimate_of_frozenBaselineSource
#check BankPaperCanonicalChargedNonsmoothRowRealization
#check sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
#check card_cast_eq_sum_completeLabelMultiplicity_of_labelSet_subset
#check bankPaperCanonicalChargedLabelSet
#check bankPaperCanonical_chargedSelectorMass_sub_height_eq_neg_smoothDiscrepancy
#check bankPaperCanonical_chargedSelectorMass_sub_height_eq_rawSmoothLedger
#check BankPaperRealization.bankPaperCanonicalInitialSmoothFrozenMass
#check BankPaperRealization.roughCanonicalSmoothPreinitialMismatch_eq_neg_chargedMassError
#check BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_exists_chargedMassIdentity
#check BankPaperRealization.roughCanonicalPostchargeRowDiscrepancy_eq_constructedSmoothLedger
#check BankPaperRealization.abs_roughCanonicalPostchargeRowDiscrepancy_le_of_constructedSmoothQuota
#check @BankPaperRealization.bankPaperCanonicalActualSelectorMassEstimate_of_constructedSmoothQuota
#check bankPaperCanonical_secondOrderScale_div_L_isBigO_secondOrderScale
#check bankPaperAnchorMarkerBudget_isBigO_secondOrderScale_div_L
#check BankPaperRealization.prechargeBaseState_card_family_isBigO_secondOrderScale_div_L
#check BankPaperRealization.prechargeBaseState_logMassFamily_isBigO_secondOrderScale
#check bankPaperCanonicalActualFrozenTotalMassFamily_isBigO
#check bankPaperCanonicalActualFrozenLogMassFamily_centered_isBigO
#check BankPaperCanonicalActualGuardedSmoothMassEstimate
#check bankPaperCanonicalGuardedSmoothCorrectionEstimate_of_actualData
#check bankPaperCanonicalActualGuardedSmoothMassEstimate_scaledActiveSeed
#check BankPaperCanonicalActualFrozenBaselineEstimates
#check bankPaperCanonicalActualFrozenBaselineEstimates_of_intervalGeometry
#check BankPaperCanonicalSectionEightActualDataSourceLedger
#check BankPaperCanonicalSectionEightScaledActualDataSourceLedger
#check bankPaperCanonicalSectionEightScaledActualDataSourceLedger_of_intervalGeometry
#check bankPaperCanonicalFrozenBaselineSourceLedger_of_actualData
-- These five analytic connectors consume an honest guarded tail family.
#check @bankPaperCanonicalSectionEightAnalyticLedger_of_actualData
#check @bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData
#check @bankPaperCanonicalSectionEightAnalyticLedger_of_scaledActualData_intervalGeometry
#check @bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_selectorMass_intervalGeometry
#check @bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_intervalGeometry

end

end Erdos390.WholePaper
