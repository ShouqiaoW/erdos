import Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement

/-!
# Statement audit for guarded smooth additive placement

The public inventory includes the minimal source-state interface used before
Proposition 8.7.  The finite-algebra block audits the literal two zero-head cells,
their integer mass change, the structured head-cell moments, the corrected
signed whole-smooth-row ledger, and the exact support boundary.  The
expanded example records the minimized preselector interface consumed by
the actual Proposition 8.7 endpoint.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

#check BankPaperRealization.BankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalUniformCellIncrement
#check BankPaperRealization.sum_bankPaperCanonicalUniformCellIncrement
#check BankPaperRealization.bankPaperCanonicalTwoZeroHeadCellRebalance
#check BankPaperRealization.sum_bankPaperCanonicalTwoZeroHeadCellRebalance_sub
#check BankPaperRealization.bankPaperCanonicalLiteralActiveMass_twoZeroHeadCellRebalance
#check BankPaperRealization.bankPaperCanonicalLiteralActiveMass_rebalancedScaledActiveSeed
#check BankPaperRealization.bankPaperCanonicalActiveSeedAmbientWeight_sub
#check BankPaperRealization.sum_bankPaperCanonicalActiveSeedAmbientWeight_of_changeSupport
#check BankPaperRealization.bankPaperCanonicalTwoZeroHeadCellRebalance_changeSupport
#check BankPaperRealization.sum_bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub
#check BankPaperRealization.factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_headPrime
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger_of_rowChange
#check BankPaperRealization.bankPaperCanonicalTwoZeroHeadCellSourceSelector
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothAdditivePrebridgeMomentLedger_twoZeroHeadCells
#check BankPaperRealization.sum_baselineBaseWeight_mul_cellFunction
#check BankPaperRealization.sum_bankPaperCanonicalScaledActiveSeed_mul_headFunction
#check BankPaperRealization.sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
#check BankPaperRealization.sum_bankPaperCanonicalScaledActiveSeed_mul_paperHeadValuation
#check BankPaperRealization.sum_bankPaperCanonicalScaledActiveSeedAmbient_mul_paperHeadValuation
#check BankPaperRealization.bankPaperCanonicalStructuredHeadCellMomentLedger
#check BankPaperRealization.sum_bankPaperCanonicalUniformZeroHeadCellIncrement_mul_valuation_eq_zero
#check BankPaperRealization.sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
#check BankPaperRealization.sum_bankPaperCanonicalRebalancedScaledActiveSeed_mul_paperHeadValuation
#check BankPaperRealization.not_all_paperHeadSimplex_values_mem_guardedBroadCorrectionPool
#check BankPaperRealization.bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
#check BankPaperRealization.BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_eq_zero_of_yNat_lt
#check BankPaperRealization.sum_guardedCandidates_structuredAdditivePlacement_factorization_sub_base_eq_moment
#check BankPaperRealization.bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
#check BankPaperRealization.bankPaperCanonicalSelectorRowIntegral_structuredAdditivePlacement_of_prebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_structuredAdditivePlacement_of_prebridgeMomentLedger
#check BankPaperRealization.BankPaperCanonicalSelectorSourceState
#check BankPaperRealization.bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
#check BankPaperRealization.BankPaperCanonicalGuardedStructuredAdditivePlacement
#check BankPaperRealization.bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
#check BankPaperRealization.BankPaperCanonicalGuardedSmoothAdditivePlacement
#check BankPaperRealization.bankPaperCanonicalSelectorRowIntegral_additiveRefinement_of_prebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalSelectorDeficitSupportedOnPrimeBand_additiveRefinement_of_prebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothAdditivePlacement_of_prebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothAdditivePlacement_of_roundedSelector_prebridgeMomentLedger
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothAdditivePlacement_of_zeroMomentLedger
#check exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
#check BankPaperRealization.bankPaperCanonicalGuardedSmoothFlexibleQuota_actualP87Endpoint_of_additiveRowChange
#check BankPaperRealization.exists_bankPaperCanonicalActualP87EndpointSelector_of_additivePlacement
#check BankPaperRealization.exists_bankPaperCanonicalActualP87EndpointSelector_of_structuredAdditivePlacement

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hpreRow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector)
    (hpreSupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int)
    (Hfit : B.HasPaperProposition87Conclusion Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate
        fixed candidates preSelector activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight
        B.sampleData candidates preSelector activeSeed)
      quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ path : Real -> B.ParamSpace, ∃ endpoint : Nat -> Real,
      B.IsPaperProposition87Path Delta radius
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed)
        N Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota path ∧
      endpoint = bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path ∧
      bankPaperProposition87SelectorSupport B
        (bankPaperCanonicalActualFrozenValue (candidates := candidates)) =
          candidates ∧
      (forall p : Nat,
        bankPaperProposition87FullMarkedTarget
            (bankPaperCanonicalActualFrozenValue (candidates := candidates))
            (bankPaperCanonicalActualFrozenWeight
              B.sampleData candidates preSelector activeSeed)
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed) p =
          ((certificate.selectorTailTarget R fixed).factorization p : Real)) ∧
      (forall x, x ∉ candidates -> endpoint x = 0) ∧
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
          B.partition.band cellIndex)
        endpoint :=
  exists_bankPaperCanonicalActualP87EndpointSelector_of_rowIntegral_deficitSupported
    B R certificate fixed candidates preSelector activeSeed Hmeasure hseed
    hpreRow hpreSupport Delta radius N Cpost quota Hfit cellIndex

end

end Erdos390.WholePaper
