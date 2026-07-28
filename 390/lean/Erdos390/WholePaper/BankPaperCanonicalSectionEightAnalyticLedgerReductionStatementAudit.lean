import Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction

/-! # Statement audit for the reduced Section 8 analytic ledger -/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real) :
    bankPaperCanonicalRawSmoothBaseMass W n h K betaAct -
        bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar W K betaAct =
      betaAct / L n *
        ((bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
          deltaStar W K).card : Real) :=
  bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
    R certificate deltaStar W K betaAct

example (h logY Lambda0 m0 mFrozen qTilde : Nat -> Real)
    (Hsource : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde
      =O[atTop] secondOrderScale :=
  bankPaperCanonicalSmoothA0Family_isBigO_of_baselineSource
    h logY Lambda0 m0 mFrozen qTilde Hsource

example (betaAct : Real)
    (rawBase guardedBase qTilde deletedCard : Nat -> Real)
    (h logY Lambda0 m0 mFrozen : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hsource : BankPaperCanonicalSectionEightAnalyticSourceLedger
      guardedBase qTilde deletedCard h logY Lambda0 m0) :
    BankPaperCanonicalSectionEightAnalyticLedger rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) :=
  bankPaperCanonicalSectionEightAnalyticLedger_of_sourceLedger
    betaAct rawBase guardedBase qTilde deletedCard h logY Lambda0 m0
      mFrozen hidentity Hsource

/-! ## Complete public declaration census -/

#check bankPaperCanonicalSmoothBaseGuardDeletionPool
#check bankPaperCanonicalGuardedSmoothBaseMass
#check bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
#check bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchors
#check bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
#check bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
#check bankPaperCanonicalSmoothResidualAnchorPool
#check guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
#check bankPaperCanonicalSmoothResidualAnchorPool_card_le
#check guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
#check bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
#check BankPaperCanonicalGuardedTailFiber
#check BankPaperCanonicalGuardedTailFamily
#check BankPaperCanonicalGuardedTailFamily.mk
#check BankPaperCanonicalGuardedTailFamily.fiber
#check BankPaperCanonicalGuardedTailFamily.realization
#check BankPaperCanonicalGuardedTailFamily.certificate
#check BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass
#check BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard
#check BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard
#check bankPaperCanonicalSmoothGuardCensusEnvelope
#check bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg
#check bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale
#check bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO
#check guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
#check BankPaperCanonicalSmoothGuardDeletionCensus
#check bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
#check bankPaperCanonical_beta_div_L_isBigO_one
#check bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
#check BankPaperCanonicalGuardedSmoothCorrectionEstimate
#check bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
#check bankPaperCanonicalRawSmoothBase_sub_qTilde_isLittleO_of_guardedReduction
#check BankPaperCanonicalFrozenBaselineSourceLedger
#check bankPaperCanonical_one_isBigO_secondOrderScale_div_L
#check bankPaperCanonicalSmoothQ0_baselineMassError_isBigO
#check bankPaperCanonicalSmoothQ0_baselineMassError_mul_L_isBigO
#check bankPaperCanonicalSmoothA0Family_isBigO_of_baselineSource
#check BankPaperCanonicalSectionEightAnalyticSourceLedger
#check bankPaperCanonicalSectionEightAnalyticLedger_of_sourceLedger
#check bankPaperCanonicalSectionEightAnalyticLedger_of_literalGuardedSource
#check bankPaperCanonicalSectionEightAnalyticLedger_of_literalAnchorSource
#check bankPaperCanonicalSectionEightAnalyticLedger_of_correctionAndBaseline

end

end Erdos390.WholePaper
