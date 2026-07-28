import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector

/-!
# Synchronization of the two frozen smooth-row masses

Section 8 records the frozen smooth mass by subtracting the literal active
seed mass from the initial selector.  The frozen-top source records the same
quantity directly as the protected raw mass on the guarded smooth row.

For the scaled barycentric seed these definitions agree exactly.  The two
charged label-one multiplicities vanish in the paper range, while the
guarded-row source identity contributes precisely `q` units of active mass.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- The row-local Section 8 frozen mass of the literal scaled-seed source is
the frozen-top protected raw mass. -/
theorem bankPaperCanonicalInitialSmoothFrozenMass_eq_topFrozenSmoothFrozenMass_of_scaledSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal q : Real)
    (hn : 0 < B.sampleData.n)
    (hdeltaUpper : deltaStar <= 1)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
        certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
            B R certificate deltaStar betaProt alpha betaTotal
              (bankPaperCanonicalScaledActiveSeed T q)) q =
      bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
        B R certificate deltaStar betaProt alpha := by
  have hsum :=
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
        (alpha := alpha) (beta := betaTotal) B R certificate
        (bankPaperCanonicalScaledActiveSeed T q) hvalues
  have hsum' :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a) =
        bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K)
            B R certificate deltaStar betaProt alpha + q := by
    simpa only [bankPaperCanonicalTopFrozenSmoothFrozenMass,
      bankPaperCanonicalLiteralActiveMass_scaledActiveSeed] using hsum
  unfold BankPaperRealization.bankPaperCanonicalInitialSmoothFrozenMass
  rw [R.paperFixedExceptionalFactors_completeLabelMultiplicity_one_eq_zero
      hn hdeltaUpper,
    R.prechargeBaseState_completeLabelMultiplicity_one_eq_zero]
  norm_num
  linarith

end BankPaperRealization

end

end Erdos390.WholePaper
