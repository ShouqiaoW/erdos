import Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector

/-!
# Actual-measure closure for the two-zero-cell placement

The symmetric Section 8 height change is not, in general, another scaled
`BarycentricTarget` baseline: it changes only the two physical copies of the
zero head cell.  The actual bridge therefore keeps the original scaled seed.

This file proves the missing coordinate fit for that seed.  The height loss
is `o(n / log n)`, whereas either zero-head cell has positive density.  After
uniform spreading, the loss at one tagged coordinate is consequently
absorbed by the existing protected reserve `betaProt / L`.  Every nonzero
head coordinate is unchanged.  These two facts give the literal
`BankPaperCanonicalActualActiveMeasureConstructor`.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The protected reserve absorbs a little-o cell loss -/

/-- A little-o total mass change, spread over either canonical zero-head
cell, is eventually smaller than the total protected reserve in that cell.
The statement is deliberately one-sided: only a negative change needs
absorption for coordinate fit. -/
theorem
    eventually_bankPaperCanonicalTwoZeroHeadCell_protectedAbsorption_of_littleO
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (cellChange : Nat -> Real)
    (Hchange : cellChange =o[atTop] secondOrderScale)
    {betaProt : Real} (hbetaProt : 0 < betaProt) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall sigma : PhysicalSign,
            -cellChange n <=
              (Fintype.card
                  (B.sampleData.SampleAt (none, sigma)) : Real) *
                (betaProt / B.L) := by
  let rho := bankPaperCanonicalZeroHeadCellDensityFloor Phead I
  have hrho : 0 < rho := by
    simpa only [rho] using
      bankPaperCanonicalZeroHeadCellDensityFloor_pos Phead I
  have hchange :=
    Hchange.bound (mul_pos hrho hbetaProt)
  have hdensity :=
    eventually_guarded_rawCell_density Phead I Cprom Cbank ledger
  filter_upwards [hchange, hdensity, eventually_gt_atTop 1] with
      n hchangeN hdensityN hn
  intro B hBn hsep hremaining hcanonical sigma
  have hscalePos : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hcellFinset :
      B.sampleData.cellFinset (none, sigma) =
        rawCell Phead I n (none, sigma) \
          (ledger n).guards := by
    calc
      B.sampleData.cellFinset (none, sigma) =
          (canonicalSampleData (W := B.sampleData.W)
            Phead I (ledger B.sampleData.n)
              hsep hremaining).cellFinset (none, sigma) :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.cellFinset (none, sigma))
          hcanonical
      _ = rawCell Phead I B.sampleData.n (none, sigma) \
          (ledger B.sampleData.n).guards :=
        canonicalSampleData_cellFinset
          Phead I (ledger B.sampleData.n)
            hsep hremaining (none, sigma)
      _ = rawCell Phead I n (none, sigma) \
          (ledger n).guards := by rw [hBn]
  have hcardEq :
      (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) =
        ((rawCell Phead I n (none, sigma) \
          (ledger n).guards).card : Real) := by
    rw [Fintype.card_coe, hcellFinset]
  have hcardDensity :
      rho * (n : Real) <=
        (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) := by
    have hrhoLe :
        rho <= paperCellDensity (Phead none)
            (I.lower sigma) (I.upper sigma) / 4 := by
      simpa only [rho] using
        bankPaperCanonicalZeroHeadCellDensityFloor_le
          Phead I sigma
    calc
      rho * (n : Real) <=
          (paperCellDensity (Phead none)
            (I.lower sigma) (I.upper sigma) / 4) * (n : Real) :=
        mul_le_mul_of_nonneg_right hrhoLe hnReal.le
      _ = paperCellDensity (Phead none)
          (I.lower sigma) (I.upper sigma) * (n : Real) / 4 := by
        ring
      _ <= ((rawCell Phead I n (none, sigma) \
          (ledger n).guards).card : Real) :=
        hdensityN (none, sigma)
      _ = (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) :=
        hcardEq.symm
  have hchangeAbs :
      |cellChange n| <=
        (rho * betaProt) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscalePos] using hchangeN
  have hBL : B.L = L n := by
    unfold BridgeData.L L
    rw [hBn]
  calc
    -cellChange n <= |cellChange n| := neg_le_abs _
    _ <= (rho * betaProt) * secondOrderScale n := hchangeAbs
    _ = (rho * (n : Real)) * (betaProt / L n) := by
      unfold secondOrderScale L
      ring
    _ <= (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) *
        (betaProt / L n) :=
      mul_le_mul_of_nonneg_right hcardDensity
        (div_nonneg hbetaProt.le (L_pos hn).le)
    _ = (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) *
        (betaProt / B.L) := by rw [hBL]

/-- Section 8 specialization: the literal height-only change is absorbed
by the protected reserve in both zero-head cells. -/
theorem
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_protectedAbsorption
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct mu betaProt : Real}
    (hmu : 0 < mu) (hbetaProt : 0 < betaProt)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall sigma : PhysicalSign,
            -bankPaperCanonicalSymmetricHeightCellMassFamily
                mu logY Lambda0 mFrozen qTilde n <=
              (Fintype.card
                  (B.sampleData.SampleAt (none, sigma)) : Real) *
                (betaProt / B.L) := by
  apply
    eventually_bankPaperCanonicalTwoZeroHeadCell_protectedAbsorption_of_littleO
      (Band := Band) Phead I Cprom Cbank ledger
        (bankPaperCanonicalSymmetricHeightCellMassFamily
          mu logY Lambda0 mFrozen qTilde)
        (bankPaperCanonicalSymmetricHeightCellMassFamily_isLittleO
          W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger)
        hbetaProt

/-! ## Finite coordinate fit -/

/-- On a zero-head cell, the total protected-reserve inequality is exactly
the pointwise inequality between the original scaled seed and the protected
plus rebalanced weight. -/
theorem
    bankPaperCanonicalScaledActiveSeed_le_protected_add_symmetricHeightRebalance
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
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hpool : B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1)
    (hloss :
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L)) :
    bankPaperCanonicalScaledActiveSeed T q m <=
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
          B R certificate deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m := by
  have hcard : 0 <
      (Fintype.card
        (B.sampleData.SampleAt (none, sigma)) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos (none, sigma)
  have htotalLoss :
      (d : Real) / 2 <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L) := by
    unfold bankPaperCanonicalSymmetricHeightCellMass at hloss
    linarith
  have hpointLoss :
      (d : Real) / 2 /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) <=
        betaProt / B.L := by
    apply (div_le_iff₀ hcard).2
    simpa only [mul_comm] using htotalLoss
  have hold :
      bankPaperCanonicalScaledActiveSeed T q m =
        (q * T.baseline.cellMass (none, sigma)) /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) := by
    unfold bankPaperCanonicalScaledActiveSeed BaselineAllocation.baseWeight
    rw [hcell]
    ring
  rw [
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
      B R certificate hpool,
    bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
      B.sampleData T q d m sigma hcell,
    hold]
  calc
    q * T.baseline.cellMass (none, sigma) /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) =
        (q * T.baseline.cellMass (none, sigma) - (d : Real) / 2) /
            Fintype.card (B.sampleData.SampleAt (none, sigma)) +
          (d : Real) / 2 /
            Fintype.card (B.sampleData.SampleAt (none, sigma)) := by
      ring
    _ <=
        (q * T.baseline.cellMass (none, sigma) - (d : Real) / 2) /
            Fintype.card (B.sampleData.SampleAt (none, sigma)) +
          betaProt / B.L :=
      by linarith
    _ =
        betaProt / B.L +
          (q * T.baseline.cellMass (none, sigma) - (d : Real) / 2) /
            Fintype.card (B.sampleData.SampleAt (none, sigma)) := by
      ring

/-- The final structured selector retains an arbitrary smaller protected
reserve for the original scaled seed on the guarded smooth broad pool.
The reserve lost to the two-zero-cell rebalance is charged to the positive
gap `betaProt - sigma`. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
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
    (deltaStar betaProt sigma : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hgap : 0 < betaProt - sigma)
    (hloss : forall sign : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          ((betaProt - sigma) / B.L)) :
    ∀ a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q) a <=
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q)
            (bankPaperCanonicalSymmetricHeightCellMass d)
            (bankPaperCanonicalSymmetricHeightCellMass d)) a := by
  intro a ha
  rw [
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)) ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)) ha]
  have hsigma : sigma <= betaProt := by linarith
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    rw [
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
        B.sampleData (bankPaperCanonicalScaledActiveSeed T q) hsep m,
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
        B.sampleData
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q)
            (bankPaperCanonicalSymmetricHeightCellMass d)
            (bankPaperCanonicalSymmetricHeightCellMass d))
          hsep m]
    rcases hcell : B.sampleData.cellOf m with ⟨head, sign⟩
    cases head with
    | none =>
        have hseed :=
          bankPaperCanonicalScaledActiveSeed_le_protected_add_symmetricHeightRebalance
            (K := K) B R certificate deltaStar (betaProt - sigma) T q d m sign
              hcell ha (hloss sign)
        rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate ha] at hseed
        calc
          sigma / B.L + bankPaperCanonicalScaledActiveSeed T q m <=
              sigma / B.L +
                ((betaProt - sigma) / B.L +
                  bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T q)
                    (bankPaperCanonicalSymmetricHeightCellMass d)
                    (bankPaperCanonicalSymmetricHeightCellMass d) m) :=
            by linarith
          _ = betaProt / B.L +
                bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                  (bankPaperCanonicalScaledActiveSeed T q)
                  (bankPaperCanonicalSymmetricHeightCellMass d)
                  (bankPaperCanonicalSymmetricHeightCellMass d) m := by
            ring
    | some _head =>
        have hunchanged :
            bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                (bankPaperCanonicalScaledActiveSeed T q)
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d) m =
              bankPaperCanonicalScaledActiveSeed T q m := by
          simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
            bankPaperCanonicalUniformCellIncrement, hcell]
        rw [hunchanged]
        have hdiv : sigma / B.L <= betaProt / B.L :=
          div_le_div_of_nonneg_right hsigma B.L_pos.le
        linarith
  · have hold :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hnew :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q)
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d)) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    rw [hold, hnew, add_zero]
    simpa using (div_le_div_of_nonneg_right hsigma B.L_pos.le)

/-- Section 8 eventually supplies the preceding protected-reserve
inequality with the full reserve loss charged to
`betaProt - sigma`.  The realization and certificate are quantified only
after the asymptotic index, so the statement does not require a global
family of realizations. -/
theorem
    eventually_bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar sigma : Real}
    (hmu : 0 < mu) (hgap : 0 < betaProt - sigma)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hphysical : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hphysical hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate :
              GuardedCentralAnchorCertificate c depth B.sampleData.n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth))
            (T : BarycentricTarget B.sampleData),
            B.sampleData.HeadPatternsSeparated ->
            ∀ (baseSelector : Nat -> Real) (a : Nat),
              a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar B.sampleData.W K 1 ->
              sigma / B.L +
                  bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n)) a <=
                bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                  B R certificate deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) a := by
  have hloss :=
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_protectedAbsorption
      (Band := Band) Phead I Cprom Cbank ledger W K
        (betaProt := betaProt - sigma) hmu hgap
        logY Lambda0 mFrozen qTilde Hledger
  filter_upwards [hloss] with n hlossN
  intro B hBn hphysical hremaining hcanonical
    R certificate T hsep baseSelector a ha
  apply
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
      (K := K) B R certificate deltaStar betaProt sigma baseSelector T
        (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
        (bankPaperCanonicalSmoothDIntFamily
          mu logY Lambda0 mFrozen qTilde n)
        hsep hgap
  · simpa only [bankPaperCanonicalSymmetricHeightCellMassFamily] using
      hlossN B hBn hphysical hremaining hcanonical
  · exact ha

/-- The original scaled seed has coordinate fit under the final symmetric
height placement.  The protected reserve handles the two changed zero-head
cells; all nonzero-head cells are definitionally unchanged. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit_symmetricHeight
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
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbetaProt : 0 <= betaProt)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hloss : forall sigma : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L)) :
    BankPaperCanonicalActualCoordinateFit B.sampleData T
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      q := by
  intro m
  rw [
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d))
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
    bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
      B.sampleData
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d))
        hsep m]
  rcases hcell : B.sampleData.cellOf m with ⟨head, sigma⟩
  cases head with
  | none =>
      apply
        bankPaperCanonicalScaledActiveSeed_le_protected_add_symmetricHeightRebalance
          (K := K) B R certificate deltaStar betaProt T q d m sigma hcell
      · cases sigma with
        | minus => exact hminus m hcell
        | plus => exact hplus m hcell
      · exact hloss sigma
  | some p =>
      have hunchanged :
          bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q)
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d) m =
            bankPaperCanonicalScaledActiveSeed T q m := by
        simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
          bankPaperCanonicalUniformCellIncrement, hcell]
      rw [hunchanged]
      exact le_add_of_nonneg_left
        (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
          (K := K) (deltaStar := deltaStar)
          B R certificate hbetaProt (B.sampleData.value m))

/-- Candidate support and final selector feasibility promote the preceding
coordinate fit to the full actual-active-measure constructor, still using
the original scaled seed. -/
theorem
    bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
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
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hbetaProt : 0 <= betaProt)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hloss : forall sigma : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L))
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q)
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d))) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalScaledActiveSeed T q) := by
  have hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact
      (mem_completeRoughRowFiber.mp
        (hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩))).1
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement at hplacement
  have hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <=
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q)
            (bankPaperCanonicalSymmetricHeightCellMass d)
            (bankPaperCanonicalSymmetricHeightCellMass d)) a :=
    fun a ha => (hplacement.1 a ha).1
  apply
    (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      q hsep hvalues hselectorNonneg).2
  exact ⟨hq,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit_symmetricHeight
      (K := K) B R certificate deltaStar betaProt baseSelector T q d hsep
        hbetaProt hminus hplus hloss⟩

/-- For canonical paper-head data, the finite geometry projection from the
one-shot connector discharges all four structural inputs of the symmetric
height actual-measure constructor.  The remaining hypotheses are exactly
the mass threshold, protected-reserve bounds, and the already constructed
structured placement; no selector or realization is chosen here. -/
theorem
    bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_canonicalGeometry
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    {c : Real} {depth K : Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hphysical : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : forall cell : Cell (PaperHeadSimplex.Tag P),
      (rawCell (PaperHeadSimplex.pattern P hprime E) I B.sampleData.n cell \
        (ledger B.sampleData.n).guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W)
        (PaperHeadSimplex.pattern P hprime E) I
        (ledger B.sampleData.n) hphysical hremaining)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
      (ledger B.sampleData.n) R certificate deltaStar)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q0 : Real) (d : Int)
    (hq0 : 1 <= q0) (hbetaProt : 0 <= betaProt)
    (hloss : forall sigma : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L))
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q0)
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d))) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalScaledActiveSeed T q0) := by
  obtain ⟨hheadSep, hactiveSmooth, hminus, hplus⟩ :=
    bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
      (K := K) hprime E hE I hlowerOne hupperTwo Cprom Cbank ledger
        B hhead hphysical hremaining hcanonical R certificate deltaStar
        hguardAgreement hKh hupperBroad
  exact
    bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
      (K := K) B R certificate fixed deltaStar betaProt baseSelector T q0 d
        hq0 hheadSep hactiveSmooth hbetaProt hminus hplus hloss Hplacement

/-! ## Exact baseline seed on the actual-mass bridge -/

/-- The lower-level active-mass bridge can be constructed from `q > 0`
before `Hmeasure` is known, so there is no circularity.  Its baseline weight
is definitionally the original scaled seed, closing the endpoint consumer's
`hseed` argument. -/
@[simp] theorem
    bankPaperCanonicalActiveMassBridgeData_baseWeight_scaledSeed
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Erdos390.Full.RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : Erdos390.Full.RegularMeshPrimeCutoffs.ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta)
    (m : D.Sample) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).baseline.baseWeight m =
        bankPaperCanonicalScaledActiveSeed T q m := by
  rw [bankPaperCanonicalActiveMassBridgeData_baseline,
    T.activeMassBaseline_baseWeight]
  rfl

/-! ## Eventual Section 8 inputs for the finite constructor -/

/-- The analytic ledger simultaneously gives the constructor threshold
`q0 >= 1` and the protected absorption inequality.  These are exactly the
two asymptotic inputs needed by the finite actual-measure theorem above. -/
theorem
    eventually_bankPaperCanonicalSymmetricHeight_actualMeasureInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct mu betaProt : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmu : 0 < mu) (hbetaProt : 0 < betaProt)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalSmoothQ0Family mFrozen qTilde n ∧
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall sigma : PhysicalSign,
            -bankPaperCanonicalSymmetricHeightCellMass
                (bankPaperCanonicalSmoothDIntFamily
                  mu logY Lambda0 mFrozen qTilde n) <=
              (Fintype.card
                  (B.sampleData.SampleAt (none, sigma)) : Real) *
                (betaProt / B.L) := by
  have hqLower :=
    bankPaperCanonicalSectionEight_q0_paperScaleLower
      W K hc hbeta logY Lambda0 mFrozen qTilde Hledger
  have hqOne :=
    eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) hqLower
  have hloss :=
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_protectedAbsorption
      (Band := Band) Phead I Cprom Cbank ledger W K hmu hbetaProt
        logY Lambda0 mFrozen qTilde Hledger
  filter_upwards [hqOne, hloss] with n hqN hlossN
  refine ⟨hqN, ?_⟩
  simpa only [bankPaperCanonicalSymmetricHeightCellMassFamily] using hlossN

/-- Paper-facing composition of the asymptotic inputs with the finite
constructor.  Once the one-shot placement has supplied smooth support,
zero-cell pool membership, and selector feasibility, `Hmeasure` is a
theorem for the original initialized scaled seed.  The realization and
certificate are pointwise data after the asymptotic index, so no global
realization family is required. -/
theorem
    eventually_bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_placement
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmu : 0 < mu) (hbetaProt : 0 < betaProt)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate :
              GuardedCentralAnchorCertificate c depth B.sampleData.n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth))
            (T : BarycentricTarget B.sampleData),
            B.sampleData.HeadPatternsSeparated ->
            forall (fixed : Finset Nat) (baseSelector : Nat -> Real),
              bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
                  R.roughCanonicalGuardedRow
                    certificate deltaStar K 1 ->
              (forall m : B.sampleData.Sample,
                B.sampleData.cellOf m = (none, .minus) ->
                  B.sampleData.value m ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar
                      B.sampleData.W K 1) ->
              (forall m : B.sampleData.Sample,
                B.sampleData.cellOf m = (none, .plus) ->
                  B.sampleData.value m ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar
                      B.sampleData.W K 1) ->
              BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
                  B R certificate
                  fixed deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) ->
                BankPaperCanonicalActualActiveMeasureConstructor
                  B.sampleData T
                  (R.roughCanonicalGuardedCandidateSet
                    certificate deltaStar K)
                  (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                    B R certificate
                    deltaStar betaProt baseSelector
                    (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                      (bankPaperCanonicalScaledActiveSeed T
                        (bankPaperCanonicalSmoothQ0Family
                          mFrozen qTilde n))
                      (bankPaperCanonicalSymmetricHeightCellMass
                        (bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n))
                      (bankPaperCanonicalSymmetricHeightCellMass
                        (bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n))))
                  (bankPaperCanonicalScaledActiveSeed T
                    (bankPaperCanonicalSmoothQ0Family
                      mFrozen qTilde n)) := by
  have hinputs :=
    eventually_bankPaperCanonicalSymmetricHeight_actualMeasureInputs
      (Band := Band) Phead I Cprom Cbank ledger W K hc hbeta hmu hbetaProt
        logY Lambda0 mFrozen qTilde Hledger
  filter_upwards [hinputs] with n hinputsN
  intro B hBn hsep hremaining hcanonical R certificate T hheadSep
    fixed baseSelector hactiveSmooth hminus hplus Hplacement
  exact
    bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
      (K := K) B R certificate
      fixed deltaStar betaProt baseSelector T
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      (bankPaperCanonicalSmoothDIntFamily
        mu logY Lambda0 mFrozen qTilde n)
      hinputsN.1 hheadSep hactiveSmooth hbetaProt.le hminus hplus
      (hinputsN.2 B hBn hsep hremaining hcanonical) Hplacement

/-- Fixed-ledger specialization of the paper-facing actual-measure
constructor.  Its canonical-sample hypotheses now use the same
realization-independent relevant-ledger family as the one-shot
specialization, so an `Hplacement` produced there can be passed here without
another ledger identification. -/
theorem
    eventually_bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_placement_relevantLedgerFamily
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmu : 0 < mu) (hbetaProt : 0 < betaProt)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (roughCanonicalBridgeRelevantLedgerFamily
                depth B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I
                (roughCanonicalBridgeRelevantLedgerFamily
                  depth B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate :
              GuardedCentralAnchorCertificate c depth B.sampleData.n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth))
            (T : BarycentricTarget B.sampleData),
            B.sampleData.HeadPatternsSeparated ->
            forall (fixed : Finset Nat) (baseSelector : Nat -> Real),
              bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
                  R.roughCanonicalGuardedRow
                    certificate deltaStar K 1 ->
              (forall m : B.sampleData.Sample,
                B.sampleData.cellOf m = (none, .minus) ->
                  B.sampleData.value m ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar
                      B.sampleData.W K 1) ->
              (forall m : B.sampleData.Sample,
                B.sampleData.cellOf m = (none, .plus) ->
                  B.sampleData.value m ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar
                      B.sampleData.W K 1) ->
              BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
                  B R certificate
                  fixed deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) ->
                BankPaperCanonicalActualActiveMeasureConstructor
                  B.sampleData T
                  (R.roughCanonicalGuardedCandidateSet
                    certificate deltaStar K)
                  (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                    B R certificate
                    deltaStar betaProt baseSelector
                    (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                      (bankPaperCanonicalScaledActiveSeed T
                        (bankPaperCanonicalSmoothQ0Family
                          mFrozen qTilde n))
                      (bankPaperCanonicalSymmetricHeightCellMass
                        (bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n))
                      (bankPaperCanonicalSymmetricHeightCellMass
                        (bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n))))
                  (bankPaperCanonicalScaledActiveSeed T
                    (bankPaperCanonicalSmoothQ0Family
                      mFrozen qTilde n)) := by
  exact
    eventually_bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_placement
      (P := P) (Band := Band) (c := c) (betaAct := betaAct)
      (mu := mu) (betaProt := betaProt) (deltaStar := deltaStar)
      Phead I 2 0 (roughCanonicalBridgeRelevantLedgerFamily depth)
      depth W K hc hbeta hmu hbetaProt
      logY Lambda0 mFrozen qTilde Hledger

end BankPaperRealization

end

end Erdos390.WholePaper
