import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellMeasureConnector

/-!
# Proposition 8.7 fit inputs for the two-zero-cell placement

This file discharges the finite inputs of the actual Proposition 8.7 call
which are forced by the already constructed placement.

There is one quantitative distinction which matters.  The final structured
placement uses the rebalanced seed, whereas the actual bridge keeps the
original scaled seed.  Consequently its frozen remainder is not literally
`betaProt / L` on a changed zero-head coordinate.  It is

`protected + rebalanced - original`.

The height increment is little-o of `n / log n`.  Applying the existing
cell-absorption theorem to its negative gives the missing upper estimate,
and hence the uniform frozen ledger `(betaProt + 1) / L`.

The final adapter also derives the integer quota, ambient frozen
feasibility, the choice `N = B.q`, the mass bound with `Cmass = 1`, and the
conversion of the selector residual into the literal initial marked
residual.  The target envelope, the primewise selector-residual rate, and
the active-coordinate `Cactive / L` estimate remain visible: the current
prebridge ledger deliberately does not constrain medium-prime moments, and
no uniform all-cell active-coordinate bound is hidden here.
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

/-! ## The missing upper half of the frozen height ledger -/

/-- The symmetric height increment is eventually at most one protected
unit per coordinate in either zero-head cell.  This is the upper analogue
of protected absorption, obtained by applying that theorem to the negative
height family. -/
theorem
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_upperAbsorption
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct mu : Real}
    (hmu : 0 < mu)
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
            bankPaperCanonicalSymmetricHeightCellMass
                (bankPaperCanonicalSmoothDIntFamily
                  mu logY Lambda0 mFrozen qTilde n) <=
              (Fintype.card
                  (B.sampleData.SampleAt (none, sigma)) : Real) *
                ((1 : Real) / B.L) := by
  have hchange :
      bankPaperCanonicalSymmetricHeightCellMassFamily
          mu logY Lambda0 mFrozen qTilde =o[atTop]
        secondOrderScale :=
    bankPaperCanonicalSymmetricHeightCellMassFamily_isLittleO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hupper :=
    eventually_bankPaperCanonicalTwoZeroHeadCell_protectedAbsorption_of_littleO
      (Band := Band)
      Phead I Cprom Cbank ledger
      (fun n =>
        -bankPaperCanonicalSymmetricHeightCellMassFamily
          mu logY Lambda0 mFrozen qTilde n)
      hchange.neg_left (by norm_num : (0 : Real) < 1)
  filter_upwards [hupper] with n hn
  intro B hBn hsep hremaining hcanonical sigma
  have hsigma := hn B hBn hsep hremaining hcanonical sigma
  simpa only [bankPaperCanonicalSymmetricHeightCellMassFamily,
    neg_neg] using hsigma

/-- Finite frozen-ledger estimate for the actual old seed.  A supplied
upper bound `cellMass <= card * gamma / L` controls the difference between
the rebalanced placement seed and the original scaled bridge seed. -/
theorem
    bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
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
    (deltaStar betaProt : Real) (hbetaProt : 0 <= betaProt)
    (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalScaledActiveSeed T q))
    (gamma : Real)
    (hgamma : 0 <= gamma)
    (hcellUpper : forall sigma : PhysicalSign,
      bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (gamma / B.L)) :
    forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                (bankPaperCanonicalScaledActiveSeed T q)
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d)))
            (bankPaperCanonicalScaledActiveSeed T q))
          (B.sampleData.value m) <=
        (betaProt + gamma) / B.L := by
  intro m
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight,
    if_pos (bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m),
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
      B R certificate baseSelector
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
        (bankPaperCanonicalSymmetricHeightCellMass d)) hsep m,
    bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
      B.sampleData (bankPaperCanonicalScaledActiveSeed T q) hsep m]
  have hprotected :
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
          B R certificate deltaStar betaProt (B.sampleData.value m) <=
        betaProt / B.L := by
    by_cases hpool : B.sampleData.value m ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
        (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
        B R certificate hpool]
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
        B R certificate hpool]
      exact div_nonneg hbetaProt B.L_pos.le
  have hchange :
      bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m -
        bankPaperCanonicalScaledActiveSeed T q m <= gamma / B.L := by
    rcases hcell : B.sampleData.cellOf m with ⟨head, sigma⟩
    cases head with
    | none =>
        have hcard : 0 <
            (Fintype.card
              (B.sampleData.SampleAt (none, sigma)) : Real) := by
          exact_mod_cast B.sampleData.sampleAt_card_pos (none, sigma)
        have hscaled :
            bankPaperCanonicalSymmetricHeightCellMass d /
                Fintype.card (B.sampleData.SampleAt (none, sigma)) <=
              gamma / B.L := by
          apply (div_le_iff₀ hcard).2
          simpa only [mul_comm] using hcellUpper sigma
        calc
          bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                (bankPaperCanonicalScaledActiveSeed T q)
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d) m -
              bankPaperCanonicalScaledActiveSeed T q m =
            bankPaperCanonicalSymmetricHeightCellMass d /
              Fintype.card
                (B.sampleData.SampleAt (none, sigma)) := by
              rw [
                bankPaperCanonicalSymmetricHeightRebalance_apply_of_zeroHeadCell
                  B.sampleData T q d m sigma hcell]
              unfold bankPaperCanonicalScaledActiveSeed
                BaselineAllocation.baseWeight
                bankPaperCanonicalSymmetricHeightCellMass
              rw [hcell]
              ring
          _ <= gamma / B.L := hscaled
    | some head =>
        simpa [bankPaperCanonicalTwoZeroHeadCellRebalance,
          bankPaperCanonicalUniformCellIncrement, hcell] using
          (div_nonneg hgamma B.L_pos.le)
  calc
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
          B R certificate deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q)
            (bankPaperCanonicalSymmetricHeightCellMass d)
            (bankPaperCanonicalSymmetricHeightCellMass d) m -
          bankPaperCanonicalScaledActiveSeed T q m <=
        betaProt / B.L + gamma / B.L :=
      by linarith
    _ = (betaProt + gamma) / B.L := by ring

/-- Section 8 specialization of the finite frozen estimate.  The analytic
ledger supplies `gamma = 1` eventually.  The realization and certificate
are pointwise data after the asymptotic index, so no global realization
family is required. -/
theorem
    eventually_bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar : Real}
    (hmu : 0 < mu) (hbetaProt : 0 <= betaProt)
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
            (T : BarycentricTarget B.sampleData)
            (baseSelector : Nat -> Real),
            let q :=
              bankPaperCanonicalSmoothQ0Family mFrozen qTilde n
            let d :=
              bankPaperCanonicalSmoothDIntFamily
                mu logY Lambda0 mFrozen qTilde n
            BankPaperCanonicalActualActiveMeasureConstructor
                B.sampleData T
                (R.roughCanonicalGuardedCandidateSet
                  certificate deltaStar K)
                (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                  B R certificate
                  deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T q)
                    (bankPaperCanonicalSymmetricHeightCellMass d)
                    (bankPaperCanonicalSymmetricHeightCellMass d)))
                (bankPaperCanonicalScaledActiveSeed T q) ->
              B.sampleData.HeadPatternsSeparated ->
              forall m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight
                    (bankPaperCanonicalActualFrozenValue
                      (candidates :=
                        R.roughCanonicalGuardedCandidateSet
                          certificate deltaStar K))
                    (bankPaperCanonicalActualFrozenWeight B.sampleData
                      (R.roughCanonicalGuardedCandidateSet
                        certificate deltaStar K)
                      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                        B R certificate
                        deltaStar betaProt baseSelector
                        (bankPaperCanonicalTwoZeroHeadCellRebalance
                          B.sampleData
                          (bankPaperCanonicalScaledActiveSeed T q)
                          (bankPaperCanonicalSymmetricHeightCellMass d)
                          (bankPaperCanonicalSymmetricHeightCellMass d)))
                      (bankPaperCanonicalScaledActiveSeed T q))
                    (B.sampleData.value m) <=
                  (betaProt + 1) / B.L := by
  have hupper :=
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_upperAbsorption
      (Band := Band)
      Phead I Cprom Cbank ledger W K hmu
        logY Lambda0 mFrozen qTilde Hledger
  filter_upwards [hupper] with n hupperN
  intro B hBn hsep hremaining hcanonical
    R certificate T baseSelector
  dsimp only
  intro Hmeasure hhead m
  apply bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
    B R certificate deltaStar betaProt hbetaProt baseSelector T
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      (bankPaperCanonicalSmoothDIntFamily
        mu logY Lambda0 mFrozen qTilde n)
      hhead Hmeasure 1 (by norm_num)
  exact hupperN B hBn hsep hremaining hcanonical

/-! ## The exact finite P87-tail adapter -/

/-- A selector-deficit estimate is exactly the initial marked estimate for
the actual tagged active target. -/
theorem bankPaperCanonicalActualInitialMarkedRate_of_selectorDeficit
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
    (Cinitial : Real)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L)) :
    ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) 0) <=
          Cinitial * B.q / ((p : Real) * B.L) := by
  intro p hp
  rw [← bankPaperCanonicalActualInitial_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed p]
  exact hdeficit p hp

/-- Tail adapter for a local instance of canonical Proposition 8.7.

The argument `hP87` is precisely the local tail obtained after the global
canonical theorem has fixed its mesh, threshold, radius, and post-fit
constant and after the structural bridge hypotheses and active baseline
have been supplied.  This theorem removes every remaining finite premise
which follows from the actual-measure constructor and selector state.
-/
theorem exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical
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
    (hselector : ∀ a ∈ candidates,
      0 <= preSelector a ∧ preSelector a <= 1)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector)
    (hhead : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j))
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates := candidates))
          (bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota) :
    ∃ quota : Int,
      B.HasPaperProposition87Conclusion
        (fun j => B.markedBandResidual
          (bankPaperCanonicalActualActiveMarkedTarget
            B R certificate fixed candidates preSelector activeSeed) 0 j)
        radius
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed)
        B.q Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota := by
  obtain ⟨quota, hquotaLiteral⟩ :=
    exists_bankPaperCanonicalActualP87IntegerQuota Hmeasure hrow
  have hqLiteral :
      B.q = bankPaperCanonicalLiteralActiveMass
        B.sampleData activeSeed :=
    Erdos390.WholePaper.BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
      B activeSeed hseed
  have hquota :
      (quota : Real) =
        (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed a) + B.q := by
    rw [hqLiteral]
    exact hquotaLiteral
  have hfrozenFeasible :
      forall x,
        BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates := candidates))
          (bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed) x ∈
          Icc (0 : Real) 1 :=
    bankPaperCanonicalActualFrozenWeight_mem_Icc Hmeasure hselector
  have hinitial :=
    bankPaperCanonicalActualInitialMarkedRate_of_selectorDeficit
      B R certificate fixed candidates preSelector activeSeed
        Hmeasure hseed Cinitial hdeficit
  refine ⟨quota, hP87
    (fun j => B.markedBandResidual
      (bankPaperCanonicalActualActiveMarkedTarget
        B R certificate fixed candidates preSelector activeSeed) 0 j)
    henv
    (bankPaperCanonicalActualActiveMarkedTarget
      B R certificate fixed candidates preSelector activeSeed)
    B.q B.q_pos.le (by simp) hinitial (fun _j => rfl)
    (Fixed := BankPaperCanonicalActualFrozenIndex candidates)
    (bankPaperCanonicalActualFrozenValue (candidates := candidates))
    (bankPaperCanonicalActualFrozenWeight
      B.sampleData candidates preSelector activeSeed)
    quota hquota hhead hfrozenFeasible hfrozenLedger hactiveLedger⟩

end BankPaperRealization

end

end Erdos390.WholePaper
