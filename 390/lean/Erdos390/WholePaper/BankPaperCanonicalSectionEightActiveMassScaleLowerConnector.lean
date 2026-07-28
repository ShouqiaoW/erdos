import Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction

/-!
# Paper-scale lower bound for the guarded Section 8 active mass

The explicit raw smooth base has a positive `secondOrderScale` lower bound.
This connector shows that the concrete guarded tail-family base inherits
that bound without any additional analytic input:

* the guard-deletion pool is bounded by the already controlled smooth
  anchor intersection;
* its weighted mass is therefore `o(secondOrderScale)`; and
* deleting that negligible mass preserves the positive lower comparison.

The tie-lower nearest-integer initialization changes the guarded mass by at
most one half, so the literal Section 8 `q0` family inherits the same type of
lower bound.  No frozen-height or selector-mass hypothesis is used here.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

/-! ## The concrete guard-deletion census -/

/-- Every honest guarded tail family has the smooth guard-deletion census
needed by the raw-to-guarded mass comparison. -/
theorem bankPaperCanonicalGuardedTailSmoothBaseDeletionCensus
    {c : Real} {N : Nat} (depth W K : Nat) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalSmoothGuardDeletionCensus
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar) := by
  have hdeletedToAnchors :
      F.extendedSmoothBaseGuardDeletionCard W K deltaStar =O[atTop]
        F.extendedAnchorIntersectionCard W K := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [
      BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
      dif_pos hn,
      BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
      dif_pos hn, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
    exact_mod_cast
      bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
        (BankPaperCanonicalGuardedTailFamily.realization F n hn)
        (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
          deltaStar W K
  exact hdeletedToAnchors.trans
    (guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
      depth W K F)

/-! ## Raw-to-guarded loss -/

/-- Guard deletion changes the explicit smooth base by
`o(secondOrderScale)`, uniformly for the concrete guarded tail-family
extension. -/
theorem
    bankPaperCanonicalRawSmoothBase_sub_extendedGuardedSmoothBase_isLittleO
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    (fun n =>
      bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) K betaAct -
        F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n)
      =o[atTop] secondOrderScale := by
  apply bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
    betaAct
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    (F.extendedSmoothBaseGuardDeletionCard W K deltaStar)
  · intro n
    by_cases hn : N ≤ n
    · simpa only [
          BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
          BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
          dif_pos hn] using
        bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
          (BankPaperCanonicalGuardedTailFamily.realization F n hn)
          (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
            deltaStar W K betaAct
    · simp only [
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
        dif_neg hn, sub_self, mul_zero]
  · exact bankPaperCanonicalGuardedTailSmoothBaseDeletionCensus
      depth W K deltaStar F

/-! ## Positive paper-scale mass -/

/-- The literal guarded smooth base retains a fixed positive multiple of
`secondOrderScale` whenever the active broad coefficient is positive. -/
theorem
    bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
    {c betaAct : Real} {N : Nat} (depth W K : Nat)
    (hc : 0 < c) (hbeta : 0 < betaAct) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar) := by
  exact bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    (bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
      W K hc hbeta)
    (bankPaperCanonicalRawSmoothBase_sub_extendedGuardedSmoothBase_isLittleO
      depth W K betaAct deltaStar F)

/-- The literal nearest-integer Section 8 initial active mass `q0` inherits
the guarded base's positive paper-scale lower bound. -/
theorem bankPaperCanonicalGuardedTailSmoothQ0Family_paperScaleLower
    {c betaAct : Real} {N : Nat} (depth W K : Nat)
    (hc : 0 < c) (hbeta : 0 < betaAct) (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (mFrozen : Nat -> Real) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothQ0Family mFrozen
        (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)) := by
  exact bankPaperCanonicalSmoothQ0Family_paperScaleLower
    mFrozen
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    (bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
      depth W K hc hbeta deltaStar F)

end

end Erdos390.WholePaper
