import Erdos390.WholePaper.BankPaperCanonicalTopFrozenSourceFeasibilityReductionConnector

/-!
# Smooth-row feasibility for the frozen-top source

The classification theorem for the frozen-top source leaves one local
premise on complete rough label `1`.  This file discharges that premise for
the literal scaled active seed.

There are two elementary points.

* At a surviving smooth coordinate in the broad lower block, the protected
  layer is exactly the raw head-compatible weight.  If the coordinate is
  head-free it lies in the guarded smooth correction pool; otherwise both
  weights vanish.
* Away from the structured active image the ambient scaled seed vanishes.
  On the image, the existing
  `BankPaperCanonicalStructuredAdditivePlacementCapacity` is precisely the
  required upper bound.

Thus the only geometric input is that the structured active values lie in
the broad lower block.  This is the finite form of the strict physical
upper-endpoint gap already used in the canonical Section 8 geometry.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Broad support from the physical endpoint gap -/

/-- The same strict upper-endpoint gap used by the canonical Section 8
geometry puts every structured sample value in the broad lower block.

This is stated separately because the earlier geometry projection exports
smooth-row support but only exports guarded-broad membership for the two
zero-head cells. -/
theorem
    bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals) (h K : Nat)
    (hlowerOne : ∀ sigma, 1 <= I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma <= 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : ∀ sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n - K * h) :
    ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n h K := by
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  intro m
  rw [roughBroadLowerBlock, Finset.mem_Ioc]
  refine ⟨hbounds.1 m, ?_⟩
  calc
    B.sampleData.value m <=
        B.sampleData.hi (B.sampleData.cellOf m).2 :=
      B.sampleData.value_le_hi m
    _ = physicalBound (I.upper (B.sampleData.cellOf m).2)
          B.sampleData.n :=
      hhi (B.sampleData.cellOf m).2
    _ <= 2 * B.sampleData.n - K * h :=
      hupperBroad (B.sampleData.cellOf m).2

/-! ## Identification of the protected layer on the broad smooth row -/

/-- On every surviving smooth-row coordinate in the broad lower block, the
explicit protected layer equals the raw head-compatible weight with broad
parameter `betaProt`.

The existing pointwise theorem handles the head-free case.  In the
non-head-free case the coordinate is outside the correction pool and both
sides are zero. -/
theorem
    bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
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
    {deltaStar alpha betaProt : Real} {a : Nat}
    (haSmooth :
      a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (haBroad :
      a ∈ roughBroadLowerBlock B.sampleData.n
        (upperTailLength c B.sampleData.n) K) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  by_cases hcop : Nat.Coprime a (roughHeadModulus B.sampleData.W)
  · have haCandidate :
        a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
      (mem_completeRoughRowFiber.mp haSmooth).1
    have haSurvives :
        a ∉ R.roughCanonicalGuardSet certificate deltaStar :=
      (Finset.disjoint_left.mp
        (R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
          certificate deltaStar K)) haCandidate
    have haRawPool :
        a ∈ roughCanonicalBroadCorrectionPool B.sampleData.W
          B.sampleData.n (upperTailLength c B.sampleData.n) K
            (yNat B.sampleData.n) 1 := by
      apply mem_completeRoughRowFiber.mpr
      exact
        ⟨mem_roughHeadFree.mpr ⟨haBroad, hcop⟩,
          (mem_completeRoughRowFiber.mp haSmooth).2⟩
    have haPool :
        a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      rw [roughCanonicalGuardedBroadCorrectionPool, Finset.mem_sdiff]
      exact ⟨haRawPool, haSurvives⟩
    exact
      bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
        B R certificate haPool
  · have hnotPool :
        a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
      intro haPool
      have haRawPool :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar B.sampleData.W K 1 haPool
      have haHeadFree :=
        (mem_completeRoughRowFiber.mp haRawPool).1
      exact hcop (mem_roughHeadFree.mp haHeadFree).2
    rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate hnotPool]
    simp [roughHeadCompatibleRawWeight, hcop]

/-! ## The atomic smooth-row premise -/

/-- The exact structured-placement capacity closes feasibility of the
literal frozen-top source on complete rough label `1`.

Inactive coordinates use the ordinary raw parameter box.  At an active
coordinate, broad support identifies the raw layer with the protected layer,
and head-pattern separation identifies the ambient push-forward with the
corresponding tagged scaled seed. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_feasible_of_scaledSeedCapacity
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
    (hq : 0 <= q)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbetaProt : 0 <= betaProt / B.L ∧ betaProt / B.L <= 1)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hcapacity :
      BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
        B R certificate deltaStar betaProt T q) :
    ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a <= 1 := by
  intro a haSmooth
  rw [
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
      B R certificate (bankPaperCanonicalScaledActiveSeed T q) haSmooth]
  have hraw :=
    roughHeadCompatibleRawWeight_mem_unitInterval
      (W := B.sampleData.W) (n := B.sampleData.n)
      (h := upperTailLength c B.sampleData.n) (K := K)
      (α := alpha) (β := betaProt) (L := B.L)
      halpha hbetaProt a
  have hambientNonneg :
      0 <= bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q) a :=
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg T hq a
  constructor
  · exact add_nonneg hraw.1 hambientNonneg
  · by_cases hactive :
        a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
    · obtain ⟨m, rfl⟩ :=
        mem_bankPaperCanonicalStructuredActiveValues.mp hactive
      rw [
        ←
          bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
            B R certificate haSmooth (hactiveBroad m),
        bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
          B.sampleData (bankPaperCanonicalScaledActiveSeed T q) hsep m]
      exact hcapacity.2 m
    · have hambientZero :
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
        apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
        intro m hma
        exact hactive
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
      rw [hambientZero, add_zero]
      exact hraw.2

/-! ## Full finite feasibility -/

/-- The preceding smooth-row theorem eliminates the `hsmooth` premise from
the classification reduction.  The only remaining local premise is the
already explicit corrected-weight capacity on active nonexceptional
nonsmooth rows. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_scaledSeedCapacity_of_active
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
    (hq : 0 <= q)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbetaProt : 0 <= betaProt / B.L ∧ betaProt / B.L <= 1)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hcapacity :
      BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
        B R certificate deltaStar betaProt T q)
    (hactive : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          0 <=
              R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha betaTotal B.L a ∧
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha betaTotal B.L a <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a <= 1 := by
  apply
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_active
      (K := K) B R certificate deltaStar betaProt alpha betaTotal
        (bankPaperCanonicalScaledActiveSeed T q)
  · exact
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_feasible_of_scaledSeedCapacity
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal q
          hq halpha hbetaProt hsep hactiveBroad hcapacity
  · exact hactive

/-- A pointwise `Cactive / L` bound and the scalar room
`betaProt + Cactive <= L` are the existing parameter-box form of the exact
capacity predicate.  Combining them with the two-sided nonsmooth slack
theorem gives feasibility on the entire guarded candidate set without a
separate smooth-row premise. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_scaledSeedDivLog_of_twoSidedSlack
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
    (deltaStar betaProt alpha betaTotal q sigma Cactive : Real)
    (hq : 0 <= q)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbetaProt : 0 <= betaProt)
    (hbetaTotal : 0 <= betaTotal / B.L ∧ betaTotal / B.L <= 1)
    (hsigma : 0 <= sigma / B.L)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hCactive : 0 <= Cactive)
    (hseedUpper : ∀ m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <= Cactive / B.L)
    (hlarge : betaProt + Cactive <= B.L)
    (hfloor : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha betaTotal B.L| <=
          betaTotal / B.L)
    (hceiling : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        betaTotal / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha betaTotal B.L| <=
          1 - sigma / B.L) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T q) a <= 1 := by
  have hcapacity :
      BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
        B R certificate deltaStar betaProt T q :=
    bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
      (K := K) B R certificate deltaStar betaProt T q hbetaProt
        Cactive hCactive hseedUpper hlarge
  have hbetaProtBox :
      0 <= betaProt / B.L ∧ betaProt / B.L <= 1 :=
    ⟨div_nonneg hbetaProt B.L_pos.le, hcapacity.1⟩
  apply
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_twoSidedSlack
      (K := K) B R certificate deltaStar betaProt alpha betaTotal sigma
        (bankPaperCanonicalScaledActiveSeed T q)
        halpha hbetaTotal hsigma
  · exact
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_feasible_of_scaledSeedCapacity
        (K := K) B R certificate T deltaStar betaProt alpha betaTotal q
          hq halpha hbetaProtBox hsep hactiveBroad hcapacity
  · exact hfloor
  · exact hceiling

end BankPaperRealization

end

end Erdos390.WholePaper
