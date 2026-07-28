import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstEventualCoherentBridgeSourceObligation

/-!
# Finite exported fields for the source-first post-height bridge

This file isolates three finite consequences of the source-first `J`/`S`/
primitive-gap package which are needed by the eventual Section 9
orchestrator.

* The rounded frozen-top source has pointwise frozen remainder at most
  `(betaProt + Cactive) / L`.
* The guarded broad correction pool is nonempty.
* The local integer height adjustment is exactly the Section 8 analytic
  `d` family.

No eventual intersection or Proposition 8.7 parameter choice occurs here.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

section FiniteSourceFields

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)

include S

/-! ## Rounded frozen ledger -/

/-- At an occupied post-height coordinate, the rounded source's frozen
remainder is exactly the explicit protected layer.  Floating rounding
changes the selector and its ambient active seed by the same amount. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenAmbientWeight_eq_protectedLayer
    (m : J.postHeightBridge.sampleData.Sample) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed)
        (J.postHeightBridge.sampleData.value m) =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          (J.postHeightBridge.sampleData.value m) := by
  have hmActive :
      J.postHeightBridge.sampleData.value m ∈
        bankPaperCanonicalStructuredActiveValues
          J.postHeightBridge.sampleData :=
    mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩
  have hmSmooth :
      J.postHeightBridge.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate
          deltaStar (K0 + 1) 1 :=
    S.activeSmooth hmActive
  have hmCandidate :
      J.postHeightBridge.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1) :=
    (mem_completeRoughRowFiber.mp hmSmooth).1
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight,
    if_pos hmCandidate]
  have hchange :
      J.roundedSourceSelector
            (J.postHeightBridge.sampleData.value m) -
          bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) J.postHeightBridge R certificate
              deltaStar J.betaProt J.alpha J.beta
              (bankPaperCanonicalScaledActiveSeed
                J.Tsource J.qTilde)
              (J.postHeightBridge.sampleData.value m) =
        bankPaperCanonicalActiveSeedAmbientWeight
            J.postHeightBridge.sampleData J.roundedActiveSeed
            (J.postHeightBridge.sampleData.value m) -
          bankPaperCanonicalActiveSeedAmbientWeight
            J.postHeightBridge.sampleData
            (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
            (J.postHeightBridge.sampleData.value m) := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedActiveSeed] using
      (bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
        (K := K0 + 1) J.postHeightBridge R certificate J.Tsource
          deltaStar J.betaProt J.alpha J.beta J.qTilde
          S.activeSmooth hmCandidate)
  calc
    J.roundedSourceSelector
          (J.postHeightBridge.sampleData.value m) -
        bankPaperCanonicalActiveSeedAmbientWeight
          J.postHeightBridge.sampleData J.roundedActiveSeed
          (J.postHeightBridge.sampleData.value m) =
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
          (K := K0 + 1) J.postHeightBridge R certificate
            deltaStar J.betaProt J.alpha J.beta
            (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
            (J.postHeightBridge.sampleData.value m) -
        bankPaperCanonicalActiveSeedAmbientWeight
          J.postHeightBridge.sampleData
          (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
          (J.postHeightBridge.sampleData.value m) := by
      linarith only [hchange]
    _ =
      roughHeadCompatibleRawWeight
        J.postHeightBridge.sampleData.W
        J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)
        (K0 + 1) J.alpha J.betaProt J.postHeightBridge.L
        (J.postHeightBridge.sampleData.value m) := by
      rw [
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
          (K := K0 + 1) J.postHeightBridge R certificate
            (bankPaperCanonicalScaledActiveSeed J.Tsource J.qTilde)
            hmSmooth]
      ring
    _ =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          (J.postHeightBridge.sampleData.value m) :=
      (bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
        (K := K0 + 1) J.postHeightBridge R certificate
          hmSmooth (S.activeBroad m)).symm

/-- The rounded source satisfies the precise pointwise frozen-ledger bound
used by
`bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields`.
-/
theorem
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenLedger_of_sourceInputs
    (m : J.postHeightBridge.sampleData.Sample) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed)
        (J.postHeightBridge.sampleData.value m) ≤
      (J.betaProt + S.Cmass / S.density) /
        J.postHeightBridge.L := by
  rw [
    bankPaperCanonicalSectionNinePostHeight_roundedFrozenAmbientWeight_eq_protectedLayer
      J S m]
  have hactiveCapacity : 0 ≤ S.Cmass / S.density :=
    div_nonneg S.Cmass_nonneg S.density_pos.le
  by_cases hpool :
      J.postHeightBridge.sampleData.value m ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1
  · rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
        J.postHeightBridge R certificate hpool]
    exact div_le_div_of_nonneg_right
      (le_add_of_nonneg_right hactiveCapacity)
      J.postHeightBridge.L_pos.le
  · rw [
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        J.postHeightBridge R certificate hpool]
    exact div_nonneg
      (add_nonneg S.betaProt_nonneg hactiveCapacity)
      J.postHeightBridge.L_pos.le

/-! ## Broad-pool nonemptiness -/

/-- One zero-head physical cell supplies a literal member of the guarded
broad correction pool.  The witness comes from the nonempty structured
sample cell stored in `StructuredSampleData`; all arithmetic support facts
are already fields or consequences of `S`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_guardedBroadCorrectionPool_nonempty_of_sourceInputs :
    (R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1).Nonempty := by
  have hcellCard :
      0 < Fintype.card
        (J.postHeightBridge.sampleData.SampleAt
          ((none, .minus) : Cell (PaperHeadSimplex.Tag P))) :=
    J.postHeightBridge.sampleData.sampleAt_card_pos (none, .minus)
  let mAt :
      J.postHeightBridge.sampleData.SampleAt
        ((none, .minus) : Cell (PaperHeadSimplex.Tag P)) :=
    Classical.choice (Fintype.card_pos_iff.mp hcellCard)
  let m : J.postHeightBridge.sampleData.Sample :=
    ⟨(none, .minus), mAt⟩
  refine ⟨J.postHeightBridge.sampleData.value m, ?_⟩
  exact
    bankPaperCanonicalZeroHeadValue_mem_guardedBroadCorrectionPool_of_physicalIntervals
      (K := K0 + 1) J.postHeightBridge R certificate deltaStar
        S.hprime J.exponent S.hpattern S.headPrimes I
        S.lowerOne S.upperTwo J.postHeightHlo J.postHeightHhi
        S.upperBroad S.outsideGuard m .minus (by rfl)

/-! ## Exact analytic-family synchronization -/

variable
    {E : Nat}
    {mu sourceMarginFloor headMarginFloor physicalEtaFloor
      postMarginFloor : Real}
    {logY Lambda0 mFrozen qTilde : Nat → Real}
    (Hgap : BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
      M Bsource R certificate I E deltaStar mu sourceMarginFloor
        headMarginFloor physicalEtaFloor postMarginFloor
        logY Lambda0 mFrozen qTilde hdelta J S)

include Hgap

/-- The local rounded `q0` is the literal Section 8 smooth `q0` family at
the source index. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_q0_eq_smoothQ0Family_of_primitiveGaps :
    J.q0 =
      bankPaperCanonicalSmoothQ0Family
        mFrozen qTilde Bsource.sampleData.n := by
  rw [J.roundedQ0_eq_postHeightBridge]
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
    bankPaperCanonicalSmoothQ0Family
  rw [← Hgap.mFrozen_family, Hgap.qTilde_family]

/-- The integer selected in the finite post-height target is exactly the
analytic Section 8 integer-height family, viewed in `Real`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_d_eq_smoothDRealFamily_of_primitiveGaps :
    (J.d : Real) =
      bankPaperCanonicalSmoothDRealFamily
        mu logY Lambda0 mFrozen qTilde
          J.postHeightBridge.sampleData.n := by
  have hfinal :
      J.q0 - (J.d : Real) =
        bankPaperCanonicalSmoothQ0Family
            mFrozen qTilde Bsource.sampleData.n -
          bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.qn,
      bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
      bankPaperCanonicalSmoothFinalActiveMassFamily_eq_q0_sub_d] using
      Hgap.finalActiveMass_family
  rw [
    bankPaperCanonicalSectionNinePostHeight_q0_eq_smoothQ0Family_of_primitiveGaps
      J S Hgap] at hfinal
  have hdSource :
      (J.d : Real) =
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n := by
    linarith only [hfinal]
  simpa only [J.postHeightBridge_sampleData] using hdSource

end FiniteSourceFields

end BankPaperRealization

end

end Erdos390.WholePaper
