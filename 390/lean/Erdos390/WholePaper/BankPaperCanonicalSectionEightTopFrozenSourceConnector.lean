import Erdos390.WholePaper.BankPaperCanonicalGlobalCorrectedSourceSelector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction

/-!
# The frozen smooth-top source at the Section 8 initial stage

The paper's smooth-row initialization has three distinct layers:

* the `alpha`-weighted top block;
* the protected `betaProt / L` broad layer; and
* the structured active seed of total mass `qTilde`.

The older global corrected source retained the latter two layers on the
guarded broad pool, but its complete-label-one branch contained only the
ambient active seed.  In particular it did not contain the top block.

This connector defines a separate, finite `qTilde`-stage source which adds
that missing top layer.  On the guarded complete smooth row it is pointwise
equal to the literal raw weight with broad parameter `betaProt`, plus the
ambient old seed.  Consequently, when the old seed has total mass equal to
the guarded `betaAct` base mass, its whole guarded smooth-row sum is exactly
the balanced raw sum with broad parameter `betaProt + betaAct`.

No asymptotic estimate, post-height-fit displacement, or Section 9 source
state is asserted here.  The identities are finite and exact.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The missing smooth top layer -/

/-- The paper's frozen smooth top component: the literal raw weight with
zero broad coefficient.  The logarithmic scale is retained as an argument
so the definition can be compared directly with the existing raw weight. -/
def bankPaperCanonicalSmoothTopWeight
    (W n h K : Nat) (alpha logScale : Real) (a : Nat) : Real :=
  roughHeadCompatibleRawWeight W n h K alpha 0 logScale a

/-- On complete label one, add the frozen smooth top layer to the ambient
old seed.  Exceptional nonsmooth rows vanish, while active nonexceptional
rows keep the existing guarded postcharge corrected weight. -/
def bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
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
    (deltaStar alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) (a : Nat) : Real := by
  classical
  exact
    if completeRoughLabel (yNat B.sampleData.n) a = 1 then
      bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha B.L a +
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a
    else
      if RoughCanonicalExceptionalLabel B.sampleData.n deltaStar
          (completeRoughLabel (yNat B.sampleData.n) a) then
        0
      else
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar B.sampleData.W K
            (completeRoughLabel (yNat B.sampleData.n) a)
              alpha beta B.L a

/-- The protected two-zero-cell source, with the missing top component
restored on the remainder of complete label one. -/
def bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
    B R certificate deltaStar betaProt oldSeed
      (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
        B R certificate deltaStar alpha beta oldSeed)

/-! ## Pointwise smooth-row identification -/

/-- Away from the guarded head-free broad pool, the top-only weight equals
the raw weight with any broad coefficient on the guarded smooth row.

Indeed, a surviving smooth-row coordinate is in the high or broad block.
In the broad block, head freedom would put it in the guarded broad pool, so
outside that pool it has zero raw weight. -/
theorem bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
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
    {deltaStar alpha beta : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hnotPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha B.L a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha beta B.L a := by
  have haData := mem_completeRoughRowFiber.mp ha
  have haRaw :
      a ∈ roughRawCandidateSet B.sampleData.n
        (upperTailLength c B.sampleData.n) K :=
    R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
      certificate deltaStar K haData.1
  have haSurvives :
      a ∉ R.roughCanonicalGuardSet certificate deltaStar := by
    have hmem := haData.1
    rw [roughCanonicalGuardedCandidateSet, Finset.mem_sdiff] at hmem
    exact hmem.2
  rw [roughRawCandidateSet, Finset.mem_union] at haRaw
  rcases haRaw with haHigh | haBroad
  · have hnotBroad :
        a ∉ roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K := by
      intro haBroad
      exact Finset.disjoint_left.mp
        (roughHighLowerBlock_disjoint_roughBroadLowerBlock
          B.sampleData.n (upperTailLength c B.sampleData.n) K)
        haHigh haBroad
    simp [bankPaperCanonicalSmoothTopWeight,
      roughHeadCompatibleRawWeight, roughFiniteIndicator, hnotBroad]
  · by_cases hcop :
      Nat.Coprime a (roughHeadModulus B.sampleData.W)
    · have haRawBroad :
          a ∈ roughCanonicalBroadCorrectionPool B.sampleData.W
            B.sampleData.n (upperTailLength c B.sampleData.n) K
              (yNat B.sampleData.n) 1 := by
        apply mem_completeRoughRowFiber.mpr
        exact
          ⟨mem_roughHeadFree.mpr ⟨haBroad, hcop⟩, haData.2⟩
      exfalso
      apply hnotPool
      exact Finset.mem_sdiff.mpr ⟨haRawBroad, haSurvives⟩
    · simp [bankPaperCanonicalSmoothTopWeight,
        roughHeadCompatibleRawWeight, hcop]

/-- Exact pointwise label-one bridge: the restored source is the frozen
raw `alpha + betaProt / L` layer plus the ambient old active seed. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
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
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hpool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · have hraw :=
      roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
        (alpha := alpha) (beta := betaProt) (L := B.L)
        (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
          certificate deltaStar B.sampleData.W K 1 hpool)
    simpa [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector, hpool] using
        congrArg
          (fun x : Real =>
            x + bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a)
          hraw.symm
  · have hlabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp ha).2
    have htop :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        (B := B) R certificate (alpha := alpha) (beta := betaProt)
          ha hpool
    simpa [bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop,
      bankPaperCanonicalTwoZeroHeadCellSourceSelector, hpool,
      bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop,
      hlabel] using
        congrArg
          (fun x : Real =>
            x + bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a)
          htop

/-! ## Exact guarded-row mass identities -/

/-- Summing the pointwise bridge identifies the restored source mass with
the frozen raw mass plus the literal total mass of the old seed. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
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
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a) =
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
          (K := K) B R certificate oldSeed ha
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
      rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
        B.sampleData oldSeed
          (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues]

/-- Pointwise splitting of the broad coefficient on the guarded smooth row.
The active summand is supported exactly on the guarded head-free broad pool. -/
theorem roughHeadCompatibleRawWeight_split_protected_active_of_mem_guardedSmoothRow
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
    {deltaStar betaProt betaAct alpha : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
          (betaProt + betaAct) B.L a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
        if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1 then
          betaAct / B.L
        else 0 := by
  by_cases hpool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · have hbroad :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar B.sampleData.W K 1 hpool
    rw [roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
        (alpha := alpha) (beta := betaProt + betaAct) (L := B.L) hbroad,
      roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
        (alpha := alpha) (beta := betaProt) (L := B.L) hbroad,
      if_pos hpool]
    ring
  · have hprot :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        (B := B) R certificate (alpha := alpha) (beta := betaProt)
          ha hpool
    have htotal :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        (B := B) R certificate (alpha := alpha)
          (beta := betaProt + betaAct) ha hpool
    rw [if_neg hpool, add_zero]
    exact htotal.symm.trans hprot

/-- The raw broad-parameter split summed over the guarded smooth row. -/
theorem sum_roughHeadCompatibleRawWeight_split_protected_active_guardedSmoothRow
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
    (deltaStar betaProt betaAct alpha : Real) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
          (betaProt + betaAct) B.L a) =
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct := by
  have hfilter :
      (R.roughCanonicalGuardedRow certificate deltaStar K 1).filter
          (fun a =>
            a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) =
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun ha => ha.2
    · intro ha
      exact
        ⟨R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
            certificate deltaStar B.sampleData.W K 1 ha,
          ha⟩
  have hactiveSum :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1 then
          betaAct / B.L
        else 0) =
      betaAct / B.L *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1).card : Real) := by
    rw [← Finset.sum_filter, hfilter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    ring
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
          (betaProt + betaAct) B.L a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha betaProt B.L a +
            if a ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar B.sampleData.W K 1 then
              betaAct / B.L
            else 0) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact
        roughHeadCompatibleRawWeight_split_protected_active_of_mem_guardedSmoothRow
          (K := K) B R certificate ha
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1 then
            betaAct / B.L
          else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        betaAct / B.L *
          ((R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1).card : Real) := by
      rw [hactiveSum]
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct := by
      simp only [bankPaperCanonicalGuardedSmoothBaseMass,
        BridgeData.L, Erdos390.Full.Scale.L]

/-- Exact `xTop + fProt + oldSeed = balanced raw` guarded-row ledger.
The only identification premise is the paper's literal statement that the
old seed mass is the guarded active base mass. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_balancedRaw
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
    (deltaStar betaProt betaAct alpha : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hmass :
      bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed =
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha
          (betaProt + betaAct) oldSeed a) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha
            (betaProt + betaAct) B.L a := by
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha
          (betaProt + betaAct) oldSeed a) =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
          bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed :=
      sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_frozenRaw_add_activeMass
        (K := K) B R certificate oldSeed hvalues
    _ = (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha betaProt B.L a) +
        bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
          B.sampleData.W K betaAct := by
      rw [hmass]
    _ = ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha
            (betaProt + betaAct) B.L a := by
      symm
      exact
        sum_roughHeadCompatibleRawWeight_split_protected_active_guardedSmoothRow
          (K := K) B R certificate deltaStar betaProt betaAct alpha

/-- Scaled-seed specialization.  The normalization theorem reduces the
mass premise to the displayed equality `q = guardedSmoothBaseMass`. -/
theorem sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_scaledSeed_smoothRow_eq_balancedRaw
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
    (deltaStar betaProt betaAct alpha q : Real)
    (hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hq :
      q = bankPaperCanonicalGuardedSmoothBaseMass R certificate deltaStar
        B.sampleData.W K betaAct) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha
          (betaProt + betaAct)
            (bankPaperCanonicalScaledActiveSeed T q) a) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha
            (betaProt + betaAct) B.L a := by
  apply
    sum_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_smoothRow_eq_balancedRaw
      (K := K) B R certificate deltaStar betaProt betaAct alpha
        (bankPaperCanonicalScaledActiveSeed T q) hvalues
  simpa only [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed] using hq

end BankPaperRealization

end

end Erdos390.WholePaper
