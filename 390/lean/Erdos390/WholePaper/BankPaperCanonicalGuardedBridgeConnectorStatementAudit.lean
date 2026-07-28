import Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector

/-!
# Statement audit for the guarded Section 8/9 bridge connector

This audit expands the canonical bridge constructor, the sole selector
socket, and the literal frozen support.  It also checks every public
declaration in the connector module, including the full existential terminal.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

/-! The bridge constructor uses the supplied structured sample, the
barycentric baseline, the canonical mesh partition and low band, and has
active mass exactly one. -/
example
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    let B := bankPaperCanonicalBridgeData
      D T M hdelta hn hW S referenceHead hw
    B.sampleData = D ∧
      B.baseline = T.baseline ∧
      B.partition =
        Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
          M hdelta hn hW S ∧
      B.lowBand =
        Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M ∧
      B.w = delta + eta ∧
      B.q = 1 := by
  simp

/-! The only existential socket is an actual guarded selector.  All
balance, support, tangent, and feasibility data reside in the already
audited rounded-selector input; the sole added equation identifies its
active coordinates with the canonical bridge baseline. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real) :
    BankPaperCanonicalGuardedBridgeSelectorConstructor B R certificate
        deltaStar (K := K) cellIndex pointwiseUpper prefixUpper ↔
      ∃ selector : Nat -> Real,
        BankPaperCanonicalRoundedSelectorTangentInput
          R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          B.partition.band cellIndex pointwiseUpper prefixUpper selector ∧
        forall m : B.sampleData.Sample,
          selector (B.sampleData.value m) = B.baseline.baseWeight m := by
  rfl

/-! The frozen layer is definitionally the unit-weight fixed exceptional
set plus selector-weighted guarded coordinates outside the bridge support. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat)
    (selector : Nat -> Real) (a : Nat) :
    bankPaperCanonicalBridgeFrozenSupport B fixed candidates =
        fixed ∪ (candidates \ bankPaperCanonicalBridgeActiveValues B) ∧
      bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector a =
        if a ∈ fixed then 1
        else if a ∈ candidates \ bankPaperCanonicalBridgeActiveValues B then
          selector a
        else 0 := by
  exact ⟨rfl, rfl⟩

/-! ## Complete public declaration census -/

#check bankPaperCanonicalBridgeData
#check bankPaperCanonicalBridgeData_sampleData
#check bankPaperCanonicalBridgeData_baseline
#check bankPaperCanonicalBridgeData_partition
#check bankPaperCanonicalBridgeData_lowBand
#check bankPaperCanonicalBridgeData_w
#check bankPaperCanonicalBridgeData_q
#check bankPaperCanonicalBridgeActiveValues
#check mem_bankPaperCanonicalBridgeActiveValues
#check exists_bankPaperCanonicalSmoothQuota_of_rowIntegral
#check exists_bankPaperCanonicalTotalQuota_of_rowIntegral
#check BankPaperCanonicalGuardedBridgeSelectorConstructor
#check bankPaperCanonicalGuardedBridgeSelectorConstructor_exists_fields
#check bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
#check bankPaperCanonicalBridgeActiveValues_subset_guardedCandidates
#check paperFixedExceptionalFactors_disjoint_bridgeActiveValues
#check paperFixedExceptionalFactors_disjoint_guardedCandidates
#check bankPaperCanonicalBridgeFrozenSupport
#check BankPaperCanonicalBridgeFrozenIndex
#check bankPaperCanonicalBridgeFrozenValue
#check bankPaperCanonicalBridgeFrozenCoordinateWeight
#check bankPaperCanonicalBridgeFrozenWeight
#check frozenAmbientWeight_eq_bankPaperCanonicalBridgeFrozenWeight
#check bankPaperCanonicalBridgeFrozenWeight_mem_Icc
#check bankPaperCanonicalBridgeFrozenWeight_eq_zero_on_sample
#check sum_selector_bridgeActiveValues_eq_q
#check sum_bankPaperCanonicalBridgeFrozenCoordinateWeight
#check exists_bankPaperCanonicalBridgeIntegerQuota
#check bankPaperCanonicalBridge_combinedBaselineSlack
#check exists_bankPaperCanonicalGuardedBridgeConnector
#check bankPaperCanonicalBridge_ambientCombinedWeight_mem_Icc

end

end Erdos390.WholePaper
