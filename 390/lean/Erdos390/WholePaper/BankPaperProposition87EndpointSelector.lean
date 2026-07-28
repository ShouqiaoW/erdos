import Erdos390.Full.PaperProposition87ActiveMassTransport
import Erdos390.Full.CanonicalRegularMeshEndpointFamily

/-!
# Proposition 8.7 endpoint as an ambient natural-number selector

The bridge is carried out on a tagged active sample, whereas Section 9 uses
one weight function on natural-number coordinates.  This file performs the
finite push-forward exactly.  The ambient selector is the sum of

* every frozen tagged contribution, including a protected contribution on a
  coordinate which may also be active; and
* the endpoint active weight produced by Proposition 8.7.

Thus no disjointness between the protected and active layers is imposed.
The proofs below use only the literal Proposition 8.7 path output.  In
particular, they do not claim the separate complete-rough-row integrality or
outside-band target identities still needed by the Section 9 tangent input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Backward-compatible literal-mass bridge data -/

/-- Canonical regular-mesh bridge data using the paper's unnormalized active
mass.  The old probability-baseline constructor remains available unchanged;
this is the variant which must be used at the literal Section 8 endpoint. -/
def bankPaperCanonicalActiveMassBridgeData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    BridgeData Head (Fin (M.cellCount + 1)) where
  sampleData := D
  baseline := T.activeMassBaseline q hq
  partition :=
    Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
  lowBand := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M
  referenceHead := referenceHead
  w := delta + eta
  w_pos := hw
  n_gt_one := hn

/-- The literal-mass constructor retains the supplied structured sample. -/
@[simp] theorem bankPaperCanonicalActiveMassBridgeData_sampleData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).sampleData = D :=
  rfl

/-- The literal-mass constructor stores the scaled canonical allocation. -/
@[simp] theorem bankPaperCanonicalActiveMassBridgeData_baseline
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).baseline =
        T.activeMassBaseline q hq :=
  rfl

/-- The bridge mass of the literal-mass constructor is the supplied `q_n`. -/
@[simp] theorem bankPaperCanonicalActiveMassBridgeData_q
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw).q = q := by
  exact BridgeData.q_eq_of_baseline_eq_activeMassBaseline
    (bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw)
    T q hq rfl

/-! ## Push-forward to natural-number coordinates -/

/-- Finite natural-number support of the frozen and active tagged layers. -/
def bankPaperProposition87SelectorSupport
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    (B : BridgeData Head Band) (fixedValue : Fixed -> Nat) : Finset Nat :=
  Finset.univ.image fixedValue ∪
    Finset.univ.image B.sampleData.value

/-- The literal ambient selector at one point of the Proposition 8.7 path.
The addition is intentional: a protected frozen summand may occupy the same
clean coordinate as the active bridge. -/
def bankPaperProposition87SelectorAt
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) (a : Nat) : Real :=
  B.ambientCombinedWeight
    (BridgeData.frozenAmbientWeight fixedValue fixedWeight) (path t) a

/-- The natural-number selector at the fitted endpoint. -/
def bankPaperProposition87EndpointSelector
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) : Nat -> Real :=
  bankPaperProposition87SelectorAt B fixedValue fixedWeight path 1

/-- Every frozen tag maps into the finite ambient support. -/
theorem fixedValue_mem_bankPaperProposition87SelectorSupport
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    (B : BridgeData Head Band) (fixedValue : Fixed -> Nat) (f : Fixed) :
    fixedValue f ∈ bankPaperProposition87SelectorSupport B fixedValue := by
  classical
  simp [bankPaperProposition87SelectorSupport]

/-- Every active sample tag maps into the finite ambient support. -/
theorem sampleValue_mem_bankPaperProposition87SelectorSupport
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    (B : BridgeData Head Band) (fixedValue : Fixed -> Nat)
    (m : B.sampleData.Sample) :
    B.sampleData.value m ∈
      bankPaperProposition87SelectorSupport B fixedValue := by
  classical
  simp [bankPaperProposition87SelectorSupport]

/-- The ambient selector has no hidden support outside the two tagged
layers. -/
theorem bankPaperProposition87SelectorAt_eq_zero_of_not_mem_support
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) {a : Nat}
    (ha : a ∉ bankPaperProposition87SelectorSupport B fixedValue) :
    bankPaperProposition87SelectorAt
      B fixedValue fixedWeight path t a = 0 := by
  classical
  have hfixed : ∀ f : Fixed, fixedValue f ≠ a := by
    intro f hfa
    apply ha
    rw [← hfa]
    exact fixedValue_mem_bankPaperProposition87SelectorSupport
      B fixedValue f
  have hactive : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ≠ a := by
    intro m hma
    apply ha
    rw [← hma]
    exact sampleValue_mem_bankPaperProposition87SelectorSupport
      B fixedValue m
  simp [bankPaperProposition87SelectorAt,
    BridgeData.ambientCombinedWeight, BridgeData.frozenAmbientWeight,
    BridgeData.ambientActiveWeight, hfixed, hactive]

private theorem sum_fiberWeight_mul
    {I : Type*} [Fintype I]
    (support : Finset Nat) (value : I -> Nat) (weight : I -> Real)
    (hvalue : ∀ i, value i ∈ support) (F : Nat -> Real) :
    (∑ a ∈ support, (∑ i : I,
      if value i = a then weight i else 0) * F a) =
      ∑ i : I, weight i * F (value i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (value i)]
  · simp
  · intro a ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalue i)).elim

/-- Exact push-forward identity for an arbitrary arithmetic statistic.  It
is valid even when several frozen tags, or a frozen and an active tag, share
one natural-number coordinate. -/
theorem sum_bankPaperProposition87SelectorAt_mul
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) (F : Nat -> Real) :
    (∑ a ∈ bankPaperProposition87SelectorSupport B fixedValue,
      bankPaperProposition87SelectorAt
        B fixedValue fixedWeight path t a * F a) =
      (∑ f : Fixed, fixedWeight f * F (fixedValue f)) +
        B.paperMoment (fun m => F (B.sampleData.value m)) (path t) := by
  classical
  unfold bankPaperProposition87SelectorAt
  simp only [BridgeData.ambientCombinedWeight,
    BridgeData.frozenAmbientWeight, BridgeData.ambientActiveWeight, add_mul]
  rw [Finset.sum_add_distrib]
  rw [sum_fiberWeight_mul
    (bankPaperProposition87SelectorSupport B fixedValue)
    fixedValue fixedWeight
    (fixedValue_mem_bankPaperProposition87SelectorSupport B fixedValue) F]
  rw [sum_fiberWeight_mul
    (bankPaperProposition87SelectorSupport B fixedValue)
    B.sampleData.value (B.activeCoordinateWeight (path t))
    (sampleValue_mem_bankPaperProposition87SelectorSupport B fixedValue) F]
  rfl

/-- The finite natural-coordinate mass equals the sum of all frozen tagged
masses plus the literal active mass `q_n`. -/
theorem sum_bankPaperProposition87SelectorAt
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (path : Real -> B.ParamSpace) (t : Real) :
    (∑ a ∈ bankPaperProposition87SelectorSupport B fixedValue,
      bankPaperProposition87SelectorAt
        B fixedValue fixedWeight path t a) =
      (∑ f : Fixed, fixedWeight f) + B.q := by
  have h := sum_bankPaperProposition87SelectorAt_mul
    B fixedValue fixedWeight path t (fun _ => (1 : Real))
  simpa only [mul_one, B.paperMoment_const, mul_one] using h

/-! ## Literal marked residual at the pushed-forward endpoint -/

/-- The marked target after adjoining the frozen tagged contribution. -/
def bankPaperProposition87FullMarkedTarget
    {Fixed : Type*} [Fintype Fixed]
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real) (p : Nat) : Real :=
  (∑ f : Fixed,
    fixedWeight f * ArithmeticModel.valuation p (fixedValue f)) +
      markedTarget p

/-- Target minus the full frozen-plus-active endpoint moment, written on
the actual finite natural-number support. -/
def bankPaperProposition87FullMarkedResidual
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real)
    (path : Real -> B.ParamSpace) (p : Nat) : Real :=
  bankPaperProposition87FullMarkedTarget
      fixedValue fixedWeight markedTarget p -
    ∑ a ∈ bankPaperProposition87SelectorSupport B fixedValue,
      bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path a * ArithmeticModel.valuation p a

/-- After the exact push-forward, the full ambient residual is exactly the
active residual appearing in Proposition 8.7. -/
theorem bankPaperProposition87FullMarkedResidual_eq_activeResidual
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real)
    (path : Real -> B.ParamSpace) (p : Nat) :
    bankPaperProposition87FullMarkedResidual
        B fixedValue fixedWeight markedTarget path p =
      markedTarget p -
        B.paperMoment (B.markedValuation p) (path 1) := by
  unfold bankPaperProposition87FullMarkedResidual
    bankPaperProposition87EndpointSelector
  rw [sum_bankPaperProposition87SelectorAt_mul]
  unfold bankPaperProposition87FullMarkedTarget BridgeData.markedValuation
  ring

/-- The exact P87 band equations become exact band equations for the
natural-number endpoint selector, with all frozen overlap included. -/
theorem bankPaperProposition87FullMarkedResidual_band_sum_eq_zero
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real)
    (path : Real -> B.ParamSpace)
    (hbands : ∀ j : Band,
      B.markedBandResidual markedTarget (path 1) j = 0) :
    ∀ j : Band,
      (∑ p ∈ B.partition.data.fiber j,
        bankPaperProposition87FullMarkedResidual
          B fixedValue fixedWeight markedTarget path p.1) = 0 := by
  intro j
  rw [← hbands j]
  unfold BridgeData.markedBandResidual
  apply Finset.sum_congr rfl
  intro p hp
  exact bankPaperProposition87FullMarkedResidual_eq_activeResidual
    B fixedValue fixedWeight markedTarget path p.1

/-- The P87 primewise estimate is the same estimate for the full ambient
natural-number selector. -/
theorem abs_bankPaperProposition87FullMarkedResidual_le
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (path : Real -> B.ParamSpace)
    (hmarked : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (markedTarget p -
          B.paperMoment (B.markedValuation p) (path 1)) <=
        Cpost * N / ((p : Real) * B.L)) :
    ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperProposition87FullMarkedResidual
        B fixedValue fixedWeight markedTarget path p) <=
          Cpost * N / ((p : Real) * B.L) := by
  intro p hp
  rw [bankPaperProposition87FullMarkedResidual_eq_activeResidual]
  exact hmarked p hp

/-! ## Direct extraction from the literal Proposition 8.7 conclusion -/

/-- Every coordinate of the pushed-forward endpoint selector is feasible.
This is precisely the ambient feasibility clause of the P87 path. -/
theorem bankPaperProposition87EndpointSelector_mem_Icc_of_path
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real) (a : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (H : B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path) :
    ∀ x : Nat,
      bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path x ∈ Set.Icc (0 : Real) 1 := by
  rcases H with
    ⟨hzero, hball, hsize, hderiv, hbands, hphysical, hlog, hheads,
      hsmall, hprimeLog, hmarked, hfeasible, hfixed, hmass, hquota⟩
  intro x
  exact hfeasible 1 (by simp) x

/-- The finite natural-coordinate selector, rather than only the tagged
disjoint union, has the integer quota emitted by P87. -/
theorem sum_bankPaperProposition87EndpointSelector_eq_quota_of_path
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real) (a : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (H : B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path) :
    (∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
      bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path x) = (quota : Real) := by
  rcases H with
    ⟨hzero, hball, hsize, hderiv, hbands, hphysical, hlog, hheads,
      hsmall, hprimeLog, hmarked, hfeasible, hfixed, hmass, hquota⟩
  unfold bankPaperProposition87EndpointSelector
  rw [sum_bankPaperProposition87SelectorAt]
  have hq := hquota 1 (by simp)
  rw [B.sum_combinedWeight fixedWeight (path 1)] at hq
  exact hq

/-- Low-head marked moments of the ambient natural selector are literally
preserved from the initial point to the endpoint. -/
theorem bankPaperProposition87Selector_lowPrimeMoment_preserved_of_path
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real) (a : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (H : B.IsPaperProposition87Path Delta a markedTarget N Cpost
      fixedValue fixedWeight quota path) :
    ∀ p : Nat, p.Prime → p ≤ B.sampleData.W →
      (∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
        bankPaperProposition87EndpointSelector
          B fixedValue fixedWeight path x * ArithmeticModel.valuation p x) =
      (∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
        bankPaperProposition87SelectorAt
          B fixedValue fixedWeight path 0 x *
            ArithmeticModel.valuation p x) := by
  rcases H with
    ⟨hzero, hball, hsize, hderiv, hbands, hphysical, hlog, hheads,
      hsmall, hprimeLog, hmarked, hfeasible, hfixed, hmass, hquota⟩
  intro p hp hple
  have hsmall' :
      B.paperMoment
          (fun m => ArithmeticModel.valuation p (B.sampleData.value m))
          (path 1) =
        B.paperMoment
          (fun m => ArithmeticModel.valuation p (B.sampleData.value m)) 0 := by
    simpa only [BridgeData.markedValuation] using hsmall p hp hple
  unfold bankPaperProposition87EndpointSelector
  rw [sum_bankPaperProposition87SelectorAt_mul,
    sum_bankPaperProposition87SelectorAt_mul, hsmall', hzero]

/-- Single honest endpoint adapter.  Its witness is the actual P87 path and
the corresponding `Nat -> Real` selector.  Every displayed conclusion is a
projection of `HasPaperProposition87Conclusion`; no row-integrality or
outside-band property is inserted. -/
theorem exists_bankPaperProposition87EndpointSelector
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real) (a : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int)
    (H : B.HasPaperProposition87Conclusion Delta a markedTarget N Cpost
      fixedValue fixedWeight quota) :
    ∃ path : Real → B.ParamSpace, ∃ selector : Nat → Real,
      B.IsPaperProposition87Path Delta a markedTarget N Cpost
          fixedValue fixedWeight quota path ∧
      selector = bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path ∧
      (∀ x, selector x ∈ Set.Icc (0 : Real) 1) ∧
      (∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
        selector x) = (quota : Real) ∧
      (∀ j : Band,
        (∑ p ∈ B.partition.data.fiber j,
          bankPaperProposition87FullMarkedResidual
            B fixedValue fixedWeight markedTarget path p.1) = 0) ∧
      (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
        abs (bankPaperProposition87FullMarkedResidual
          B fixedValue fixedWeight markedTarget path p) <=
            Cpost * N / ((p : Real) * B.L)) ∧
      ∀ p : Nat, p.Prime → p ≤ B.sampleData.W →
        (∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
          selector x * ArithmeticModel.valuation p x) =
        (∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
          bankPaperProposition87SelectorAt
            B fixedValue fixedWeight path 0 x *
              ArithmeticModel.valuation p x) := by
  obtain ⟨path, hpath, hbands⟩ := H
  let selector := bankPaperProposition87EndpointSelector
    B fixedValue fixedWeight path
  refine ⟨path, selector, hpath, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · exact bankPaperProposition87EndpointSelector_mem_Icc_of_path
      B Delta a markedTarget N Cpost fixedValue fixedWeight quota path hpath
  · exact sum_bankPaperProposition87EndpointSelector_eq_quota_of_path
      B Delta a markedTarget N Cpost fixedValue fixedWeight quota path hpath
  · exact bankPaperProposition87FullMarkedResidual_band_sum_eq_zero
      B fixedValue fixedWeight markedTarget path hbands
  · rcases hpath with
      ⟨hzero, hball, hsize, hderiv, hbandMoments, hphysical, hlog, hheads,
        hsmall, hprimeLog, hmarked, hfeasible, hfixed, hmass, hquota⟩
    exact abs_bankPaperProposition87FullMarkedResidual_le
      B fixedValue fixedWeight markedTarget N Cpost path hmarked
  · intro p hp hple
    exact bankPaperProposition87Selector_lowPrimeMoment_preserved_of_path
      B Delta a markedTarget N Cpost fixedValue fixedWeight quota path hpath
        p hp hple

end

end Erdos390.WholePaper
