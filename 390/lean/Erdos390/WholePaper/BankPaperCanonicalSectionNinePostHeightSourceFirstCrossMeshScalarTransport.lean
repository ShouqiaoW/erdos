import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstRichSourceWithFixedNumericalData

/-!
# Cross-mesh transport of the source-first scalar ledger

The rich source constructor is run after a regular relative mesh has been
chosen, while the Section 8 scalar ledger must be chosen before the final
mesh.  This file records the narrow invariance needed to pass between those
two orders.

Two rich sources made from the same fixed numerical data have, eventually,
the same canonical structured sample.  Their exact rich-to-thin projections
also put both sources on the same realized bank and guarded certificate.
Finally, readiness identifies the barycentric coefficients of both source
targets with the same head target, while the rich projection identifies
their physical mean with the fixed physical target.  Consequently their
scaled active seeds agree.  The frozen mass, precharged logarithm, and
rounded frozen logarithmic mass are therefore independent of which of the
two meshes supplied the bridge partition.

There is no analytic ledger, post-height bridge, downstream contract, or
Section 9 conclusion in this module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Reusable rich-source boundary -/

/-- The mesh-dependent geometric fiber returned by the fixed-numerical
rich-source constructor. -/
abbrev
    BankPaperCanonicalSectionNinePostHeightFixedRichFiber
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (N W : Nat) : Type :=
  let P := primesUpTo W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
  Σ' _hnTail : N ≤ D.n,
  Σ' _hnD : 1 < D.n,
  Σ' _hWD : D.W ≠ 0,
  Σ' _S : ScaleSeparation M D.n D.W,
  Σ' _hlo : (∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n),
  Σ' _hhi : (∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n),
    HeadSimplexReserve P

/-- The thin source fiber used by the source-first scalar ledger. -/
abbrev
    BankPaperCanonicalSectionNinePostHeightFixedThinFiber
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (c : Real) (depth W : Nat) : Type :=
  Σ B : BridgeData
      (PaperHeadSimplex.Tag (primesUpTo W))
      (BankPaperCanonicalExponentBand M),
    BankPaperCanonicalGuardedTailFiber
        c depth B.sampleData.n ×
      BarycentricTarget B.sampleData

/-- The literal rich-to-thin projection used by the fixed-numerical source
constructor, now named so that two mesh instances can be compared. -/
def
    bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c : Real} {depth N W : Nat}
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    BankPaperCanonicalSectionNinePostHeightFixedRichFiber M N W →
      BankPaperCanonicalSectionNinePostHeightFixedThinFiber
        M c depth W := fun Z => by
  let P := primesUpTo W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  change
    (Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
      Σ' _hnTail : N ≤ D.n,
      Σ' _hnD : 1 < D.n,
      Σ' _hWD : D.W ≠ 0,
      Σ' _S : ScaleSeparation M D.n D.W,
      Σ' _hlo : (∀ sigma, D.lo sigma =
          physicalBound (I.lower sigma) D.n),
      Σ' _hhi : (∀ sigma, D.hi sigma =
          physicalBound (I.upper sigma) D.n),
        HeadSimplexReserve P) at Z
  rcases Z with
    ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
  let Kphysical :=
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
  have hw : 0 < delta + eta :=
    add_pos hdelta (M.ratio_pos.trans_le M.ratio_le_eta)
  let Tsource :=
    bankPaperCanonicalSectionNineCoherentSourceTarget
      M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
  let Bsource :=
    bankPaperCanonicalSectionNineCoherentSourceBridge
      M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
  refine ⟨Bsource, ?_⟩
  change
    BankPaperCanonicalGuardedTailFiber c depth D.n ×
      BarycentricTarget D
  exact
    ⟨⟨F.realization D.n hnTail, F.certificate D.n hnTail⟩,
      Tsource⟩

/-- A fixed-numerical rich source together with exactly the four facts
exported by its constructor.  Naming this boundary avoids repeating the
large dependent source type in every cross-mesh statement. -/
structure
    BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct sourceCellMargin : Real}
    {depth N W K0 E : Nat}
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) where
  sourceGeom :
    ∀ n, N ≤ n →
      BankPaperCanonicalSectionNinePostHeightFixedRichFiber M N W
  source :
    ∀ n, N ≤ n →
      BankPaperCanonicalSectionNinePostHeightFixedThinFiber
        M c depth W
  projection :
    ∀ n hn,
      source n hn =
        bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich
          M hdelta F (sourceGeom n hn)
  source_event :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let X := source n hn
        let B := X.1
        let R := X.2.1.1
        let certificate := X.2.1.2
        let T := X.2.2
        let alpha :=
          bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct
        let qTilde :=
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n
        B.sampleData.n = n ∧
          B.sampleData.W = W ∧
          qTilde =
            bankPaperCanonicalGuardedSmoothBaseMass
              R certificate deltaStar B.sampleData.W
                (K0 + 1) betaAct ∧
          1 ≤ qTilde ∧
          B.sampleData.HeadPatternsSeparated ∧
          bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
            R.roughCanonicalGuardedRow
              certificate deltaStar (K0 + 1) 1 ∧
          (0 ≤ alpha ∧ alpha ≤ 1) ∧
          (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
          BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
            (K := K0 + 1) B R certificate
            (R.paperFixedExceptionalFactors deltaStar)
            T deltaStar betaProt alpha
              (betaProt + betaAct) qTilde ∧
          certificate.prechargedTailTarget =
            (F.certificate n hn).prechargedTailTarget
  ready_event :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let X := source n hn
        let B := X.1
        let R := X.2.1.1
        let certificate := X.2.1.2
        let T := X.2.2
        let target :
            {p : Nat // p ∈ primesUpTo W} → Real :=
          fun p =>
            ((certificate.selectorTailTarget R
              (R.paperFixedExceptionalFactors
                deltaStar)).factorization p.1 : Real)
        B.sampleData.n = n ∧
          (∀ p : {p : Nat // p ∈ primesUpTo W},
            bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
                  secondOrderScale n ≤
                target p ∧
              target p ≤
                bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                    c p.1 *
                  secondOrderScale n) ∧
          ∃ _hWB : B.sampleData.W ≠ 0,
          ∃ _S : ScaleSeparation
              M B.sampleData.n B.sampleData.W,
          ∃ hlo : ∀ sigma, B.sampleData.lo sigma =
              physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                  sigma)
                B.sampleData.n,
          ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
              physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                  sigma)
                B.sampleData.n,
          ∃ Rhead : HeadSimplexReserve (primesUpTo W),
          ∃ Kphysical : PhysicalInterpolationTarget
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals,
            Rhead.exponent = E ∧
              (∀ p, Rhead.target p = target p) ∧
              F.extendedGuardedSmoothBaseMass
                  W (K0 + 1) betaAct deltaStar n =
                Rhead.activeMass ∧
              sourceCellMargin ≤ T.cellMassMargin ∧
              T =
                B.barycentricTargetOfPaperData
                  bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                  hlo hhi Rhead Kphysical
  canonical_event :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let X := source n hn
        let B := X.1
        let R := X.2.1.1
        let certificate := X.2.1.2
        ∃ hsep :
            physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                  .minus) n <
              physicalBound
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                  .plus) n,
        ∃ hremaining :
            ∀ cell :
                Cell (PaperHeadSimplex.Tag (primesUpTo W)),
              (rawCell
                    (PaperHeadSimplex.pattern (primesUpTo W)
                      (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                        W) E)
                    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                    n cell \
                  (roughCanonicalBridgeRelevantLedgerFamily depth n).guards
                ).Nonempty,
          B.sampleData =
              canonicalSampleData
                (W := W)
                (PaperHeadSimplex.pattern (primesUpTo W)
                  (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W)
                  E)
                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                (roughCanonicalBridgeRelevantLedgerFamily depth n)
                hsep hremaining ∧
            BankPaperCanonicalBridgeGuardAgreement
              (roughCanonicalBridgeRelevantLedgerFamily depth
                B.sampleData.n)
              R certificate deltaStar

/-! ## Finite invariance helpers -/

/-- The coherent source target does not use the mesh-dependent partition of
its temporary bridge. -/
theorem
    bankPaperCanonicalSectionNineCoherentSourceTarget_mesh_invariant
    {delta₀ eta₀ delta₁ eta₁ : Real}
    (M₀ : RegularRelativeMesh.Mesh delta₀ eta₀)
    (M₁ : RegularRelativeMesh.Mesh delta₁ eta₁)
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, D.lo sigma =
      physicalBound (I.lower sigma) D.n)
    (hhi : ∀ sigma, D.hi sigma =
      physicalBound (I.upper sigma) D.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I)
    (hdelta₀ : 0 < delta₀) (hdelta₁ : 0 < delta₁)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S₀ : ScaleSeparation M₀ D.n D.W)
    (S₁ : ScaleSeparation M₁ D.n D.W)
    (hw₀ : 0 < delta₀ + eta₀)
    (hw₁ : 0 < delta₁ + eta₁) :
    bankPaperCanonicalSectionNineCoherentSourceTarget
        M₀ D I hlo hhi Rhead Kphysical
          hdelta₀ hn hW S₀ hw₀ =
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M₁ D I hlo hhi Rhead Kphysical
          hdelta₁ hn hW S₁ hw₁ := by
  rfl

/-- The scaled active seed only uses `beta` and `mu` from a barycentric
target.  Quantitative reserve fields are proof-facing and do not enter the
coordinate weights. -/
theorem
    bankPaperCanonicalScaledActiveSeed_eq_of_beta_mu_eq
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (T₀ T₁ : BarycentricTarget D)
    (q : Real)
    (hbeta : T₀.beta = T₁.beta)
    (hmu : T₀.mu = T₁.mu) :
    bankPaperCanonicalScaledActiveSeed T₀ q =
      bankPaperCanonicalScaledActiveSeed T₁ q := by
  have hcell :
      ∀ c : Cell Head,
        T₀.cellProbability c = T₁.cellProbability c := by
    intro c
    rcases c with ⟨h, sigma⟩
    cases sigma <;>
      simp only [BarycentricTarget.cellProbability]
    · rw [hbeta, hmu]
    · rw [hbeta, hmu]
  funext m
  unfold bankPaperCanonicalScaledActiveSeed
  unfold BaselineAllocation.baseWeight
  change
    q * (T₀.cellProbability (D.cellOf m) /
        Fintype.card (D.SampleAt (D.cellOf m))) =
      q * (T₁.cellProbability (D.cellOf m) /
        Fintype.card (D.SampleAt (D.cellOf m)))
  rw [hcell]

/-- The computational barycentric coefficients of a head reserve are
determined by its exponent, active mass, and target. -/
theorem
    HeadSimplexReserve.beta_eq_of_exponent_activeMass_target_eq
    {P : Finset Nat}
    (R₀ R₁ : HeadSimplexReserve P)
    (hexponent : R₀.exponent = R₁.exponent)
    (hactiveMass : R₀.activeMass = R₁.activeMass)
    (htarget : R₀.target = R₁.target) :
    R₀.beta = R₁.beta := by
  funext h
  cases h with
  | none =>
      unfold HeadSimplexReserve.beta
      unfold HeadSimplexReserve.zeroCoefficient
      rw [hexponent, hactiveMass, htarget]
  | some p =>
      unfold HeadSimplexReserve.beta
      rw [hexponent, hactiveMass, htarget]

/-! ## Eventual transport between two fixed-rich sources -/

set_option maxHeartbeats 1600000 in
/-- Two fixed-numerical rich-source witnesses on arbitrary meshes have the
same three literal source-first scalar values on a common tail.

The theorem contains no scalar family and assumes no analytic ledger.  It
only compares the local formulas which a separately chosen reference-mesh
ledger can then synchronize with every final-mesh source. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_fixedRichSource_crossMeshScalarTransport
    {delta₀ eta₀ delta₁ eta₁ : Real}
    (M₀ : RegularRelativeMesh.Mesh delta₀ eta₀)
    (M₁ : RegularRelativeMesh.Mesh delta₁ eta₁)
    {c deltaStar betaProt betaAct sourceCellMargin : Real}
    {depth N W K0 E : Nat}
    (hdelta₀ : 0 < delta₀)
    (hdelta₁ : 0 < delta₁)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (X₀ :
      BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
        M₀ (c := c) (deltaStar := deltaStar)
          (betaProt := betaProt) (betaAct := betaAct)
          (sourceCellMargin := sourceCellMargin)
          (depth := depth) (N := N) (W := W) (K0 := K0) (E := E)
          hdelta₀ F)
    (X₁ :
      BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
        M₁ (c := c) (deltaStar := deltaStar)
          (betaProt := betaProt) (betaAct := betaAct)
          (sourceCellMargin := sourceCellMargin)
          (depth := depth) (N := N) (W := W) (K0 := K0) (E := E)
          hdelta₁ F) :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let Y₀ := X₀.source n hn
        let Y₁ := X₁.source n hn
        let B₀ := Y₀.1
        let B₁ := Y₁.1
        let R₀ := Y₀.2.1.1
        let R₁ := Y₁.2.1.1
        let certificate₀ := Y₀.2.1.2
        let certificate₁ := Y₁.2.1.2
        let T₀ := Y₀.2.2
        let T₁ := Y₁.2.2
        let alpha₀ :=
          bankPaperCanonicalPostHfitBalancedAlpha
            B₀ c K0 betaProt betaAct
        let alpha₁ :=
          bankPaperCanonicalPostHfitBalancedAlpha
            B₁ c K0 betaProt betaAct
        let qTilde :=
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n
        bankPaperCanonicalTopFrozenSmoothFrozenMass
              (K := K0 + 1) B₀ R₀ certificate₀
                deltaStar betaProt alpha₀ =
            bankPaperCanonicalTopFrozenSmoothFrozenMass
              (K := K0 + 1) B₁ R₁ certificate₁
                deltaStar betaProt alpha₁ ∧
          bankPaperCanonicalSectionNinePostHeightLogY
                B₀ R₀ certificate₀ =
            bankPaperCanonicalSectionNinePostHeightLogY
                B₁ R₁ certificate₁ ∧
          bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                (K0 + 1) B₀ R₀ certificate₀ T₀
                  deltaStar betaProt alpha₀
                    (betaProt + betaAct) qTilde =
            bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                (K0 + 1) B₁ R₁ certificate₁ T₁
                  deltaStar betaProt alpha₁
                    (betaProt + betaAct) qTilde := by
  filter_upwards [
      X₀.ready_event, X₁.ready_event,
      X₀.canonical_event, X₁.canonical_event] with
      n hready₀ hready₁ hcanonical₀ hcanonical₁
  intro hn
  have hready₀n := hready₀ hn
  have hready₁n := hready₁ hn
  have hcanonical₀n := hcanonical₀ hn
  have hcanonical₁n := hcanonical₁ hn
  rcases hZ₀ : X₀.sourceGeom n hn with
    ⟨D₀, hnTail₀, hnD₀, hWD₀, S₀, hlo₀, hhi₀, Rcore₀⟩
  rcases hZ₁ : X₁.sourceGeom n hn with
    ⟨D₁, hnTail₁, hnD₁, hWD₁, S₁, hlo₁, hhi₁, Rcore₁⟩
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  let Kphysical :=
    bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
  have hw₀ : 0 < delta₀ + eta₀ :=
    add_pos hdelta₀ (M₀.ratio_pos.trans_le M₀.ratio_le_eta)
  have hw₁ : 0 < delta₁ + eta₁ :=
    add_pos hdelta₁ (M₁.ratio_pos.trans_le M₁.ratio_le_eta)
  let Tsource₀ :=
    bankPaperCanonicalSectionNineCoherentSourceTarget
      M₀ D₀ I hlo₀ hhi₀ Rcore₀ Kphysical
        hdelta₀ hnD₀ hWD₀ S₀ hw₀
  let Tsource₁ :=
    bankPaperCanonicalSectionNineCoherentSourceTarget
      M₁ D₁ I hlo₁ hhi₁ Rcore₁ Kphysical
        hdelta₁ hnD₁ hWD₁ S₁ hw₁
  let Bsource₀ :=
    bankPaperCanonicalSectionNineCoherentSourceBridge
      M₀ D₀ I hlo₀ hhi₀ Rcore₀ Kphysical
        hdelta₀ hnD₀ hWD₀ S₀ hw₀
  let Bsource₁ :=
    bankPaperCanonicalSectionNineCoherentSourceBridge
      M₁ D₁ I hlo₁ hhi₁ Rcore₁ Kphysical
        hdelta₁ hnD₁ hWD₁ S₁ hw₁
  have hprojection₀ :
      X₀.source n hn =
        ⟨Bsource₀,
          ⟨⟨F.realization D₀.n hnTail₀,
              F.certificate D₀.n hnTail₀⟩,
            Tsource₀⟩⟩ := by
    rw [X₀.projection n hn]
    simp only [
      bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich,
      hZ₀]
    rfl
  have hprojection₁ :
      X₁.source n hn =
        ⟨Bsource₁,
          ⟨⟨F.realization D₁.n hnTail₁,
              F.certificate D₁.n hnTail₁⟩,
            Tsource₁⟩⟩ := by
    rw [X₁.projection n hn]
    simp only [
      bankPaperCanonicalSectionNinePostHeight_fixedRichThinOfRich,
      hZ₁]
    rfl
  rw [hprojection₀] at hready₀n hcanonical₀n
  rw [hprojection₁] at hready₁n hcanonical₁n
  dsimp only at hready₀n hready₁n hcanonical₀n hcanonical₁n
  rcases hcanonical₀n with
    ⟨hsep₀, hremaining₀, hDcanonical₀, _hguard₀⟩
  rcases hcanonical₁n with
    ⟨hsep₁, hremaining₁, hDcanonical₁, _hguard₁⟩
  have hDcanonical₀' :
      D₀ =
        canonicalSampleData
          (W := W)
          (PaperHeadSimplex.pattern (primesUpTo W)
            (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E)
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          (roughCanonicalBridgeRelevantLedgerFamily depth n)
          hsep₀ hremaining₀ := by
    simpa only [
      Bsource₀,
      bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData] using
        hDcanonical₀
  have hDcanonical₁' :
      D₁ =
        canonicalSampleData
          (W := W)
          (PaperHeadSimplex.pattern (primesUpTo W)
            (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E)
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
          (roughCanonicalBridgeRelevantLedgerFamily depth n)
          hsep₁ hremaining₁ := by
    simpa only [
      Bsource₁,
      bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData] using
        hDcanonical₁
  have hsep : hsep₀ = hsep₁ := Subsingleton.elim _ _
  have hremaining : hremaining₀ = hremaining₁ :=
    Subsingleton.elim _ _
  have hD : D₀ = D₁ := by
    calc
      D₀ =
          canonicalSampleData
            (W := W)
            (PaperHeadSimplex.pattern (primesUpTo W)
              (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E)
            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
            (roughCanonicalBridgeRelevantLedgerFamily depth n)
            hsep₀ hremaining₀ :=
        hDcanonical₀'
      _ =
          canonicalSampleData
            (W := W)
            (PaperHeadSimplex.pattern (primesUpTo W)
              (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E)
            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
            (roughCanonicalBridgeRelevantLedgerFamily depth n)
            hsep₁ hremaining₁ := by
        rw [hsep, hremaining]
      _ = D₁ := hDcanonical₁'.symm
  cases hD
  have hTail : hnTail₀ = hnTail₁ := Subsingleton.elim _ _
  cases hTail
  rcases hready₀n with
    ⟨_hDn₀, _htargetBounds₀, _hWB₀, _Sready₀,
      hloReady₀, hhiReady₀, Rhead₀, Kready₀,
      hE₀, htarget₀, hmass₀, _hsourceMargin₀, hTready₀⟩
  rcases hready₁n with
    ⟨_hDn₁, _htargetBounds₁, _hWB₁, _Sready₁,
      hloReady₁, hhiReady₁, Rhead₁, Kready₁,
      hE₁, htarget₁, hmass₁, _hsourceMargin₁, hTready₁⟩
  have hRheadExponent :
      Rhead₀.exponent = Rhead₁.exponent :=
    hE₀.trans hE₁.symm
  have hRheadMass :
      Rhead₀.activeMass = Rhead₁.activeMass :=
    hmass₀.symm.trans hmass₁
  have hRheadTarget :
      Rhead₀.target = Rhead₁.target := by
    funext p
    exact (htarget₀ p).trans (htarget₁ p).symm
  have hRheadBeta :
      Rhead₀.beta = Rhead₁.beta :=
    HeadSimplexReserve.beta_eq_of_exponent_activeMass_target_eq
      Rhead₀ Rhead₁ hRheadExponent hRheadMass hRheadTarget
  have hTbeta₀ : Tsource₀.beta = Rhead₀.beta := by
    rw [hTready₀]
    rfl
  have hTbeta₁ : Tsource₁.beta = Rhead₁.beta := by
    rw [hTready₁]
    rfl
  have hTbeta : Tsource₀.beta = Tsource₁.beta :=
    hTbeta₀.trans (hRheadBeta.trans hTbeta₁.symm)
  have hTmu : Tsource₀.mu = Tsource₁.mu := by
    rfl
  let qTilde :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar n
  have hseed :
      bankPaperCanonicalScaledActiveSeed Tsource₀ qTilde =
        bankPaperCanonicalScaledActiveSeed Tsource₁ qTilde :=
    bankPaperCanonicalScaledActiveSeed_eq_of_beta_mu_eq
      Tsource₀ Tsource₁ qTilde hTbeta hTmu
  let alpha₀ :=
    bankPaperCanonicalPostHfitBalancedAlpha
      Bsource₀ c K0 betaProt betaAct
  let alpha₁ :=
    bankPaperCanonicalPostHfitBalancedAlpha
      Bsource₁ c K0 betaProt betaAct
  have halpha : alpha₀ = alpha₁ := by
    rfl
  have hmFrozen :
      bankPaperCanonicalTopFrozenSmoothFrozenMass
            (K := K0 + 1) Bsource₀
              (F.realization D₀.n hnTail₀)
              (F.certificate D₀.n hnTail₀)
              deltaStar betaProt alpha₀ =
        bankPaperCanonicalTopFrozenSmoothFrozenMass
            (K := K0 + 1) Bsource₁
              (F.realization D₀.n hnTail₀)
              (F.certificate D₀.n hnTail₀)
              deltaStar betaProt alpha₁ := by
    rfl
  have hlogY :
      bankPaperCanonicalSectionNinePostHeightLogY
            Bsource₀
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀) =
        bankPaperCanonicalSectionNinePostHeightLogY
            Bsource₁
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀) := by
    rfl
  have hnearest :
      bankPaperCanonicalTopFrozenNearestIntegerCellMass
            (K := K0 + 1) Bsource₀
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            deltaStar betaProt alpha₀ qTilde =
        bankPaperCanonicalTopFrozenNearestIntegerCellMass
            (K := K0 + 1) Bsource₁
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            deltaStar betaProt alpha₁ qTilde := by
    unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
    unfold bankPaperCanonicalTopFrozenRoundedActiveMass
    rw [hmFrozen]
  have hroundedSeed :
      bankPaperCanonicalTopFrozenRoundedActiveSeed
            (K := K0 + 1) Bsource₀
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            Tsource₀ deltaStar betaProt alpha₀ qTilde =
        bankPaperCanonicalTopFrozenRoundedActiveSeed
            (K := K0 + 1) Bsource₁
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            Tsource₁ deltaStar betaProt alpha₁ qTilde := by
    unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
    simp only [
      Bsource₀, Bsource₁,
      bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData]
    rw [hseed, hnearest]
  have hroundedSelector :
      bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) Bsource₀
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            Tsource₀ deltaStar betaProt alpha₀
              (betaProt + betaAct) qTilde =
        bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) Bsource₁
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            Tsource₁ deltaStar betaProt alpha₁
              (betaProt + betaAct) qTilde := by
    unfold bankPaperCanonicalTopFrozenRoundedSourceSelector
    rw [hroundedSeed]
    rfl
  have hLambda0 :
      bankPaperCanonicalSectionNinePostHeightRoundedLambda0
            (K0 + 1) Bsource₀
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            Tsource₀ deltaStar betaProt alpha₀
              (betaProt + betaAct) qTilde =
        bankPaperCanonicalSectionNinePostHeightRoundedLambda0
            (K0 + 1) Bsource₁
            (F.realization D₀.n hnTail₀)
            (F.certificate D₀.n hnTail₀)
            Tsource₁ deltaStar betaProt alpha₁
              (betaProt + betaAct) qTilde := by
    unfold bankPaperCanonicalSectionNinePostHeightRoundedLambda0
    simp only [
      Bsource₀, Bsource₁,
      bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData]
    rw [hroundedSelector, hroundedSeed]
  rw [hprojection₀, hprojection₁]
  exact ⟨hmFrozen, hlogY, hLambda0⟩

end BankPaperRealization

end

end Erdos390.WholePaper
