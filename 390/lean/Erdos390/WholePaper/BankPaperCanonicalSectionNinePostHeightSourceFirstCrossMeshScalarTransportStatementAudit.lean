import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCrossMeshScalarTransport

/-!
# Statement audit for cross-mesh source-first scalar transport

This audit reproduces the complete parameter order and literal eventual
conclusion of the cross-mesh transport theorem.  In particular, the two
meshes, their positive mesh widths, the common guarded-tail family, and the
two fixed-rich witnesses are all quantified before the common tail.  The
conclusion compares the local frozen-mass, precharged-logarithm, and rounded
frozen-logarithmic-mass formulas directly; it introduces no scalar family,
analytic ledger, post-height bridge, or downstream conclusion package.
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

/-! ## Literal helper interfaces -/

example
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
          hdelta₁ hn hW S₁ hw₁ :=
  bankPaperCanonicalSectionNineCoherentSourceTarget_mesh_invariant
    M₀ M₁ D I hlo hhi Rhead Kphysical
      hdelta₀ hdelta₁ hn hW S₀ S₁ hw₀ hw₁

example
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head}
    (T₀ T₁ : BarycentricTarget D)
    (q : Real)
    (hbeta : T₀.beta = T₁.beta)
    (hmu : T₀.mu = T₁.mu) :
    bankPaperCanonicalScaledActiveSeed T₀ q =
      bankPaperCanonicalScaledActiveSeed T₁ q :=
  bankPaperCanonicalScaledActiveSeed_eq_of_beta_mu_eq
    T₀ T₁ q hbeta hmu

example
    {P : Finset Nat}
    (R₀ R₁ : HeadSimplexReserve P)
    (hexponent : R₀.exponent = R₁.exponent)
    (hactiveMass : R₀.activeMass = R₁.activeMass)
    (htarget : R₀.target = R₁.target) :
    R₀.beta = R₁.beta :=
  HeadSimplexReserve.beta_eq_of_exponent_activeMass_target_eq
    R₀ R₁ hexponent hactiveMass htarget

/-! ## Complete expanded cross-mesh theorem assignment -/

set_option maxHeartbeats 1600000 in
example
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
  exact
    eventually_bankPaperCanonicalSectionNinePostHeight_fixedRichSource_crossMeshScalarTransport
      M₀ M₁ hdelta₀ hdelta₁ F X₀ X₁

end BankPaperRealization

end

end Erdos390.WholePaper
