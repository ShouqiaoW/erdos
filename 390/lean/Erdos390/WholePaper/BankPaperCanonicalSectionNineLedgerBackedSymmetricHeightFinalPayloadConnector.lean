import Erdos390.WholePaper.BankPaperCanonicalSectionNineSymmetricHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineLedgerBackedWitnesswiseFinalPayloadConnector

/-!
# Ledger-backed symmetric-height Section 9 completion

The symmetric-height connector exposes both the legacy rounded-source local
input and the primary weak source-state local input.  Their corresponding
witnesswise connectors ask eventually for the matching generic suppliers.
These interfaces line up exactly: after the capacity bank and certificate
have been selected, symmetric-height packages may be supplied for those
same witnesses and converted pointwise to the appropriate generic input.

This file records both quantifier lifts and substitutes them into their
ledger-backed witnesswise completions.  The Section 8 ledger and canonical
scaled-seed alignment remain explicit.  The numerical continuation still
starts only after the positive bridge-mass constant `Cq` is known, so the
tangent-constant, mesh-width, `sigma`, and `Cpost` dependency order is
unchanged and non-circular.  Every bridge-index/width synchronization and
local supplier assertion is eventual; in particular, no impossible
sample-index equality is asserted at the exceptional index `n = 0`.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Eventual symmetric-height supplier -/

/-- Eventual symmetric-height data for the exact capacity witnesses selected
at each index.

The quantifier order is identical to
`BankPaperCanonicalSectionNinePostHfitLocalSupplier`: the canonical
partition is fixed first, then the supplier receives the selected bank
realization and guarded certificate together with the four capacity facts.
Its conclusion is only the three finite packages consumed by the
symmetric-height local-input connector. -/
def BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ hW : (B n).sampleData.W ≠ 0,
      ∃ Sscale : ScaleSeparation M
          (B n).sampleData.n (B n).sampleData.W,
        (B n).partition =
            RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta (B n).n_gt_one hW Sscale ∧
          ∀ (R : BankPaperRealization (B n).sampleData.n
                (upperEndpoint (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              (B n).sampleData.n R.anchorGuardLeftCore
              R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
            centralAnchorDivisor (B n).sampleData.n
                  (centralAnchorCutoff depth (B n).sampleData.n)
                  certificate.q * R.prechargeBaseStateProduct ∣
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            (baseBankFactors R.exactificationState).prod id ∣
                certificate.prechargedTailTarget →
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
                certificate.prechargedTailTarget →
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            ∃ Hsource :
                BankPaperCanonicalSectionNineSymmetricHeightSourceInputsAt
                  (B n) R certificate K0 deltaStar,
              ∃ Hanalytic :
                  BankPaperCanonicalSectionNineSymmetricHeightP87InputsAt
                    (B n) R certificate K0 deltaStar Cpost Hsource,
                Nonempty
                  (BankPaperCanonicalSectionNineSymmetricHeightSlackInputsAt
                    (B n) R certificate K0 deltaStar sigma Cpost
                      Hsource Hanalytic)

/-- Lift the finite symmetric-height constructor through the exact eventual
witnesswise quantifiers.

No capacity fact is discarded or repackaged: the same four facts are passed
to the symmetric-height supplier, and the three returned packages are
assembled for that same `R` and `certificate`. -/
theorem bankPaperCanonicalSectionNinePostHfitLocalSupplier_of_symmetricHeight
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (Hsymmetric :
      BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNinePostHfitLocalSupplier
      M B c depth K0 deltaStar sigma Cpost hdelta := by
  unfold BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
    at Hsymmetric
  unfold BankPaperCanonicalSectionNinePostHfitLocalSupplier
  filter_upwards [Hsymmetric] with n HsymmetricN
  obtain ⟨hW, Sscale, hpartition, Hlocal⟩ := HsymmetricN
  refine ⟨hW, Sscale, hpartition, ?_⟩
  intro R certificate hcombined hbaseDvd hchargeDvd htargetTail
  obtain ⟨Hsource, Hanalytic, ⟨Hslack⟩⟩ :=
    Hlocal R certificate hcombined hbaseDvd hchargeDvd htargetTail
  exact
    bankPaperCanonicalSectionNinePostHfitLocalInputsAt_of_symmetricHeight
      (B n) R certificate deltaStar sigma Cpost
        Hsource Hanalytic Hslack

/-! ## Eventual source-state symmetric-height supplier -/

/-- Eventual weak symmetric-height data for the exact capacity witnesses
selected at each index.

The returned source package contains only the minimal selector source state,
and the P87/slack tail is represented by the single dependent package from
the finite weak connector. -/
def BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ hW : (B n).sampleData.W ≠ 0,
      ∃ Sscale : ScaleSeparation M
          (B n).sampleData.n (B n).sampleData.W,
        (B n).partition =
            RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta (B n).n_gt_one hW Sscale ∧
          ∀ (R : BankPaperRealization (B n).sampleData.n
                (upperEndpoint (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              (B n).sampleData.n R.anchorGuardLeftCore
              R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
            centralAnchorDivisor (B n).sampleData.n
                  (centralAnchorCutoff depth (B n).sampleData.n)
                  certificate.q * R.prechargeBaseStateProduct ∣
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            (baseBankFactors R.exactificationState).prod id ∣
                certificate.prechargedTailTarget →
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
                certificate.prechargedTailTarget →
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            ∃ Hsource :
                BankPaperCanonicalSectionNineSymmetricHeightSourceStateInputsAt
                  (B n) R certificate K0 deltaStar,
              Nonempty
                (BankPaperCanonicalSectionNineSymmetricHeightDependentInputsAt
                  (B n) R certificate K0 deltaStar sigma Cpost Hsource)

/-- Lift the weak finite symmetric-height constructor through the exact
eventual witnesswise quantifiers. -/
theorem
    bankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier_of_symmetricHeight
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (Hsymmetric :
      BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
      M B c depth K0 deltaStar sigma Cpost hdelta := by
  unfold
    BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
    at Hsymmetric
  unfold BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
  filter_upwards [Hsymmetric] with n HsymmetricN
  obtain ⟨hW, Sscale, hpartition, Hlocal⟩ := HsymmetricN
  refine ⟨hW, Sscale, hpartition, ?_⟩
  intro R certificate hcombined hbaseDvd hchargeDvd htargetTail
  obtain ⟨Hsource, ⟨Hdependent⟩⟩ :=
    Hlocal R certificate hcombined hbaseDvd hchargeDvd htargetTail
  exact
    bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_symmetricHeight
      (B n) R certificate deltaStar sigma Cpost Hsource Hdependent

end BankPaperRealization

/-! ## Ledger-backed symmetric-height completion -/

/-- The ledger-backed witnesswise completion with its generic local supplier
replaced by the three symmetric-height packages.

The bridge family and mesh are fixed before the Section 8 big-O constant is
extracted.  After a positive `Cq` is supplied, the continuation chooses all
coupled numerical data and returns a symmetric-height supplier for the
exact capacity witnesses.  Both the scaled-seed alignment and the ambient
index/width synchronization are tail statements in `atTop`, not global
equalities of the bridge family. -/
def
    BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
  ∃ delta eta : Real,
    ∃ M : RegularRelativeMesh.Mesh delta eta,
      ∃ P : Finset Nat,
        ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          ∃ K0 smoothK : Nat,
            ∃ betaAct : Real,
              ∃ logY Lambda0 mFrozen qTilde : Nat → Real,
                ∃ hdelta : 0 < delta,
                  BankPaperCanonicalSectionEightAnalyticLedger
                    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
                      (upperTailLength c n) smoothK betaAct)
                    qTilde
                    (bankPaperCanonicalSmoothA0Family
                      logY Lambda0 mFrozen qTilde) ∧
                  (∀ᶠ n : Nat in atTop,
                    ∃ T : BarycentricTarget (B n).sampleData,
                      ∀ m : (B n).sampleData.Sample,
                        (B n).baseline.baseWeight m =
                          bankPaperCanonicalScaledActiveSeed T
                            (bankPaperCanonicalSmoothQ0Family
                              mFrozen qTilde n) m) ∧
                  (∀ᶠ n : Nat in atTop,
                    (B n).sampleData.n = n ∧
                      (B n).sampleData.W = W) ∧
                  ∀ Cq : Real, 0 < Cq →
                    ∃ tangentConstant sigma Cpost : Real,
                      0 < tangentConstant ∧
                      0 < sigma ∧
                      delta + M.ratio ≤
                        bankPaperCanonicalRatioCellPaperWidthChoice
                          (tangentPaperCleanListDensity W r0)
                          sigma (21 / 20 : Real) tangentConstant ∧
                      0 ≤ Cpost ∧
                      (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                      BankPaperRealization.BankPaperCanonicalSectionNineSymmetricHeightLocalSupplier
                        M B c depth K0 deltaStar sigma Cpost hdelta

/-! ## Ledger-backed source-state symmetric-height completion -/

/-- The ledger-backed symmetric-height completion with its final callback
expressed through the weak source-state source and combined dependent tail.

All ledger and numerical fields are identical to the legacy symmetric-height
completion. -/
def
    BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
  ∃ delta eta : Real,
    ∃ M : RegularRelativeMesh.Mesh delta eta,
      ∃ P : Finset Nat,
        ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          ∃ K0 smoothK : Nat,
            ∃ betaAct : Real,
              ∃ logY Lambda0 mFrozen qTilde : Nat → Real,
                ∃ hdelta : 0 < delta,
                  BankPaperCanonicalSectionEightAnalyticLedger
                    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
                      (upperTailLength c n) smoothK betaAct)
                    qTilde
                    (bankPaperCanonicalSmoothA0Family
                      logY Lambda0 mFrozen qTilde) ∧
                  (∀ᶠ n : Nat in atTop,
                    ∃ T : BarycentricTarget (B n).sampleData,
                      ∀ m : (B n).sampleData.Sample,
                        (B n).baseline.baseWeight m =
                          bankPaperCanonicalScaledActiveSeed T
                            (bankPaperCanonicalSmoothQ0Family
                              mFrozen qTilde n) m) ∧
                  (∀ᶠ n : Nat in atTop,
                    (B n).sampleData.n = n ∧
                      (B n).sampleData.W = W) ∧
                  ∀ Cq : Real, 0 < Cq →
                    ∃ tangentConstant sigma Cpost : Real,
                      0 < tangentConstant ∧
                      0 < sigma ∧
                      delta + M.ratio ≤
                        bankPaperCanonicalRatioCellPaperWidthChoice
                          (tangentPaperCleanListDensity W r0)
                          sigma (21 / 20 : Real) tangentConstant ∧
                      0 ≤ Cpost ∧
                      (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                      BankPaperRealization.BankPaperCanonicalSectionNineSymmetricHeightSourceStateLocalSupplier
                        M B c depth K0 deltaStar sigma Cpost hdelta

/-! ## Exact interface conversion -/

/-- Pointwise symmetric-height suppliers construct the generic local
supplier required by the ledger-backed witnesswise connector. -/
theorem
    bankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion_of_symmetricHeight
    {c : Real} {depth W : Nat} {r0 deltaStar : Real}
    (Hcompletion :
      BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar) :
    BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
      c depth W r0 deltaStar := by
  unfold
    BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
    at Hcompletion
  obtain
      ⟨delta, eta, M, P, B, K0, smoothK, betaAct, logY, Lambda0,
        mFrozen, qTilde, hdelta, Hledger, hseed, hsync, Hnumerical⟩ :=
    Hcompletion
  unfold
    BankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion
  refine
    ⟨delta, eta, M, P, B, K0, smoothK, betaAct, logY, Lambda0,
      mFrozen, qTilde, hdelta, Hledger, hseed, hsync, ?_⟩
  intro Cq hCq
  obtain
      ⟨tangentConstant, sigma, Cpost, htangent, hsigma, hwidth,
        hCpost, hcoefficient, Hsymmetric⟩ :=
    Hnumerical Cq hCq
  exact
    ⟨tangentConstant, sigma, Cpost, htangent, hsigma, hwidth,
      hCpost, hcoefficient,
      BankPaperRealization.bankPaperCanonicalSectionNinePostHfitLocalSupplier_of_symmetricHeight
        M B c depth K0 deltaStar sigma Cpost hdelta Hsymmetric⟩

/-! ## Exact source-state interface conversion -/

/-- Pointwise weak symmetric-height suppliers construct the generic
source-state local supplier required by the ledger-backed weak connector. -/
theorem
    bankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion_of_symmetricHeight
    {c : Real} {depth W : Nat} {r0 deltaStar : Real}
    (Hcompletion :
      BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
        c depth W r0 deltaStar) :
    BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
      c depth W r0 deltaStar := by
  unfold
    BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
    at Hcompletion
  obtain
      ⟨delta, eta, M, P, B, K0, smoothK, betaAct, logY, Lambda0,
        mFrozen, qTilde, hdelta, Hledger, hseed, hsync, Hnumerical⟩ :=
    Hcompletion
  unfold
    BankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion
  refine
    ⟨delta, eta, M, P, B, K0, smoothK, betaAct, logY, Lambda0,
      mFrozen, qTilde, hdelta, Hledger, hseed, hsync, ?_⟩
  intro Cq hCq
  obtain
      ⟨tangentConstant, sigma, Cpost, htangent, hsigma, hwidth,
        hCpost, hcoefficient, Hsymmetric⟩ :=
    Hnumerical Cq hCq
  exact
    ⟨tangentConstant, sigma, Cpost, htangent, hsigma, hwidth,
      hCpost, hcoefficient,
      BankPaperRealization.bankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier_of_symmetricHeight
        M B c depth K0 deltaStar sigma Cpost hdelta Hsymmetric⟩

/-! ## Parameter-synchronized terminal -/

/-- The full parameter-synchronized Section 9 terminal from a callback whose
remaining finite input is expressed only through the three symmetric-height
packages. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
    {c : Real} (hc : C0 < c)
    (Hcompletion :
      ∀ (depth W : Nat) (r0 deltaStar : Real),
        201 ≤ depth →
        2 ≤ W →
        2 * depth + 1 ≤ W →
        fullReciprocalSumUniformCutoff ≤ W →
        canonicalActualMomentCutoff ≤ W →
        1 < r0 →
        r0 < 3 / 2 →
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
          BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
            c depth W r0 deltaStar) :
    ∃ depth W : Nat, ∃ r0 deltaStar : Real,
      201 ≤ depth ∧
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        1 < r0 ∧
        r0 < 3 / 2 ∧
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar ∧
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
        BankPaperCanonicalDistributedSectionNineTerminalAtDepth
          c deltaStar depth := by
  apply
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedWitnesswiseAnalyticCompletion
      hc
  intro depth W r0 deltaStar hdepth hWtwo hprefix hMertens hMoment
    hr0one hr0three hdeltaStar
  exact
    bankPaperCanonicalSectionNineLedgerBackedWitnesswiseAnalyticCompletion_of_symmetricHeight
      (Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix hMertens
        hMoment hr0one hr0three hdeltaStar)

/-! ## Source-state parameter-synchronized terminal -/

/-- The full parameter-synchronized Section 9 terminal from a callback
expressed through only the weak symmetric-height source-state packages. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
    {c : Real} (hc : C0 < c)
    (Hcompletion :
      ∀ (depth W : Nat) (r0 deltaStar : Real),
        201 ≤ depth →
        2 ≤ W →
        2 * depth + 1 ≤ W →
        fullReciprocalSumUniformCutoff ≤ W →
        canonicalActualMomentCutoff ≤ W →
        1 < r0 →
        r0 < 3 / 2 →
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
          BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
            c depth W r0 deltaStar) :
    ∃ depth W : Nat, ∃ r0 deltaStar : Real,
      201 ≤ depth ∧
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        1 < r0 ∧
        r0 < 3 / 2 ∧
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar ∧
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
        BankPaperCanonicalDistributedSectionNineTerminalAtDepth
          c deltaStar depth := by
  apply
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
      hc
  intro depth W r0 deltaStar hdepth hWtwo hprefix hMertens hMoment
    hr0one hr0three hdeltaStar
  exact
    bankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion_of_symmetricHeight
      (Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix hMertens
        hMoment hr0one hr0three hdeltaStar)

/-! ## Global main-asymptotic wrapper -/

/-- Ledger-backed symmetric-height completions at every paper scale imply the
literal small-`o` main theorem.

For each `c > C0`, parameter synchronization is allowed to choose its own
capacity depth together with `W`, `r0`, and `deltaStar`.  The distributed
terminal at that selected depth gives the eventual upper endpoint directly;
no externally fixed depth or comparison between independently selected depths
is required. -/
theorem
    mainAsymptotic_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
    (Hcompletion :
      ∀ (c : Real), C0 < c →
        ∀ (depth W : Nat) (r0 deltaStar : Real),
          201 ≤ depth →
          2 ≤ W →
          2 * depth + 1 ≤ W →
          fullReciprocalSumUniformCutoff ≤ W →
          canonicalActualMomentCutoff ≤ W →
          1 < r0 →
          r0 < 3 / 2 →
          IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
            BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
              c depth W r0 deltaStar) :
    MainAsymptotic := by
  apply mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  obtain
      ⟨depth, W, r0, deltaStar, hdepth, _hWtwo, _hprefix,
        _hMertens, _hMoment, _hr0one, _hr0three, _hdeltaStar,
        _hcharge, hterminal⟩ :=
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload_of_ledgerBackedSymmetricHeightWitnesswiseAnalyticCompletion
      hc (Hcompletion c hc)
  exact
    eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
      hc hdepth hterminal

/-! ## Source-state global main-asymptotic wrapper -/

/-- Weak ledger-backed symmetric-height completions at every paper scale
imply the literal small-`o` main theorem. -/
theorem
    mainAsymptotic_of_ledgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
    (Hcompletion :
      ∀ (c : Real), C0 < c →
        ∀ (depth W : Nat) (r0 deltaStar : Real),
          201 ≤ depth →
          2 ≤ W →
          2 * depth + 1 ≤ W →
          fullReciprocalSumUniformCutoff ≤ W →
          canonicalActualMomentCutoff ≤ W →
          1 < r0 →
          r0 < 3 / 2 →
          IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
            BankPaperCanonicalSectionNineLedgerBackedSymmetricHeightSourceStateWitnesswiseAnalyticCompletion
              c depth W r0 deltaStar) :
    MainAsymptotic := by
  apply
    mainAsymptotic_of_ledgerBackedSourceStateWitnesswiseAnalyticCompletion
  intro c hc depth W r0 deltaStar hdepth hWtwo hprefix hMertens
    hMoment hr0one hr0three hdeltaStar
  exact
    bankPaperCanonicalSectionNineLedgerBackedSourceStateWitnesswiseAnalyticCompletion_of_symmetricHeight
      (Hcompletion c hc depth W r0 deltaStar hdepth hWtwo hprefix
        hMertens hMoment hr0one hr0three hdeltaStar)

end

end Erdos390.WholePaper
