import Erdos390.Full.PaperActualSchurEndpointReferenceTransport
import Erdos390.Full.PaperCanonicalPrimeGraphActualSchurEventually
import Erdos390.Full.CanonicalEndpointOrdinaryProjectedRawInverseEventually

/-!
# The same actual Schur equivalence in sharp and ordinary norm

This file composes two independent outputs of Lemma 8.4:

* the canonical prime-graph construction of the literal actual Schur
  equivalence, with its paper sharp-norm inverse; and
* the canonical endpoint arithmetic reference inverse in ordinary norm.

The deterministic endpoint connector then transfers the ordinary estimate
to the very same equivalence.  The remaining hypotheses are exactly the
four perturbative estimates displayed by that connector (moment ratio,
squarefree/reference row, full/squarefree row, and nuisance Schur error),
together with their explicit uniform smallness inequalities.  No anchor,
profile, or abstract inverse assumption is exposed.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs
open SquarefreeReferenceOperatorIdentification

namespace BridgeData

set_option maxHeartbeats 2000000 in
/--
Paper-scale, independent-`eta` endpoint-to-actual-Schur connector.

All structural constants and the cutoff are selected before the mesh and
the effective box.  The final ambient threshold may depend on the already
fixed finite data and box, exactly as in the source theorems.
-/
theorem exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary_of_endpoint_inputs :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cref : ℝ, 0 < Cref ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            ∀ (T : BarycentricTarget B.sampleData)
              (_hTmargin : marginFloor ≤ T.cellMassMargin)
              (hbaseline : B.baseline = T.baseline),
              ∃ e : ∀ (z : B.EffectiveParamSpace),
                  z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                    B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                  e z hz q =
                    B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                      (B.canonicalEffectiveNuisanceGamma_pos
                        I U (3 * (a : ℝ)) T)
                      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                        hU hlowerOne hupperU
                        (by intro sigma; rw [hcanonical]; rfl)
                        (by intro sigma; rw [hcanonical]; rfl)
                        T hbaseline hBWlarge z hz) q) ∧
                (∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      ((e z hz).symm v) ≤
                    Csharp *
                      paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) v) ∧
                ∀ {Esquare Rpow Rproj deltaSchur : ℝ},
                  0 ≤ Esquare → 0 ≤ Rpow → 0 ≤ Rproj →
                  (∑ j : Fin (M.cellCount + 1),
                      B.harmonicMass j * B.bandCenter j) ≤
                    Rproj * MovingLowGaugeTransfer.sharpWeightTotal
                      B.harmonicMass B.bandCenter →
                  (∀ (z : B.EffectiveParamSpace)
                      (_hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ))
                      (q : B.RawBandGauge) (i : Fin (M.cellCount + 1)),
                    |SquarefreeSharpBandTransfer.squarefreeBandRow
                        (B.actualValuationLaw (B.effectiveParamEquiv z))
                          B.partition q.1 i -
                      SquarefreeSharpBandTransfer.referenceBandRow
                        B.partition q.1 i| ≤ ‖q‖ * Esquare) →
                  (∀ (z : B.EffectiveParamSpace)
                      (_hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ))
                      (q : B.RawBandGauge) (i : Fin (M.cellCount + 1)),
                    |PrimePowerSharpBandTransfer.fullBandRow
                        (B.actualValuationLaw (B.effectiveParamEquiv z))
                          B.partition q.1 i -
                      SquarefreeSharpBandTransfer.squarefreeBandRow
                        (B.actualValuationLaw (B.effectiveParamEquiv z))
                          B.partition q.1 i| ≤ ‖q‖ * Rpow) →
                  Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2 →
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ))
                      (q : B.RawBandGauge),
                    ‖B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz) q -
                        B.actualBandFullLinearMap
                          (B.effectiveParamEquiv z) q‖ ≤
                      deltaSchur * ‖q‖) →
                  (2 * Cref) * deltaSchur ≤ 1 / 2 →
                  ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ (4 * Cref) * ‖v‖ := by
  obtain ⟨sharpTol, hsharpTol, Csharp, hCsharp, Wsharp, hSharp⟩ :=
    @exists_fineMesh_cutoff_eventually_actualBandSchur_primeGraph_inverse
  obtain ⟨Cref, hCref, refTol, hrefTol, Wref, hReference⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_paperFineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse
  let meshTol : ℝ := min sharpTol refTol
  let W₀ : ℕ := max Wsharp Wref
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hsharpTol hrefTol
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp,
    Cref, hCref, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
    Head _instHead _instHeadDec _instHeadNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWsharp : Wsharp ≤ W :=
    (le_max_left Wsharp Wref).trans hW
  have hWref : Wref ≤ W :=
    (le_max_right Wsharp Wref).trans hW
  have hSharpFine : delta + M.ratio ≤ sharpTol := by
    have hpaper : delta + eta ≤ sharpTol :=
      hfine.trans (min_le_left sharpTol refTol)
    linarith [M.ratio_le_eta]
  have hRefFine : delta + eta ≤ refTol :=
    hfine.trans (min_le_right sharpTol refTol)
  have hSharpN := hSharp W hWsharp M hdelta hSharpFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hReferenceN := hReference W hWref M hdelta hRefFine
  filter_upwards [hSharpN, hReferenceN] with n hSharpAt hReferenceAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline
  subst n
  subst W
  have hSharpB := hSharpAt B rfl rfl hBWlarge hsep hremaining
    hcanonical hpartition T hTmargin hbaseline
  obtain ⟨e, he, hsharp⟩ := hSharpB
  obtain ⟨hWrefNe, hnRef, Sref, hReferenceRaw⟩ := hReferenceAt
  let Pref := RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
    hnRef hWrefNe Sref
  let Eref := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta
    hnRef hWrefNe Sref
  have hReferenceRef :
      ∀ q : RawGaugeSpace Pref.mass Pref.center,
        ‖q‖ ≤ Cref *
          ‖projectedRawLinearMap
            (CompressedArithmeticOperator.arithmeticDiagonal
              (ArithmeticModel.y B.sampleData.n) Eref.lower Eref.upper)
            (CompressedArithmeticOperator.arithmeticKernel
              (ArithmeticModel.y B.sampleData.n) Eref.lower Eref.upper)
            Pref.mass Pref.center
            (by
              unfold MovingLowGaugeTransfer.sharpWeightTotal
                MovingLowGaugeTransfer.sharpWeight
              simpa only [Erdos390.Lemma84.WeightedBandData.centerEnergy,
                Erdos390.Lemma84.WeightedBandData.bandNormSq,
                Erdos390.Lemma84.WeightedBandData.bandInner, pow_two,
                mul_assoc] using
                  (Pref.centerEnergy_pos hnRef).ne') q‖ := by
    simpa only [Pref, Eref] using hReferenceRaw
  obtain ⟨hWuser, Suser, hpartitionUser⟩ := hpartition
  have hpartitionRef : B.partition = Pref := by
    exact hpartitionUser.trans (by dsimp only [Pref])
  refine ⟨e, he, hsharp, ?_⟩
  intro Esquare Rpow Rproj deltaSchur hEsquare hRpow hRproj hRatio
    hsquare hfull hSmallFull hSchurError hSmallSchur z hz v
  have hOrdinary :=
    B.actualBandSchur_sameEquiv_ordinary_inverse_of_partition_eq_endpoint_reference
      (B.effectiveParamEquiv z)
      (B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T)
      (B.canonicalEffectiveNuisanceGap_on_closedBall I a
        hU hlowerOne hupperU
        (by intro sigma; rw [hcanonical]; rfl)
        (by intro sigma; rw [hcanonical]; rfl)
        T hbaseline hBWlarge z hz)
      (e z hz) (he z hz) Pref hpartitionRef Eref hCref.le
      hEsquare hRpow hRproj hRatio hReferenceRef
      (hsquare z hz) (hfull z hz) hSmallFull
      (hSchurError z hz) hSmallSchur
  exact hOrdinary.2 v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
