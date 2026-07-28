import Erdos390.Full.PaperCanonicalActualSchurOrdinaryRowsEventually
import Erdos390.Full.PaperCanonicalMomentRatioEventually

/-!
# Final sharp-and-ordinary same-map form of Lemma 8.4

The endpoint arithmetic inverse, the literal actual Schur equivalence, the
canonical moment ratio, and all three ordinary perturbation rows are joined
here.  The public theorem has no anchor, profile, convergence, row-error,
smallness, or abstract inverse premise.  The equivalence in the two norm
bounds is definitionally the same object and is exactly the finite-`n`
actual Schur map throughout the selected effective ball.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs

namespace BridgeData

set_option maxHeartbeats 3000000 in
/--
Assumption-free canonical Lemma 8.4 terminal in both paper norms.

All numerical constants and the structural cutoff are chosen before the two
independent mesh parameters, the mesh itself, the finite head data, and the
effective tilt ball.  Only the final ambient threshold may depend on those
already fixed objects.
-/
theorem exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
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
                  ∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖ := by
  obtain ⟨Rproj, hRproj, ratioTol, hratioTol, Wratio, hRatio⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_momentRatio
  obtain ⟨connectorTol, hconnectorTol, Csharp, hCsharp,
      Cref, hCref, Wconnector, hConnector⟩ :=
    exists_paperFineMesh_cutoff_eventually_actualBandSchur_sameEquiv_sharp_and_ordinary_of_endpoint_inputs
  obtain ⟨Wrows, hRows⟩ :=
    exists_cutoff_eventually_canonical_ordinary_perturbation_rows
      Cref Rproj hCref hRproj.le
  let meshTol : ℝ := min ratioTol connectorTol
  let Cordinary : ℝ := 4 * Cref
  let W₀ : ℕ := max Wratio (max Wconnector Wrows)
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hratioTol hconnectorTol
  have hCordinary : 0 < Cordinary := by
    dsimp only [Cordinary]
    positivity
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp,
    Cordinary, hCordinary, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
    Head _instHead _instHeadDec _instHeadNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWratio : Wratio ≤ W :=
    (le_max_left Wratio _).trans hW
  have hWconnector : Wconnector ≤ W :=
    (le_max_left Wconnector Wrows).trans
      ((le_max_right Wratio _).trans hW)
  have hWrows : Wrows ≤ W :=
    (le_max_right Wconnector Wrows).trans
      ((le_max_right Wratio _).trans hW)
  have hRatioFine : delta + eta ≤ ratioTol :=
    hfine.trans (min_le_left ratioTol connectorTol)
  have hConnectorFine : delta + eta ≤ connectorTol :=
    hfine.trans (min_le_right ratioTol connectorTol)
  have hHeadLe : ∀ h : Head, ∀ p ∈ (Phead h).primes, p ≤ W := by
    intro h p hp
    exact (hPhead h p).mp hp |>.2
  have hRatioN := hRatio W hWratio M hdelta hRatioFine
    (Head := Head)
  have hConnectorN := hConnector W hWconnector M hdelta hConnectorFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hRowsN := hRows W hWrows Phead hHeadLe I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
      (Band := Fin (M.cellCount + 1))
  filter_upwards [hRatioN, hConnectorN, hRowsN] with
      n hRatioAt hConnectorAt hRowsAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    T hTmargin hbaseline
  have hRatioB := hRatioAt B hBn hBW hpartition
  obtain ⟨e, he, hsharp, hconditional⟩ :=
    hConnectorAt B hBn hBW hBWlarge hsep hremaining hcanonical
      hpartition T hTmargin hbaseline
  obtain ⟨hsquare, hfull, hschur⟩ :=
    hRowsAt B hBn hBW hBWlarge hsep hremaining hcanonical
      T hTmargin hbaseline hRatioB
  have hordinary := hconditional
    (Esquare := canonicalOrdinaryRowTolerance Cref Rproj)
    (Rpow := canonicalOrdinaryRowTolerance Cref Rproj)
    (Rproj := Rproj)
    (deltaSchur := canonicalOrdinarySchurTolerance Cref)
    (canonicalOrdinaryRowTolerance_pos hCref hRproj.le).le
    (canonicalOrdinaryRowTolerance_pos hCref hRproj.le).le
    hRproj.le hRatioB hsquare hfull
    (canonicalOrdinaryRows_small hCref hRproj.le)
    hschur (canonicalOrdinarySchur_small hCref)
  refine ⟨e, he, hsharp, ?_⟩
  intro z hz v
  simpa only [Cordinary] using hordinary z hz v

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
