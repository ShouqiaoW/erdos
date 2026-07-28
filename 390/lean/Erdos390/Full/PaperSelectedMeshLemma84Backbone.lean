import Erdos390.Full.PaperSelectedMeshSchurEventually
import Erdos390.Full.PaperActualFullEffectiveBall
import Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually

/-!
# Selected-mesh backbone for the full arithmetic Lemma 8.4 conclusion

This theorem nests the eventual nuisance--Schur terminal under the literal
selected dyadic mesh.  Consequently neither the actual-full projected
inverse nor the moving-low center envelope is an assumption of the final
certificate.  The only remaining analytic input is the sharp global marked
nuisance row; a separate canonical splice discharges that row from the
physical and head-tag estimates.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport
  SelectedDyadicRegularMesh

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

set_option maxHeartbeats 1800000 in
/-- A literal selected mesh, followed by `W`, followed by an arbitrary
effective-ball radius.  This order certifies that the Lemma 8.4 inverse does
not choose `W` after seeing the later ODE box. -/
theorem exists_selectedDyadicMesh_eventually_actualBandSchurCertificate
    [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (U : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank)
    (marginFloor : ℝ) (hmarginFloor : 0 < marginFloor) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cfull : ℝ, 0 < Cfull ∧
      ∃ K N : ℕ, ∃ hK : 3 ≤ K, ∃ hN : 0 < N,
        let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
        let anchors := SelectedDyadicRegularMesh.anchors hK hN
        ∃ anchor : Fin M.cellCount, anchor ∈ anchors ∧
          delta K < meshTol ∧
          (∀ k : Fin M.cellCount, M.width k < meshTol) ∧
          ∃ centerScale : ℝ, 0 < centerScale ∧
          ∃ W₀ : ℕ, 2 ≤ W₀ ∧
            ∀ W : ℕ, ∀ hWtwo : 2 ≤ W,
              ∀ _hWcutoff : W₀ ≤ W,
              ∀ _hmod : (∀ h, (Phead h).modulus ≤ W),
              ∀ (a : NNReal) (epsilon : ℕ → ℝ),
                (∀ n, 0 ≤ epsilon n) →
                Tendsto
                  (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
                    atTop (nhds 0) →
                ∀ᶠ n : ℕ in atTop,
                  ∀ (B : BridgeData Head (Fin (M.cellCount + 1)))
                    (_hBn : B.sampleData.n = n)
                    (hBW : B.sampleData.W = W)
                    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                      physicalBound (I.lower .plus) B.sampleData.n)
                    (hremaining : ∀ c : Cell Head,
                      (PaperGuardCensus.rawCell Phead I B.sampleData.n c \
                        (ledger B.sampleData.n).guards).Nonempty)
                    (hcanonical : B.sampleData =
                      PaperGuardCensus.canonicalSampleData
                        (W := B.sampleData.W) Phead I
                          (ledger B.sampleData.n) hsep hremaining)
                    (_hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                        (S : RegularMeshPrimeCutoffs.ScaleSeparation
                          M B.sampleData.n B.sampleData.W),
                      B.partition =
                        RegularMeshPrimeCutoffs.Mesh.canonicalPartition M
                          (by
                            unfold SelectedDyadicRegularMesh.delta
                            positivity)
                          B.n_gt_one hWne S)
                    (T : PaperGuardCensus.BarycentricTarget B.sampleData)
                    (_hTmargin : marginFloor ≤ T.cellMassMargin)
                    (hbaseline : B.baseline = T.baseline)
                    (_hmarked : ∀ (z : B.EffectiveParamSpace)
                        (_hz : z ∈ closedBall
                          (0 : B.EffectiveParamSpace) (a : ℝ))
                        (c : NuisanceCoord B.HeadIndex)
                        (p : BandPrime B.sampleData.n B.sampleData.W),
                      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                        (fun m ↦ B.nuisanceStatistic m c)
                        (fun m ↦ valuation p.1
                          (B.sampleData.value m))| ≤
                        epsilon B.sampleData.n * (1 / (p.1 : ℝ))),
                    let hlo : ∀ sigma, B.sampleData.lo sigma =
                        physicalBound (I.lower sigma) B.sampleData.n := by
                      intro sigma
                      rw [hcanonical]
                      rfl
                    let hhi : ∀ sigma, B.sampleData.hi sigma =
                        physicalBound (I.upper sigma) B.sampleData.n := by
                      intro sigma
                      rw [hcanonical]
                      rfl
                    ActualBandSchurCertificate B I U a T Cfull centerScale
                      (epsilon B.sampleData.n) hU hlowerOne hupperU hlo hhi
                      hbaseline (by omega) := by
  obtain ⟨kappa, hkappa, meshTol, hmeshTol, Cfull, hCfull,
      K, N, hK, hN, anchor, hanchor, hdeltaFine, hwidthFine,
      Wfull, hfullSelected⟩ :=
    exists_selectedDyadicMesh_eventually_actualFullProjected_inverse
      Phead I U hlowerOne hupperU Cprom Cbank ledger
  let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
  have hdelta : 0 < delta K := by
    unfold delta
    positivity
  obtain ⟨centerScale, hcenterScale, Wcenter, hcenterEvent⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_center_lower_logL
      M hdelta
  refine ⟨kappa, hkappa, meshTol, hmeshTol, Cfull, hCfull,
    K, N, hK, hN, anchor, hanchor, hdeltaFine, hwidthFine,
    centerScale, hcenterScale, max 2 (max Wfull Wcenter),
    le_max_left 2 _, ?_⟩
  intro W hWtwo hWcutoff hmod a epsilon hepsilonNonneg hepsilonRate
  have hWfull : Wfull ≤ W :=
    ((le_max_left Wfull Wcenter).trans (le_max_right 2 _)).trans hWcutoff
  have hWcenter : Wcenter ≤ W :=
    ((le_max_right Wfull Wcenter).trans (le_max_right 2 _)).trans hWcutoff
  have hWone : 1 < W := by omega
  have hfullEvent := hfullSelected W hWfull hmod
    (3 * (a : ℝ)) (3 * (a : ℝ)) (by positivity) (by positivity)
  have hcenterN := hcenterEvent W hWcenter
  have hschurEvent := eventually_actualBandSchurCertificate
    (Head := Head) (Band := Fin (M.cellCount + 1))
    I hU hlowerOne hupperU W hWone a marginFloor centerScale Cfull
      hmarginFloor hcenterScale hCfull epsilon hepsilonNonneg hepsilonRate
  filter_upwards [hfullEvent, hcenterN, hschurEvent] with n hfullN hcenterAtN
      hschurN
  intro B hBn hBW hsep hremaining hcanonical hpartition T hTmargin
    hbaseline hmarked
  subst n
  subst W
  obtain ⟨hWne, S, hpartitionCanonical⟩ := hpartition
  have hpoint : ∀ (xi : B.ParamSpace),
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p| ≤ 3 * (a : ℝ)) →
      |xi MomentCoord.physical| ≤ 3 * (a : ℝ) →
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
    intro xi heta hphys
    exact hfullN B xi rfl rfl hsep hremaining hcanonical
      ⟨hWne, S, hpartitionCanonical⟩ heta hphys
  obtain ⟨fullEquiv, hfull, hinvFull⟩ :=
    B.exists_actualFullProjectedEquiv_on_closedBall_of_box a hpoint
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hcenter : ∀ i : Fin (M.cellCount + 1),
      centerScale / Real.log (Scale.L B.sampleData.n) ≤
        B.bandCenter i := by
    intro i
    change centerScale / Real.log (Scale.L B.sampleData.n) ≤
      B.partition.center i
    rw [hpartitionCanonical]
    simpa only [M] using hcenterAtN B.n_gt_one hWne S i
  exact hschurN B rfl rfl T hTmargin hbaseline hlo hhi
    fullEquiv hfull hinvFull hcenter hmarked

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
