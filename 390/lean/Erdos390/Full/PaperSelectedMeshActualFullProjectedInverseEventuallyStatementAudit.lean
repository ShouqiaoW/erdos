import Erdos390.Full.PaperSelectedMeshActualFullProjectedInverseEventually

/-!
# Exact statement-shape audit for the selected-mesh actual-full terminal

This restates the complete dependent type independently.  In particular it
checks, rather than merely describing, the order

`(kappa, meshTol, Cfull) -> explicit mesh -> W -> coefficient box -> n`,

and verifies that no reference inverse or comparison-row estimate is an
assumption of the terminal theorem.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperSelectedMeshActualFullProjectedInverseEventuallyStatementAudit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimeSums PaperWeightedInverseExport
open OmittedTiltPairChamber PaperPrimePowerChamberError
open SelectedDyadicRegularMesh
open PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

example [Nonempty Head]
    (Phead : Head → HeadPattern.Pattern)
    (I : PaperGuardCensus.PhysicalIntervals) (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, PaperGuardCensus.Ledger n Cprom Cbank) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cfull : ℝ, 0 < Cfull ∧
      ∃ K N : ℕ, ∃ hK : 3 ≤ K, ∃ hN : 0 < N,
        let M := mesh K N (lt_of_lt_of_le (by decide : 0 < 3) hK) hN
        let anchors := SelectedDyadicRegularMesh.anchors hK hN
        ∃ anchor : Fin M.cellCount, anchor ∈ anchors ∧
          delta K < meshTol ∧
          (∀ k : Fin M.cellCount, M.width k < meshTol) ∧
          ∃ W₀ : ℕ,
            ∀ W : ℕ, W₀ ≤ W →
              (∀ h, (Phead h).modulus ≤ W) →
              ∀ Acoef Aphys : ℝ, 0 ≤ Acoef → 0 ≤ Aphys →
              ∀ᶠ n : ℕ in atTop,
                ∀ (B : PaperBridgeFit.BridgeData Head
                    (Fin (M.cellCount + 1)))
                  (xi : B.ParamSpace),
                  B.sampleData.n = n → B.sampleData.W = W →
                  ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                      physicalBound (I.lower .plus) B.sampleData.n)
                    (hremaining : ∀ c : Cell Head,
                      (PaperGuardCensus.rawCell Phead I B.sampleData.n c \
                        (ledger B.sampleData.n).guards).Nonempty),
                    B.sampleData = PaperGuardCensus.canonicalSampleData
                        (W := B.sampleData.W) Phead I
                          (ledger B.sampleData.n) hsep hremaining →
                    (∃ (hWne : B.sampleData.W ≠ 0)
                        (S : RegularMeshPrimeCutoffs.ScaleSeparation
                          M B.sampleData.n B.sampleData.W),
                      B.partition =
                        RegularMeshPrimeCutoffs.Mesh.canonicalPartition M
                          (by
                            unfold SelectedDyadicRegularMesh.delta
                            positivity)
                          B.n_gt_one hWne S) →
                    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
                    |xi MomentCoord.physical| ≤ Aphys →
                    ∃ actualEquiv :
                      SharpGaugeSpace B.partition.mass B.partition.center
                          ≃L[ℝ]
                        SharpGaugeSpace B.partition.mass B.partition.center,
                      (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
                      ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖ := by
  exact PaperBridgeFit.BridgeData.exists_selectedDyadicMesh_eventually_actualFullProjected_inverse
      Phead I Cmax hlowerOne hupperMax Cprom Cbank ledger

end

end Erdos390.Full.PaperSelectedMeshActualFullProjectedInverseEventuallyStatementAudit
