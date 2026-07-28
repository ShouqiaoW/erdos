import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually

/-!
# Eventual canonical `MomentReady` data for the Section 9 traffic input

The canonical actual-moment theorem constructs
`RegularMeshPrimeCutoffs.Mesh.MomentReady` from its three endpoint
quadratures, uses it to prove the displayed moment inequalities, and then
discards the structure.  Section 9's ratio-cell moment argument consumes the
structure itself.

This connector exports that already-proved finite payload for the literal
canonical partition, uniformly in the supplied `ScaleSeparation` proof.  It
also records the independent eventual fact needed by the ratio-cell
coordinate argument: every positive-cell lower scale point eventually
exceeds any fixed real threshold, uniformly over the finite mesh.  The
combined theorem specializes this fact at the downstream threshold `2`.

No residual, balance, selector, Mertens, or traffic bound is asserted here.
-/

open scoped BigOperators
open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.PositiveCellTransfer
open Erdos390.Full.KernelPrimeQuadrature
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.PrimeCoordinateSecondMoment
open Erdos390.Full.MovingLowMomentQuadrature

noncomputable section

/-! ## Uniform positive-cell scale growth -/

/-- Every fixed real threshold is eventually below every positive-cell
lower scale point.  The threshold is fixed before the asymptotic index, and
the conclusion is uniform over the finite mesh. -/
theorem eventually_bankPaperCanonical_all_le_scalePoint_lower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) (A : Real) :
    ∀ᶠ n : Nat in atTop,
      ∀ k : Fin M.cellCount, A ≤ scalePoint n (M.lower k) := by
  rw [Filter.eventually_all]
  intro k
  exact
    (tendsto_scalePoint_atTop (M.lower_pos hdelta k)).eventually
      (eventually_ge_atTop A)

/-! ## Literal canonical-partition moment readiness -/

/-- The actual endpoint quadratures supply `MomentReady` for every literal
canonical partition obtained from a scale-separation proof.  At the same
asymptotic index, every positive-cell lower scale point is at least `2`, as
required by the ratio-cell coordinate bound.

The only cutoff premise is the existing structural condition
`canonicalActualMomentCutoff ≤ W`; in particular, no traffic hypothesis is
folded into this statement. -/
theorem eventually_bankPaperCanonical_actualMomentReady
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) :
    ∀ W : Nat, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : Nat in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          (∀ k : Fin M.cellCount,
            (2 : Real) ≤ scalePoint n (M.lower k)) ∧
          ∀ S : ScaleSeparation M n W,
            RegularMeshPrimeCutoffs.Mesh.MomentReady M
              (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta hn hWne S) := by
  let Cmass : Real := canonicalMassQuadratureConstant
  let Xmass : Nat := canonicalMassQuadratureCutoff
  let Cfirst : Real :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformConstant
  let Xfirst : Nat :=
    MovingLowMomentQuadrature.fullLogReciprocalSumUniformCutoff
  let Csecond : Real := canonicalSecondMomentConstant
  let Xsecond : Nat := canonicalSecondMomentCutoff
  have hMass : ∀ A Y : Nat, Xmass ≤ A → A ≤ Y →
      |PrimeSums.fullReciprocalSum Y - PrimeSums.fullReciprocalSum A -
          (Real.log (Real.log (Y : Real)) -
            Real.log (Real.log (A : Real)))| ≤
        5 * Cmass / Real.log (A : Real) ^ 3 := by
    intro A Y hA hAY
    simpa only [Cmass, Xmass] using
      canonicalMassQuadratureBound A Y hA hAY
  have hFirst : ∀ A Y : Nat, Xfirst ≤ A → A ≤ Y →
      |PrimeSums.fullLogReciprocalSum Y -
          PrimeSums.fullLogReciprocalSum A -
          (Real.log (Y : Real) - Real.log (A : Real))| ≤
        2 * Cfirst / Real.log (A : Real) ^ 3 +
          Cfirst / (2 * Real.log (A : Real) ^ 2) := by
    intro A Y hA hAY
    simpa only [Cfirst, Xfirst] using
      MovingLowMomentQuadrature.fullLogReciprocalSumUniform_bound A Y hA hAY
  have hSecond : ∀ z : Real, 1 < z → ∀ A Y : Nat,
      Xsecond ≤ A → A ≤ Y →
      |KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z Y -
          KernelPrimeQuadrature.fullWeightedReciprocalSum
            PrimeCoordinateSecondMoment.squareCoordinate z A -
          ((realLogCoordinate z (Y : Real) ^ 2 -
            realLogCoordinate z (A : Real) ^ 2) / 2)| ≤
        3 * Csecond / (Real.log z ^ 2 * Real.log (A : Real)) := by
    intro z hz A Y hA hAY
    simpa only [Csecond, Xsecond] using
      canonicalSecondMomentBound z hz A Y hA hAY
  intro W hW
  have hW8 : 8 ≤ W :=
    (le_max_left 8 (max Xmass (max Xfirst Xsecond))).trans hW
  have hXmass : Xmass ≤ W :=
    ((le_max_left Xmass (max Xfirst Xsecond)).trans
      (le_max_right 8 (max Xmass (max Xfirst Xsecond)))).trans hW
  have hXfirst : Xfirst ≤ W :=
    ((le_max_left Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hXsecond : Xsecond ≤ W :=
    ((le_max_right Xfirst Xsecond).trans
      ((le_max_right Xmass (max Xfirst Xsecond)).trans
        (le_max_right 8 (max Xmass (max Xfirst Xsecond))))).trans hW
  have hWne : W ≠ 0 := by omega
  have hEndpoint :=
    RegularMeshPrimeCutoffs.Mesh.eventually_endpointMomentBounds
      M hdelta W Cmass Cfirst Csecond (by omega : 1 < W)
  have hTwo :=
    eventually_bankPaperCanonical_all_le_scalePoint_lower
      M hdelta (2 : Real)
  filter_upwards [hEndpoint, hTwo] with n R hTwoN
  let hn : 1 < n := R.n_gt_one
  refine ⟨hWne, hn, hTwoN, ?_⟩
  intro S
  let P :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta hn hWne S
  let E :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta hn hWne S
  exact
    RegularMeshPrimeCutoffs.Mesh.momentReady_of_endpointMomentBounds M P E
      (fun j ↦ rfl) (fun j ↦ rfl)
      hW8 hXmass hXfirst hXsecond hMass hFirst hSecond R

end

end Erdos390.WholePaper
