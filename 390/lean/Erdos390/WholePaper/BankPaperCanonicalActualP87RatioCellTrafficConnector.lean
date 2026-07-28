import Erdos390.WholePaper.BankPaperProposition87ActualDataConnector
import Erdos390.WholePaper.BankPaperCanonicalActualMomentReadyEventually
import Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic

/-!
# Actual Proposition 8.7 residuals in the canonical ratio-cell traffic ledger

The actual Proposition 8.7 endpoint has primewise residual bound

`Cpost * q / (p * B.L)`,

where `q = B.q` is the literal active mass.  This file connects that bound to
the audited canonical ratio-cell moment and port estimates.  In particular,
the traffic scale below is always the literal

`Cpost * B.q / B.L`;

the active mass is never replaced by `1`.

There are two levels of output.

* The finite connector gives the weighted-residual, uniform-port, and total
  moment-traffic bounds at the actual scale, for the literal canonical
  partition.
* The paper-budget connector gives the scalar Section 9 main/error form after
  receiving the precise scale domination

  `Cpost * B.q / B.L <= tangentConstant * N / log y`.

The latter comparison is not manufactured here.  A reusable normalization
lemma shows that it follows from the equivalent numerator comparison after
using the exact identity `log y = (2/9) B.L`.

Finally, the eventual connector consumes the actual `MomentReady` producer.
It is uniform in the scale-separation proof and in every residual satisfying
the displayed balance and actual-scale pointwise hypotheses.  The quantitative
Mertens and fixed-ratio PNT hypotheses remain visible traffic inputs.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## Exact comparison of the actual P87 and harmonic pointwise forms -/

/-- The literal actual-P87 pointwise upper bound is exactly the harmonic
majorant at scale `Cpost * B.q / B.L`. -/
theorem bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (Cpost : Real)
    (p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W) :
    bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p =
      bankPaperCanonicalHarmonicPointwiseUpper
        (Cpost * B.q / B.L) p := by
  have hp : (p.1 : Real) ≠ 0 := by
    exact_mod_cast (bankPaperCanonicalTangentPrimeLabel_prime p).pos.ne'
  have hL : B.L ≠ 0 := B.L_pos.ne'
  unfold bankPaperCanonicalActualP87PointwiseUpper
    bankPaperCanonicalHarmonicPointwiseUpper
    bankPaperCanonicalTangentPrimeLabel
  field_simp [hp, hL]

/-- The harmonic primewise upper bound is monotone in its scalar scale. -/
theorem bankPaperCanonicalHarmonicPointwiseUpper_mono_scale
    {n W : Nat} {scale scale' : Real} (hscale : scale <= scale')
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalHarmonicPointwiseUpper scale p <=
      bankPaperCanonicalHarmonicPointwiseUpper scale' p := by
  unfold bankPaperCanonicalHarmonicPointwiseUpper
  exact div_le_div_of_nonneg_right hscale (Nat.cast_nonneg _)

/-- Exact normalized criterion for domination by a Section 9 paper scale.

Since `log y = (2/9) B.L`, the numerator comparison

`(2/9) * (Cpost * q) <= tangentConstant * N`

implies the required comparison of the two pointwise scales. -/
theorem bankPaperCanonical_actualP87Scale_le_paperScale_of_normalized
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {Cpost tangentConstant N : Real}
    (hnormalized :
      (2 / 9 : Real) * (Cpost * B.q) <= tangentConstant * N) :
    Cpost * B.q / B.L <=
      tangentConstant * N / Real.log (y B.sampleData.n) := by
  have hlog :
      Real.log (y B.sampleData.n) = (2 / 9 : Real) * B.L := by
    calc
      Real.log (y B.sampleData.n) =
          (2 / 9 : Real) * Erdos390.Full.Scale.L B.sampleData.n :=
        Erdos390.Full.Scale.log_y
          (Nat.zero_lt_of_lt B.n_gt_one)
      _ = (2 / 9 : Real) * B.L := by
        rfl
  rw [hlog]
  have hL : 0 < B.L := B.L_pos
  have hden : 0 < (2 / 9 : Real) * B.L :=
    mul_pos (by norm_num) hL
  apply (div_le_div_iff₀ hL hden).2
  have hmul := mul_le_mul_of_nonneg_right hnormalized hL.le
  calc
    Cpost * B.q * ((2 / 9 : Real) * B.L) =
        ((2 / 9 : Real) * (Cpost * B.q)) * B.L := by ring
    _ <= (tangentConstant * N) * B.L := hmul

/-! ## The common finite traffic payload -/

private theorem bankPaperCanonical_ratioCellMomentTraffic_payload
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hWtwo : 2 <= W) (S : ScaleSeparation M n W)
    {rho scale : Real} (hrho : 1 < rho) (hscale : 0 <= scale)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn (by omega) S))
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bankPaperCanonicalExponentBandOf
            M hdelta hn (by omega) S p = band then residual p else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |residual p| <= bankPaperCanonicalHarmonicPointwiseUpper scale p) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        scale) ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
            tangentRatioCellUniformPortLoad residual
              (bankPaperCanonicalExponentBandOf
                M hdelta hn (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta hn (by omega) S rho) p <=
          bankPaperCanonicalRatioCellUniformPortMajorant
            M n W rho scale) ∧
      tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
            residual
            (bankPaperCanonicalExponentBandOf
              M hdelta hn (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta hn (by omega) S rho)) <=
        bankPaperCanonicalRatioCellMomentTotalTrafficMajorant
          M n W rho scale := by
  refine ⟨?_, ?_, ?_⟩
  · intro p
    exact bankPaperCanonical_weightedResidual_le_harmonicScale
      residual hpointwise p
  · intro p
    exact
      bankPaperCanonical_weightedRatioCellUniformPortLoad_le_majorant
        M hdelta hn hWtwo S hrho hscale hMertens hPNT hTwo
        residual hbalance hpointwise p
  · exact bankPaperCanonical_ratioCellTotalTraffic_le_momentMajorant
      M hdelta hn hWtwo S hrho hscale hMertens hTwo Hmoment
      residual hbalance hpointwise

/-! ## Selector-facing actual-P87 traffic -/

/-- A rounded actual-P87 selector on the literal canonical partition supplies
all three analytic traffic estimates used by the distributed Section 9
assembly:

* weighted residual at `Cpost * B.q / B.L`;
* weighted uniform port at the matching explicit port majorant; and
* total earthmover traffic at the one-Mertens moment majorant.

The only selector facts used are the exact canonical-band balance and the
actual P87 pointwise field already present in
`BankPaperCanonicalRoundedSelectorTangentInput`. -/
theorem bankPaperCanonical_actualP87RatioCellMomentTraffic
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : BridgeData Head (BankPaperCanonicalExponentBand M))
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hdelta : 0 < delta) (hWtwo : 2 <= B.sampleData.W)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S)
    {rho Cpost : Real} (hrho : 1 < rho) (hCpost : 0 <= Cpost)
    (hMertens : fullReciprocalSumUniformCutoff <= B.sampleData.W)
    (hPNT : TangentFixedRatioPrimeCountLower B.sampleData.W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint B.sampleData.n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S))
    {prefixUpper : BankPaperCanonicalExponentBand M -> Nat -> Real}
    (Hselector : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
      B.partition.band
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      prefixUpper selector) :
    let residual :=
      bankPaperCanonicalTangentResidual R certificate
        fixed candidates selector
    let scale := Cpost * B.q / B.L
    (forall p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        scale) ∧
      (forall p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
            tangentRatioCellUniformPortLoad residual
              (bankPaperCanonicalExponentBandOf
                M hdelta B.n_gt_one (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta B.n_gt_one (by omega) S rho) p <=
          bankPaperCanonicalRatioCellUniformPortMajorant M
            B.sampleData.n B.sampleData.W rho scale) ∧
      tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            (bankPaperCanonicalLastRatioCell M
              (n := B.sampleData.n) (W := B.sampleData.W) rho)
            residual
            (bankPaperCanonicalExponentBandOf
              M hdelta B.n_gt_one (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta B.n_gt_one (by omega) S rho)) <=
        bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M
          B.sampleData.n B.sampleData.W rho scale := by
  dsimp only
  letI : Nonempty Head := ⟨B.referenceHead⟩
  let residual : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real :=
    bankPaperCanonicalTangentResidual (W := B.sampleData.W)
      R certificate fixed candidates selector
  let scale := Cpost * B.q / B.L
  have HselectorCanonical : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      prefixUpper selector := by
    simpa only [bankPaperCanonicalExponentBandOf, hpartition] using Hselector
  have hbounds :=
    bankPaperCanonicalRoundedSelectorTangentInput_residualBounds
      HselectorCanonical
  have hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if bankPaperCanonicalExponentBandOf
            M hdelta B.n_gt_one (by omega) S p = band then
          residual p else 0) = 0 := by
    simpa only [residual] using hbounds.1
  have hpointwiseActual : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      |residual p| <=
        bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p := by
    simpa only [residual] using hbounds.2.1
  have hpointwise : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      |residual p| <=
        bankPaperCanonicalHarmonicPointwiseUpper scale p := by
    intro p
    calc
      |residual p| <=
          bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p :=
        hpointwiseActual p
      _ = bankPaperCanonicalHarmonicPointwiseUpper scale p := by
        simpa only [scale] using
          bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
            B Cpost p
  have hscale : 0 <= scale := by
    exact div_nonneg (mul_nonneg hCpost B.q_pos.le) B.L_pos.le
  simpa only [residual, scale] using
    bankPaperCanonical_ratioCellMomentTraffic_payload
      M hdelta B.n_gt_one hWtwo S hrho hscale hMertens hPNT
      hTwo Hmoment residual hbalance hpointwise

/-! ## Assembly-facing paper main/error form -/

/-- If the literal actual-P87 scale is dominated by a chosen paper scale,
the same endpoint supplies the four quantitative premises used in the
distributed assembly:

* weighted residual;
* weighted uniform port;
* total traffic in fixed-main plus vanishing-error form; and
* the matching weighted-incident identity.

The domination premise is deliberately displayed.  It is the only bridge
from the actual active mass `B.q` to the assembly normalization `N`. -/
theorem bankPaperCanonical_actualP87RatioCellPaperTraffic_of_scale_le
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {Head : Type*} [Fintype Head] [DecidableEq Head]
    (B : BridgeData Head (BankPaperCanonicalExponentBand M))
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hdelta : 0 < delta) (hWtwo : 2 <= B.sampleData.W)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S)
    {rho Cpost tangentConstant N : Real}
    (hrho : 1 < rho) (htangent : 0 <= tangentConstant) (hN : 0 <= N)
    (hscaleDom : Cpost * B.q / B.L <=
      tangentConstant * N / Real.log (y B.sampleData.n))
    (hMertens : fullReciprocalSumUniformCutoff <= B.sampleData.W)
    (hPNT : TangentFixedRatioPrimeCountLower B.sampleData.W rho)
    (hTwo : forall k : Fin M.cellCount,
      2 <= scalePoint B.sampleData.n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S))
    {prefixUpper : BankPaperCanonicalExponentBand M -> Nat -> Real}
    (Hselector : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
      B.partition.band
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      prefixUpper selector) :
    let residual :=
      bankPaperCanonicalTangentResidual R certificate
        fixed candidates selector
    let paperScale :=
      tangentConstant * N / Real.log (y B.sampleData.n)
    (forall p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        paperScale) ∧
      (forall p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
            tangentRatioCellUniformPortLoad residual
              (bankPaperCanonicalExponentBandOf
                M hdelta B.n_gt_one (by omega) S)
              (bankPaperCanonicalRatioCellIndex
                M hdelta B.n_gt_one (by omega) S rho) p <=
          bankPaperCanonicalRatioCellUniformPortMajorant M
            B.sampleData.n B.sampleData.W rho paperScale) ∧
      tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            (bankPaperCanonicalLastRatioCell M
              (n := B.sampleData.n) (W := B.sampleData.W) rho)
            residual
            (bankPaperCanonicalExponentBandOf
              M hdelta B.n_gt_one (by omega) S)
            (bankPaperCanonicalRatioCellIndex
              M hdelta B.n_gt_one (by omega) S rho)) <=
        bankPaperCanonicalRatioCellTrafficConstant rho *
            tangentConstant * N * (delta + M.ratio) +
          bankPaperCanonicalRatioCellTrafficErrorCoefficient M
            B.sampleData.n B.sampleData.W rho tangentConstant * N ∧
      paperScale +
          2 * bankPaperCanonicalRatioCellUniformPortMajorant M
            B.sampleData.n B.sampleData.W rho paperScale =
        bankPaperCanonicalRatioCellIncidentConstant rho *
            tangentConstant * N * (delta + M.ratio) +
          bankPaperCanonicalRatioCellIncidentErrorCoefficient
            B.sampleData.W B.sampleData.n rho tangentConstant * N := by
  dsimp only
  let residual : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real :=
    bankPaperCanonicalTangentResidual (W := B.sampleData.W)
      R certificate fixed candidates selector
  let paperScale :=
    tangentConstant * N / Real.log (y B.sampleData.n)
  have HselectorCanonical : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      prefixUpper selector := by
    simpa only [bankPaperCanonicalExponentBandOf, hpartition] using Hselector
  have hbounds :=
    bankPaperCanonicalRoundedSelectorTangentInput_residualBounds
      HselectorCanonical
  have hbalance : forall band : BankPaperCanonicalExponentBand M,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if bankPaperCanonicalExponentBandOf
            M hdelta B.n_gt_one (by omega) S p = band then
          residual p else 0) = 0 := by
    simpa only [residual] using hbounds.1
  have hpointwiseActual : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      |residual p| <=
        bankPaperCanonicalHarmonicPointwiseUpper
          (Cpost * B.q / B.L) p := by
    intro p
    calc
      |residual p| <=
          bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p := by
        simpa only [residual] using hbounds.2.1 p
      _ = bankPaperCanonicalHarmonicPointwiseUpper
          (Cpost * B.q / B.L) p :=
        bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
          B Cpost p
  have hpointwise : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      |residual p| <=
        bankPaperCanonicalHarmonicPointwiseUpper paperScale p := by
    intro p
    exact (hpointwiseActual p).trans
      (bankPaperCanonicalHarmonicPointwiseUpper_mono_scale
        hscaleDom p)
  have hpaperScale : 0 <= paperScale := by
    exact div_nonneg (mul_nonneg htangent hN) B.log_y_pos.le
  have hpayload :=
    bankPaperCanonical_ratioCellMomentTraffic_payload
      M hdelta B.n_gt_one hWtwo S hrho hpaperScale hMertens hPNT
      hTwo Hmoment residual hbalance hpointwise
  have htotalScalar :=
    bankPaperCanonical_ratioCellMomentTotalTrafficMajorant_paperScale
      M hdelta B.n_gt_one hWtwo hrho htangent hN
  have hincident :=
    bankPaperCanonical_incidentMajorant_paperScale
      M B.n_gt_one hWtwo hrho
      (tangentConstant := tangentConstant) (N := N)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [residual, paperScale] using hpayload.1
  · simpa only [residual, paperScale] using hpayload.2.1
  · exact hpayload.2.2.trans htotalScalar
  · simpa only [paperScale] using hincident

/-! ## Eventual actual-scale moment traffic -/

/-- The actual endpoint moment producer upgrades every eventually
nonnegative active-mass family to the full ratio-cell moment traffic payload,
uniformly in the supplied scale-separation proof and residual.

This theorem intentionally does not assert existence of a P87 selector or
balance.  It consumes those finite endpoint facts once supplied.  The only
remaining fixed-cutoff traffic premises are the quantitative Mertens and PNT
inputs displayed in the arguments. -/
theorem eventually_bankPaperCanonical_actualP87RatioCellMomentTraffic
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) (W : Nat)
    (hMomentCutoff : canonicalActualMomentCutoff <= W)
    {rho Cpost : Real} (hrho : 1 < rho) (hCpost : 0 <= Cpost)
    (hMertens : fullReciprocalSumUniformCutoff <= W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (q : Nat -> Real) (hq : ∀ᶠ n : Nat in atTop, 0 <= q n) :
    ∀ᶠ n : Nat in atTop,
      ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        (forall k : Fin M.cellCount,
          (2 : Real) <= scalePoint n (M.lower k)) ∧
        forall S : ScaleSeparation M n W,
        forall residual : BankPaperCanonicalTangentPrime n W -> Real,
          (forall band : BankPaperCanonicalExponentBand M,
            (∑ p : BankPaperCanonicalTangentPrime n W,
              if bankPaperCanonicalExponentBandOf
                  M hdelta hn hWne S p = band then residual p else 0) = 0) ->
          (forall p : BankPaperCanonicalTangentPrime n W,
            |residual p| <=
              bankPaperCanonicalHarmonicPointwiseUpper
                (Cpost * q n / Erdos390.Full.Scale.L n) p) ->
          (forall p : BankPaperCanonicalTangentPrime n W,
            (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
              Cpost * q n / Erdos390.Full.Scale.L n) ∧
            (forall p : BankPaperCanonicalTangentPrime n W,
              (bankPaperCanonicalTangentPrimeLabel p : Real) *
                  tangentRatioCellUniformPortLoad residual
                    (bankPaperCanonicalExponentBandOf
                      M hdelta hn hWne S)
                    (bankPaperCanonicalRatioCellIndex
                      M hdelta hn hWne S rho) p <=
                bankPaperCanonicalRatioCellUniformPortMajorant M
                  n W rho (Cpost * q n / Erdos390.Full.Scale.L n)) ∧
            tangentDistributedTotalTrafficLedger residual
                (tangentRatioCellCanonicalCutTraffic
                  (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
                  residual
                  (bankPaperCanonicalExponentBandOf
                    M hdelta hn hWne S)
                  (bankPaperCanonicalRatioCellIndex
                    M hdelta hn hWne S rho)) <=
              bankPaperCanonicalRatioCellMomentTotalTrafficMajorant M
                n W rho (Cpost * q n / Erdos390.Full.Scale.L n) := by
  have hWtwo : 2 <= W := by
    have hEight : 8 <= canonicalActualMomentCutoff := by
      unfold canonicalActualMomentCutoff
      exact le_max_left _ _
    omega
  have hready :=
    eventually_bankPaperCanonical_actualMomentReady
      M hdelta W hMomentCutoff
  filter_upwards [hready, hq] with n hreadyN hqN
  rcases hreadyN with ⟨hWne, hn, hTwo, Hmoment⟩
  refine ⟨hWne, hn, hTwo, ?_⟩
  intro S residual hbalance hpointwise
  have hscale :
      0 <= Cpost * q n / Erdos390.Full.Scale.L n := by
    exact div_nonneg (mul_nonneg hCpost hqN)
      (Erdos390.Full.Scale.L_pos hn).le
  exact bankPaperCanonical_ratioCellMomentTraffic_payload
    M hdelta hn hWtwo S hrho hscale hMertens hPNT hTwo
    (Hmoment S) residual hbalance hpointwise

end

end Erdos390.WholePaper
