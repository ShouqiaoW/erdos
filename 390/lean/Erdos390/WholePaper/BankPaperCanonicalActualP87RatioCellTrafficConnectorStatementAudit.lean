import Erdos390.WholePaper.BankPaperCanonicalActualP87RatioCellTrafficConnector

/-!
# Statement audit for the actual-P87 ratio-cell traffic connector

The complete public declaration census is followed by expanded checks of the
two scale identities and of the eventual literal-`q` traffic payload.  The
finite selector and paper-budget terminals are checked in the census; their
source statements expose the canonical partition, weighted port, total
moment traffic, and incident ledger without an abbreviated wrapper.
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

/-! ## Complete public declaration census -/

#check bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
#check bankPaperCanonicalHarmonicPointwiseUpper_mono_scale
#check bankPaperCanonical_actualP87Scale_le_paperScale_of_normalized
#check bankPaperCanonical_actualP87RatioCellMomentTraffic
#check bankPaperCanonical_actualP87RatioCellPaperTraffic_of_scale_le
#check eventually_bankPaperCanonical_actualP87RatioCellMomentTraffic

/-! ## Exact actual scale -/

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (Cpost : Real)
    (p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W) :
    bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost p =
      bankPaperCanonicalHarmonicPointwiseUpper
        (Cpost * B.q / B.L) p :=
  bankPaperCanonicalActualP87PointwiseUpper_eq_harmonicScale
    B Cpost p

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {Cpost tangentConstant N : Real}
    (hnormalized :
      (2 / 9 : Real) * (Cpost * B.q) <= tangentConstant * N) :
    Cpost * B.q / B.L <=
      tangentConstant * N / Real.log (y B.sampleData.n) :=
  bankPaperCanonical_actualP87Scale_le_paperScale_of_normalized
    B hnormalized

/-! ## Expanded eventual moment/traffic payload -/

example
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
                n W rho (Cpost * q n / Erdos390.Full.Scale.L n) :=
  eventually_bankPaperCanonical_actualP87RatioCellMomentTraffic
    M hdelta W hMomentCutoff hrho hCpost hMertens hPNT q hq

end

end Erdos390.WholePaper
