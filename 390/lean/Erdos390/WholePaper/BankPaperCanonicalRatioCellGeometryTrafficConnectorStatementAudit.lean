import Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometryTrafficConnector

/-!
# Statement audit for the ratio-cell geometry/traffic connector

The two monotonicity lemmas and the complete same-cutoff terminal are
expanded below.  The terminal displays all five continuation-facing geometry
fields together with the quantitative PNT, Mertens, and locality inputs.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Complete public declaration census -/

#check tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
#check tangentFixedRatioPrimeCountLower_mono_cutoff
#check exists_fixedW_bankPaperCanonical_ratioCellGeometryTraffic_spec

example {W W' : Nat} {rho : Real} (hWW' : W <= W')
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    TangentFixedRatioPrimeIntervalOccupied W' rho :=
  tangentFixedRatioPrimeIntervalOccupied_mono_cutoff hWW' hprime

example {W W' : Nat} {rho : Real} (hWW' : W <= W')
    (hPNT : TangentFixedRatioPrimeCountLower W rho) :
    TangentFixedRatioPrimeCountLower W' rho :=
  tangentFixedRatioPrimeCountLower_mono_cutoff hWW' hPNT

example {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
    ∃ W : Nat, ∃ hW : 2 <= W,
      fullReciprocalSumUniformCutoff <= W ∧
      TangentFixedRatioPrimeCountLower W rho ∧
      forall {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta) {n : Nat}
        (hdelta : 0 < delta) (hn : 1 < n)
        (S : ScaleSeparation M n W),
        (forall p : BankPaperCanonicalTangentPrime n W,
          bankPaperCanonicalRatioCellIndex M hdelta hn
              (by omega : W ≠ 0) S rho p <=
            bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
              (bankPaperCanonicalExponentBandOf M hdelta hn
                (by omega : W ≠ 0) S p)) ∧
          (forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
            cell <= bankPaperCanonicalLastRatioCell M
              (n := n) (W := W) rho band ->
              tangentRatioCellCard
                (bankPaperCanonicalExponentBandOf M hdelta hn
                  (by omega : W ≠ 0) S)
                (bankPaperCanonicalRatioCellIndex M hdelta hn
                  (by omega : W ≠ 0) S rho)
                band cell ≠ 0) ∧
          (forall (band : BankPaperCanonicalExponentBand M) (cut : Nat),
            fullReciprocalSumUniformCutoff <=
              bankPaperCanonicalRatioCellTailLower M n W rho band cut) ∧
          (forall (band : BankPaperCanonicalExponentBand M) (cut : Nat),
            bankPaperCanonicalRatioCellTailLower M n W rho band cut <=
              bankPaperCanonicalRatioCellTailUpper M n W band) ∧
          (forall (band : BankPaperCanonicalExponentBand M) (cut : Nat)
              (p : BankPaperCanonicalTangentPrime n W),
            bankPaperCanonicalExponentBandOf M hdelta hn
                (by omega : W ≠ 0) S p = band ->
              cut < bankPaperCanonicalRatioCellIndex M hdelta hn
                (by omega : W ≠ 0) S rho p ->
                bankPaperCanonicalRatioCellTailLower M n W rho band cut <
                    bankPaperCanonicalTangentPrimeLabel p ∧
                  bankPaperCanonicalTangentPrimeLabel p <=
                    bankPaperCanonicalRatioCellTailUpper M n W band) ∧
          TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
            (bankPaperCanonicalExponentBandOf M hdelta hn
              (by omega : W ≠ 0) S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn
              (by omega : W ≠ 0) S rho) r0 :=
  exists_fixedW_bankPaperCanonical_ratioCellGeometryTraffic_spec hrho hratio

end

end Erdos390.WholePaper
