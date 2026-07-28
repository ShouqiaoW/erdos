import Erdos390.WholePaper.BankPaperCanonicalRatioCellOccupancy

/-!
# Expanded statement audit for fixed-ratio PNT cell occupancy

All six public theorems are listed.  The examples expose both eventual PNT
forms and the exact paper-order quantifiers: `rho`, then one cutoff `W`, then
every later mesh and `n` satisfying the canonical scale separation.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

#check eventually_primeCounting_fixedRatio_difference_pos
#check eventually_fixedRatio_primeCounting_lower
#check eventually_exists_prime_in_fixedRatio_interval
#check exists_fixedRatioPrimeIntervalOccupancy_cutoff
#check exists_fixedW_bankPaperCanonical_ratioCell_occupancy
#check exists_fixedW_bankPaperCanonical_ratioCellGeometry_spec

example {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      0 < Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
        Nat.primeCounting A :=
  eventually_primeCounting_fixedRatio_difference_pos hrho

example {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      ((rho - 1) / 2) *
          ((A : Real) / Real.log (A : Real)) <=
        (Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
          Nat.primeCounting A : Nat) :=
  eventually_fixedRatio_primeCounting_lower hrho

example {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊ :=
  eventually_exists_prime_in_fixedRatio_interval hrho

example {rho : Real} (hrho : 1 < rho) :
    ∃ W : Nat, 2 <= W ∧
      forall A : Nat, W <= A ->
        ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊ :=
  exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho

example {rho : Real} (hrho : 1 < rho) :
    ∃ W : Nat, ∃ hW : 2 <= W,
      forall {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta) {n : Nat}
        (hdelta : 0 < delta) (hn : 1 < n)
        (S : ScaleSeparation M n W),
        forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
          cell <= bankPaperCanonicalLastRatioCell M
            (n := n) (W := W) rho band ->
            tangentRatioCellCard
              (bankPaperCanonicalExponentBandOf M hdelta hn
                (by omega : W ≠ 0) S)
              (bankPaperCanonicalRatioCellIndex M hdelta hn
                (by omega : W ≠ 0) S rho)
              band cell ≠ 0 :=
  exists_fixedW_bankPaperCanonical_ratioCell_occupancy hrho

example {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
    ∃ W : Nat, ∃ hW : 2 <= W,
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
          TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
            (bankPaperCanonicalExponentBandOf M hdelta hn
              (by omega : W ≠ 0) S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn
              (by omega : W ≠ 0) S rho) r0 :=
  exists_fixedW_bankPaperCanonical_ratioCellGeometry_spec hrho hratio

end

end Erdos390.WholePaper
