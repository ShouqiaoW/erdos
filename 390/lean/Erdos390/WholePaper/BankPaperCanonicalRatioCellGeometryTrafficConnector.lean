import Erdos390.WholePaper.BankPaperCanonicalRatioCellTraffic

/-!
# Same-cutoff connector for canonical ratio-cell geometry and traffic

The qualitative occupancy theorem and the quantitative traffic theorem each
choose a fixed cutoff.  Their uniform predicates are both preserved when the
cutoff is increased, so their witnesses can be synchronized by taking a
maximum.

The already packaged geometry output cannot itself simply be transported to a
larger cutoff: its finite prime type, band map, and cell map all depend on the
old cutoff.  Instead this connector transports the underlying uniform prime
interval predicate and invokes `bankPaperCanonical_ratioCellGeometry_spec`
anew at the common cutoff.  The terminal exposes, for that same `W`,

* the quantitative PNT and Mertens inputs used by the traffic envelopes;
* the bounded-index and occupied-cell inputs;
* the exact tail endpoint data used by the guarded continuation; and
* the fixed-ratio locality used by the distributed clean-list adapter.

No new analytic or geometric assumption is introduced.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Monotonicity of the two uniform cutoff predicates -/

/-- Uniform prime-interval occupancy remains valid after increasing its
lower cutoff. -/
theorem tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
    {W W' : Nat} {rho : Real} (hWW' : W <= W')
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    TangentFixedRatioPrimeIntervalOccupied W' rho := by
  intro A hW'A
  exact hprime A (hWW'.trans hW'A)

/-- The quantitative fixed-ratio prime-count lower bound remains valid after
increasing its lower cutoff. -/
theorem tangentFixedRatioPrimeCountLower_mono_cutoff
    {W W' : Nat} {rho : Real} (hWW' : W <= W')
    (hPNT : TangentFixedRatioPrimeCountLower W rho) :
    TangentFixedRatioPrimeCountLower W' rho := by
  intro A hW'A
  exact hPNT A (hWW'.trans hW'A)

/-! ## One common cutoff for geometry, continuation tails, and traffic -/

/-- One fixed cutoff simultaneously supplies the canonical ratio-cell
geometry and every cutoff-dependent input of the traffic envelopes.

Besides the quantitative PNT and Mertens bounds, the per-mesh conclusion
contains the exact five geometric fields used downstream: bounded indices,
occupancy, the Mertens-valid tail lower endpoint, ordered tail endpoints, and
tail membership.  The final conjunct is the fixed-ratio locality needed for
clean-list absorption. -/
theorem exists_fixedW_bankPaperCanonical_ratioCellGeometryTraffic_spec
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
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
              (by omega : W ≠ 0) S rho) r0 := by
  obtain ⟨Woccupancy, _hWoccupancy, hoccupancy⟩ :=
    exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho
  obtain ⟨Wtraffic, hWtraffic, hMertens, hPNT⟩ :=
    exists_fixedRatioPrimeCountLower_and_Mertens_cutoff hrho
  let W := max Woccupancy Wtraffic
  have hoccupancyLe : Woccupancy <= W := le_max_left _ _
  have htrafficLe : Wtraffic <= W := le_max_right _ _
  have hW : 2 <= W := hWtraffic.trans htrafficLe
  have hMertensW : fullReciprocalSumUniformCutoff <= W :=
    hMertens.trans htrafficLe
  have hPNTW : TangentFixedRatioPrimeCountLower W rho :=
    tangentFixedRatioPrimeCountLower_mono_cutoff htrafficLe hPNT
  have hoccupancyW : TangentFixedRatioPrimeIntervalOccupied W rho :=
    tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
      hoccupancyLe hoccupancy
  exact ⟨W, hW, hMertensW, hPNTW, by
    intro delta eta M n hdelta hn S
    have hgeometry := bankPaperCanonical_ratioCellGeometry_spec
      M hdelta hn (by omega) S hrho hratio hoccupancyW
    exact ⟨hgeometry.1, hgeometry.2.1,
      fun band cut => hMertensW.trans
        (bankPaperCanonical_fixedCutoff_le_ratioCellTailLower
          M hdelta hn (by omega) S hrho band cut),
      bankPaperCanonicalRatioCellTailLower_le_upper M n W rho,
      bankPaperCanonical_ratioCellTail_mem_interval
        M hdelta hn (by omega) S hrho,
      hgeometry.2.2⟩⟩

end

end Erdos390.WholePaper
