import Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometry
import Erdos390.WholePaper.PrimeLayerCounts

/-!
# PNT occupancy for canonical multiplicative ratio cells

The geometry file reduces cell occupancy to one uniform fixed-ratio prime
interval statement.  Here that statement is proved from the already audited
safe prime number theorem.  For every fixed `rho > 1`, there is one natural
cutoff `W` such that every interval

`(A, floor (rho * A)]`, `A >= W`,

contains a prime.  Consequently all full raw `rho`-cells of every later
canonical exponent mesh are occupied; the possibly short terminal fragment
is handled by the deterministic merge.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-- The safe PNT makes the prime-count difference in every fixed-ratio
interval eventually positive. -/
theorem eventually_primeCounting_fixedRatio_difference_pos
    {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      0 < Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
        Nat.primeCounting A := by
  have hLimit :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : Real)) (b := rho) zero_lt_one hrho.le
  have hRatioPos : ∀ᶠ A : Nat in atTop,
      0 <
        ((Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
            Nat.primeCounting A : Nat) : Real) /
          ((A : Real) / Real.log (A : Real)) := by
    have hEventually := hLimit.eventually
      (eventually_gt_nhds (sub_pos.mpr hrho))
    simpa using hEventually
  filter_upwards [hRatioPos, eventually_gt_atTop 1] with A hRatio hA
  have hAPos : (0 : Real) < A := by
    exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hLogPos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hA)
  have hScalePos : 0 < (A : Real) / Real.log (A : Real) :=
    div_pos hAPos hLogPos
  have hCountReal :
      0 <
        ((Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
          Nat.primeCounting A : Nat) : Real) :=
    (div_pos_iff_of_pos_right hScalePos).mp hRatio
  exact_mod_cast hCountReal

/-- Quantitative form retained for the later port-load estimate: a fixed
positive fraction of the PNT main term lies in every sufficiently large
fixed-ratio interval. -/
theorem eventually_fixedRatio_primeCounting_lower
    {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      ((rho - 1) / 2) *
          ((A : Real) / Real.log (A : Real)) <=
        (Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
          Nat.primeCounting A : Nat) := by
  have hLimit :=
    SafePrimeCounting.primeCounting_interval_natSub_normalized_tendsto
      (a := (1 : Real)) (b := rho) zero_lt_one hrho.le
  have hhalf : (rho - 1) / 2 < rho - 1 := by
    have : 0 < rho - 1 := sub_pos.mpr hrho
    linarith
  have hRatio : ∀ᶠ A : Nat in atTop,
      (rho - 1) / 2 <
        ((Nat.primeCounting ⌊rho * (A : Real)⌋₊ -
            Nat.primeCounting A : Nat) : Real) /
          ((A : Real) / Real.log (A : Real)) := by
    have hEventually := hLimit.eventually (eventually_gt_nhds hhalf)
    simpa using hEventually
  filter_upwards [hRatio, eventually_gt_atTop 1] with A hRatioA hA
  have hAPos : (0 : Real) < A := by
    exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hLogPos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast hA)
  have hScalePos : 0 < (A : Real) / Real.log (A : Real) :=
    div_pos hAPos hLogPos
  exact (le_div_iff₀ hScalePos).mp hRatioA.le

/-- Every sufficiently large natural lower endpoint has a prime in its
fixed-ratio interval. -/
theorem eventually_exists_prime_in_fixedRatio_interval
    {rho : Real} (hrho : 1 < rho) :
    ∀ᶠ A : Nat in atTop,
      ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊ := by
  filter_upwards [eventually_primeCounting_fixedRatio_difference_pos hrho]
    with A hCount
  let upper : Nat := ⌊rho * (A : Real)⌋₊
  have hPrimeCounting :
      Nat.primeCounting A < Nat.primeCounting upper := by
    exact Nat.sub_pos_iff_lt.mp hCount
  have hCounting :
      Nat.count Nat.Prime (A + 1) < Nat.count Nat.Prime (upper + 1) := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using hPrimeCounting
  obtain ⟨p, hpInterval, hpPrime⟩ :=
    Nat.exists_of_count_lt_count (p := Nat.Prime) hCounting
  rcases hpInterval with ⟨hpLower, hpUpper⟩
  exact ⟨p, hpPrime, by omega, by simpa only [upper] using (show p <= upper by omega)⟩

/-- Existential paper-order form: choose one fixed head cutoff after `rho`,
and every later fixed-ratio interval is occupied. -/
theorem exists_fixedRatioPrimeIntervalOccupancy_cutoff
    {rho : Real} (hrho : 1 < rho) :
    ∃ W : Nat, 2 <= W ∧ TangentFixedRatioPrimeIntervalOccupied W rho := by
  obtain ⟨W₀, hW₀⟩ :=
    eventually_atTop.1 (eventually_exists_prime_in_fixedRatio_interval hrho)
  let W := max 2 W₀
  exact ⟨W, le_max_left _ _, by
    intro A hWA
    exact hW₀ A ((le_max_right 2 W₀).trans hWA)⟩

/-- Full canonical-cell occupancy, with the PNT cutoff chosen before the
mesh and before `n`, in the exact order used by the paper. -/
theorem exists_fixedW_bankPaperCanonical_ratioCell_occupancy
    {rho : Real} (hrho : 1 < rho) :
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
              band cell ≠ 0 := by
  obtain ⟨W, hW, hprime⟩ :=
    exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho
  exact ⟨W, hW, by
    intro delta eta M n hdelta hn S
    exact bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
      M hdelta hn (by omega) S hrho hprime⟩

/-- The complete geometry/PNT layer in paper parameter order: after fixing
`rho` and `r0`, choose one fixed `W`; every later canonical mesh then has
the exact index, occupancy, and locality inputs of the explicit earthmover. -/
theorem exists_fixedW_bankPaperCanonical_ratioCellGeometry_spec
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
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
              (by omega : W ≠ 0) S rho) r0 := by
  obtain ⟨W, hW, hprime⟩ :=
    exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho
  exact ⟨W, hW, by
    intro delta eta M n hdelta hn S
    exact bankPaperCanonical_ratioCellGeometry_spec
      M hdelta hn (by omega) S hrho hratio hprime⟩

end

end Erdos390.WholePaper
