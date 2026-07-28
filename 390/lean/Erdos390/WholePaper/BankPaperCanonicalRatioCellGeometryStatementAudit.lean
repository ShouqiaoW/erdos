import Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometry

/-!
# Expanded statement audit for canonical exponent bands and ratio cells

The declaration census below covers all 13 public definitions/abbreviations
and all 26 public theorems.  The expanded examples then pin down the raw-cell
endpoints, terminal merge, canonical-band assignment, fixed-ratio locality,
occupancy boundary, and complete downstream package.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Complete declaration census -/

#check tangentMultiplicativeRatioCutoff
#check tangentMultiplicativeRatioCutoff_zero
#check tangentMultiplicativeRatioCutoff_mono
#check exists_label_le_tangentMultiplicativeRatioCutoff_succ
#check tangentMultiplicativeRawCellIndex
#check label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
#check tangentMultiplicativeRatioCutoff_rawCell_lt_label
#check tangentMultiplicativeRawCellIndex_mono
#check tangentMultiplicativeRawCellIndex_eq_of_mem
#check tangentMultiplicativeRawCell_real_lower_lt
#check tangentMultiplicativeRawCell_real_upper
#check tangentMergedRatioCellIndex
#check tangentMergedRatioLastCell
#check tangentMergedRatioCellIndex_le_lastCell
#check tangentMergedRatioCellIndex_le_raw
#check tangentMergedRatioCellIndex_eq_self
#check tangentMergedRatioCellIndex_lastRaw
#check raw_le_tangentMergedRatioCellIndex_add_one
#check tangentMergedRatioCellIndex_mono
#check rawCellIndices_within_two_of_merged_sameOrAdjacent
#check tangentMultiplicativeRawCell_ratio_lt_cube
#check BankPaperCanonicalExponentBand
#check bankPaperCanonicalExponentBandOf
#check bankPaperCanonicalExponentBandLower
#check bankPaperCanonicalExponentBandUpper
#check bankPaperCanonicalExponentBandOf_mem_interval
#check bankPaperCanonicalExponentBandLower_pos
#check bankPaperCanonicalRawRatioCellIndex
#check bankPaperCanonicalLastRawRatioCell
#check bankPaperCanonicalLastRatioCell
#check bankPaperCanonicalRatioCellIndex
#check bankPaperCanonicalRawRatioCellIndex_le_lastRaw
#check bankPaperCanonicalRatioCellIndex_le_lastCell
#check bankPaperCanonicalRatioCellIndex_mono_of_sameBand
#check bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
#check bankPaperCanonical_tangentRatioCellGeometry
#check TangentFixedRatioPrimeIntervalOccupied
#check bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
#check bankPaperCanonical_ratioCellGeometry_spec

/-! ## Exact definition audit -/

example (lower : Nat) (rho : Real) (k : Nat) :
    tangentMultiplicativeRatioCutoff lower rho k =
      ⌊(lower : Real) * rho ^ k⌋₊ := by
  rfl

example (lower label : Nat) (rho : Real) :
    tangentMultiplicativeRawCellIndex lower label rho =
      if h : 0 < lower ∧ 1 < rho then
        Nat.find
          (exists_label_le_tangentMultiplicativeRatioCutoff_succ
            h.1 h.2 label)
      else 0 := by
  rfl

example (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw = min raw (lastRaw - 1) := by
  rfl

example (lastRaw : Nat) :
    tangentMergedRatioLastCell lastRaw = lastRaw - 1 := by
  rfl

example {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta) :
    BankPaperCanonicalExponentBand M = Fin (M.cellCount + 1) := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalExponentBandOf M hdelta hn hW S p =
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta hn hW S).band p := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) :
    bankPaperCanonicalExponentBandLower M n W band =
      fullCutoff M n W band.1 := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) :
    bankPaperCanonicalExponentBandUpper M n W band =
      fullCutoff M n W (band.1 + 1) := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p =
      tangentMultiplicativeRawCellIndex
        (bankPaperCanonicalExponentBandLower M n W
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p))
        p.1 rho := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (rho : Real) (band : BankPaperCanonicalExponentBand M) :
    bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band =
      tangentMultiplicativeRawCellIndex
        (bankPaperCanonicalExponentBandLower M n W band)
        (bankPaperCanonicalExponentBandUpper M n W band) rho := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (rho : Real) (band : BankPaperCanonicalExponentBand M) :
    bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho band =
      tangentMergedRatioLastCell
        (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W)
          rho band) := by
  rfl

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p =
      tangentMergedRatioCellIndex
        (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p))
        (bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p) := by
  rfl

example (W : Nat) (rho : Real) :
    TangentFixedRatioPrimeIntervalOccupied W rho ↔
      forall A : Nat, W <= A ->
        ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊ := by
  rfl

/-! ## Exact elementary geometry statements -/

example {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho) < label ∧
      label <= tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  exact ⟨tangentMultiplicativeRatioCutoff_rawCell_lt_label
      hlower hrho hlabel,
    label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
      hlower hrho⟩

example {lastRaw a b : Nat} (ha : a <= lastRaw) (hb : b <= lastRaw)
    (hcell :
      tangentMergedRatioCellIndex lastRaw a =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw a + 1 =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw b + 1 =
          tangentMergedRatioCellIndex lastRaw a) :
    a <= b + 2 ∧ b <= a + 2 :=
  rawCellIndices_within_two_of_merged_sameOrAdjacent ha hb hcell

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p <=
        bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) ∧
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <=
        bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  exact ⟨bankPaperCanonicalRawRatioCellIndex_le_lastRaw
      M hdelta hn hW S rho hrho p,
    bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn hW S rho p⟩

/-! Expanded downstream shape: the exact canonical Section 8 bands and the
merged `rho`-cell indices construct `TangentRatioCellGeometry` without any
occupancy or PNT hypothesis. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 :=
  bankPaperCanonical_tangentRatioCellGeometry
    M hdelta hn hW S hrho hratio

/-! Expanded analytic boundary: uniform prime occupancy of fixed-ratio
natural intervals implies exactly the nonzero-cell premise consumed by the
explicit earthmover. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hprime : forall A : Nat, W <= A ->
      ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊) :
    forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
      cell <= bankPaperCanonicalLastRatioCell M
        (n := n) (W := W) rho band ->
        tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
          band cell ≠ 0 := by
  exact bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
    M hdelta hn hW S hrho hprime

/-! Expanded complete-package shape: the only analytic premise is the
transparent fixed-ratio interval occupancy predicate. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <=
        bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)) ∧
      (forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
        cell <= bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho band ->
          tangentRatioCellCard
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
            band cell ≠ 0) ∧
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 :=
  bankPaperCanonical_ratioCellGeometry_spec
    M hdelta hn hW S hrho hratio hprime

end

end Erdos390.WholePaper
