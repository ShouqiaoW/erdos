import Erdos390.Full.CanonicalRegularMeshEndpointFamily
import Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge
import Erdos390.WholePaper.TangentDistributedFlowCensus

/-!
# Canonical exponent bands and merged multiplicative ratio cells

This file supplies the elementary geometry missing between the canonical
regular exponent mesh and the explicit ratio-cell earthmover.

For a natural lower endpoint `A` and a fixed real `rho > 1`, the raw
multiplicative cutoffs are

`floor (A * rho ^ k)`.

The raw cell of a label is the first interval

`(floor (A * rho ^ k), floor (A * rho ^ (k+1))]`

which contains it.  In each canonical exponent band the final raw fragment
is merged into its predecessor.  Thus a merged cell contains at most two raw
cells, and adjacent merged cells span at most three powers of `rho`.  This is
the exact reason that the paper chooses `rho ^ 3 < r0`.

Everything in this module is finite and elementary.  The final section
isolates the one genuinely analytic input still needed for the earthmover:
prime occupancy of every full fixed-ratio interval.  No prime-distribution
statement is stored in the geometry construction.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PositiveCellTransfer
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Raw multiplicative cells -/

/-- The natural cutoff `floor (A * rho^k)` used by a multiplicative cell. -/
def tangentMultiplicativeRatioCutoff
    (lower : Nat) (rho : Real) (k : Nat) : Nat :=
  ⌊(lower : Real) * rho ^ k⌋₊

@[simp]
theorem tangentMultiplicativeRatioCutoff_zero
    (lower : Nat) (rho : Real) :
    tangentMultiplicativeRatioCutoff lower rho 0 = lower := by
  simp [tangentMultiplicativeRatioCutoff]

theorem tangentMultiplicativeRatioCutoff_mono
    {lower : Nat} {rho : Real} (hrho : 1 <= rho) :
    Monotone (tangentMultiplicativeRatioCutoff lower rho) := by
  intro i j hij
  unfold tangentMultiplicativeRatioCutoff
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_left
  · exact pow_le_pow_right₀ (by linarith) hij
  · exact Nat.cast_nonneg lower

/-- Powers of a fixed `rho > 1` eventually cover every natural label. -/
theorem exists_label_le_tangentMultiplicativeRatioCutoff_succ
    {lower : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (label : Nat) :
    ∃ k : Nat,
      label <= tangentMultiplicativeRatioCutoff lower rho (k + 1) := by
  have hlowerReal : 0 < (lower : Real) := by exact_mod_cast hlower
  obtain ⟨k, hk⟩ :=
    pow_unbounded_of_one_lt ((label : Real) / (lower : Real)) hrho
  exact ⟨k, by
    apply Nat.le_floor
    have hk' : (label : Real) < (lower : Real) * rho ^ k := by
      have := (div_lt_iff₀ hlowerReal).mp hk
      simpa only [mul_comm] using this
    have hpow : rho ^ k <= rho ^ (k + 1) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    exact hk'.le.trans
      (mul_le_mul_of_nonneg_left hpow hlowerReal.le)⟩

/-- The first raw multiplicative cell whose upper cutoff contains `label`.
The totalized branches are irrelevant in the paper range, where `lower > 0`
and `rho > 1`; keeping the definition total avoids proof arguments in the
cell-index function consumed by the earthmover. -/
def tangentMultiplicativeRawCellIndex
    (lower label : Nat) (rho : Real) : Nat :=
  if h : 0 < lower ∧ 1 < rho then
    Nat.find
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        h.1 h.2 label)
  else 0

theorem label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    label <= tangentMultiplicativeRatioCutoff lower rho
      (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  exact Nat.find_spec
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho label)

theorem tangentMultiplicativeRatioCutoff_rawCell_lt_label
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho) < label := by
  let H := exists_label_le_tangentMultiplicativeRatioCutoff_succ
    hlower hrho label
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩]
  by_cases hk : Nat.find H = 0
  · simpa only [hk, tangentMultiplicativeRatioCutoff_zero] using hlabel
  · have hkone : 1 <= Nat.find H := Nat.one_le_iff_ne_zero.mpr hk
    have hminimal := Nat.find_min H
      (m := Nat.find H - 1) (Nat.sub_one_lt hk)
    have hpred : Nat.find H - 1 + 1 = Nat.find H :=
      Nat.sub_add_cancel hkone
    rw [hpred] at hminimal
    exact Nat.lt_of_not_ge hminimal

theorem tangentMultiplicativeRawCellIndex_mono
    {lower x y : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hxy : x <= y) :
    tangentMultiplicativeRawCellIndex lower x rho <=
      tangentMultiplicativeRawCellIndex lower y rho := by
  unfold tangentMultiplicativeRawCellIndex
  rw [dif_pos ⟨hlower, hrho⟩, dif_pos ⟨hlower, hrho⟩]
  apply Nat.find_min'
    (exists_label_le_tangentMultiplicativeRatioCutoff_succ
      hlower hrho x)
  exact hxy.trans
    (Nat.find_spec
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        hlower hrho y))

theorem tangentMultiplicativeRawCellIndex_eq_of_mem
    {lower label cell : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho)
    (hlowerCell : tangentMultiplicativeRatioCutoff lower rho cell < label)
    (hupperCell : label <=
      tangentMultiplicativeRatioCutoff lower rho (cell + 1)) :
    tangentMultiplicativeRawCellIndex lower label rho = cell := by
  have hle : tangentMultiplicativeRawCellIndex lower label rho <= cell := by
    unfold tangentMultiplicativeRawCellIndex
    rw [dif_pos ⟨hlower, hrho⟩]
    exact Nat.find_min'
      (exists_label_le_tangentMultiplicativeRatioCutoff_succ
        hlower hrho label) hupperCell
  apply Nat.le_antisymm hle
  by_contra hnot
  have hlt : tangentMultiplicativeRawCellIndex lower label rho < cell :=
    Nat.lt_of_not_ge hnot
  have hrawUpper :=
    label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
      hlower hrho (label := label)
  have hcutMono := tangentMultiplicativeRatioCutoff_mono
    (lower := lower) (rho := rho) hrho.le
  have hcut : tangentMultiplicativeRatioCutoff lower rho
      (tangentMultiplicativeRawCellIndex lower label rho + 1) <=
        tangentMultiplicativeRatioCutoff lower rho cell :=
    hcutMono (by omega)
  omega

theorem tangentMultiplicativeRawCell_real_lower_lt
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) (hlabel : lower < label) :
    (lower : Real) *
        rho ^ tangentMultiplicativeRawCellIndex lower label rho <
      (label : Real) := by
  have hnat := tangentMultiplicativeRatioCutoff_rawCell_lt_label
    hlower hrho hlabel
  exact (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg lower)
    (pow_nonneg (by linarith) _))).mp hnat

theorem tangentMultiplicativeRawCell_real_upper
    {lower label : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho) :
    (label : Real) <= (lower : Real) *
      rho ^ (tangentMultiplicativeRawCellIndex lower label rho + 1) := by
  have hnat :=
    label_le_tangentMultiplicativeRatioCutoff_rawCell_succ
      hlower hrho (label := label)
  have hcast : (label : Real) <=
      (tangentMultiplicativeRatioCutoff lower rho
        (tangentMultiplicativeRawCellIndex lower label rho + 1) : Nat) := by
    exact_mod_cast hnat
  exact hcast.trans (Nat.floor_le
    (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _)))

/-! ## Merging the terminal fragment -/

/-- The paper merges the final raw fragment into its predecessor. -/
def tangentMergedRatioCellIndex (lastRaw raw : Nat) : Nat :=
  min raw (lastRaw - 1)

/-- Last index after merging the terminal raw fragment. -/
def tangentMergedRatioLastCell (lastRaw : Nat) : Nat :=
  lastRaw - 1

theorem tangentMergedRatioCellIndex_le_lastCell
    (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw <=
      tangentMergedRatioLastCell lastRaw := by
  exact Nat.min_le_right _ _

theorem tangentMergedRatioCellIndex_le_raw
    (lastRaw raw : Nat) :
    tangentMergedRatioCellIndex lastRaw raw <= raw := by
  exact Nat.min_le_left _ _

theorem tangentMergedRatioCellIndex_eq_self
    {lastRaw raw : Nat} (hraw : raw <= tangentMergedRatioLastCell lastRaw) :
    tangentMergedRatioCellIndex lastRaw raw = raw := by
  exact Nat.min_eq_left hraw

theorem tangentMergedRatioCellIndex_lastRaw
    {lastRaw : Nat} (hlast : 0 < lastRaw) :
    tangentMergedRatioCellIndex lastRaw lastRaw =
      tangentMergedRatioLastCell lastRaw := by
  unfold tangentMergedRatioCellIndex tangentMergedRatioLastCell
  exact Nat.min_eq_right (by omega)

theorem raw_le_tangentMergedRatioCellIndex_add_one
    {lastRaw raw : Nat} (hraw : raw <= lastRaw) :
    raw <= tangentMergedRatioCellIndex lastRaw raw + 1 := by
  by_cases hfull : raw <= lastRaw - 1
  · rw [tangentMergedRatioCellIndex_eq_self hfull]
    omega
  · have hcap : lastRaw - 1 <= raw := by omega
    unfold tangentMergedRatioCellIndex
    rw [Nat.min_eq_right hcap]
    omega

theorem tangentMergedRatioCellIndex_mono
    {lastRaw a b : Nat} (hab : a <= b) :
    tangentMergedRatioCellIndex lastRaw a <=
      tangentMergedRatioCellIndex lastRaw b := by
  exact min_le_min_right (lastRaw - 1) hab

/-- Same or adjacent merged cells come from raw indices at distance at most
two.  The extra unit is precisely the possible terminal merge. -/
theorem rawCellIndices_within_two_of_merged_sameOrAdjacent
    {lastRaw a b : Nat} (ha : a <= lastRaw) (hb : b <= lastRaw)
    (hcell :
      tangentMergedRatioCellIndex lastRaw a =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw a + 1 =
          tangentMergedRatioCellIndex lastRaw b ∨
        tangentMergedRatioCellIndex lastRaw b + 1 =
          tangentMergedRatioCellIndex lastRaw a) :
    a <= b + 2 ∧ b <= a + 2 := by
  have haUpper := raw_le_tangentMergedRatioCellIndex_add_one ha
  have hbUpper := raw_le_tangentMergedRatioCellIndex_add_one hb
  have haLower := tangentMergedRatioCellIndex_le_raw lastRaw a
  have hbLower := tangentMergedRatioCellIndex_le_raw lastRaw b
  rcases hcell with hsame | hforward | hbackward <;> omega

/-- If two labels have raw indices at distance at most two in this
orientation, their ratio is strictly below `rho^3`. -/
theorem tangentMultiplicativeRawCell_ratio_lt_cube
    {lower x y : Nat} {rho : Real}
    (hlower : 0 < lower) (hrho : 1 < rho)
    (_hxLower : lower < x) (hyLower : lower < y)
    (hindex : tangentMultiplicativeRawCellIndex lower x rho <=
      tangentMultiplicativeRawCellIndex lower y rho + 2) :
    (x : Real) / (y : Real) < rho ^ 3 := by
  let ix := tangentMultiplicativeRawCellIndex lower x rho
  let iy := tangentMultiplicativeRawCellIndex lower y rho
  have hxUpper : (x : Real) <= (lower : Real) * rho ^ (ix + 1) := by
    simpa only [ix] using
      (tangentMultiplicativeRawCell_real_upper
        hlower hrho (label := x))
  have hyLowerReal : (lower : Real) * rho ^ iy < (y : Real) := by
    simpa only [iy] using
      (tangentMultiplicativeRawCell_real_lower_lt
        hlower hrho hyLower)
  have hpow : rho ^ (ix + 1) <= rho ^ (iy + 3) := by
    apply pow_le_pow_right₀ (by linarith)
    dsimp only [ix, iy]
    omega
  have hxToBoundary : (x : Real) <=
      (lower : Real) * rho ^ (iy + 3) :=
    hxUpper.trans
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg lower))
  have hrhoCubePos : 0 < rho ^ 3 := pow_pos (by linarith) _
  have hboundary : (lower : Real) * rho ^ (iy + 3) <
      (y : Real) * rho ^ 3 := by
    rw [show iy + 3 = iy + 3 by rfl, pow_add]
    simpa only [mul_assoc] using
      (mul_lt_mul_of_pos_right hyLowerReal hrhoCubePos)
  have hyPos : (0 : Real) < y := by
    exact_mod_cast (hlower.trans hyLower)
  rw [div_lt_iff₀ hyPos]
  calc
    (x : Real) <= (lower : Real) * rho ^ (iy + 3) := hxToBoundary
    _ < (y : Real) * rho ^ 3 := hboundary
    _ = rho ^ 3 * (y : Real) := mul_comm _ _

/-! ## The canonical paper exponent bands -/

/-- The finite exponent-band type: one moving low band followed by the
positive regular relative mesh. -/
abbrev BankPaperCanonicalExponentBand
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta) :=
  Fin (M.cellCount + 1)

/-- Exact canonical band assignment already used by the Section 8
arithmetic partition. -/
def bankPaperCanonicalExponentBandOf
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    BankPaperCanonicalExponentBand M :=
  (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S).band p

/-- Natural lower endpoint of one canonical exponent band. -/
def bankPaperCanonicalExponentBandLower
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) : Nat :=
  fullCutoff M n W band.1

/-- Natural upper endpoint of one canonical exponent band. -/
def bankPaperCanonicalExponentBandUpper
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (n W : Nat) (band : BankPaperCanonicalExponentBand M) : Nat :=
  fullCutoff M n W (band.1 + 1)

theorem bankPaperCanonicalExponentBandOf_mem_interval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalExponentBandLower M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) < p.1 ∧
      p.1 <= bankPaperCanonicalExponentBandUpper M n W
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  have hp := (E.band_eq_iff p (P.band p)).mp rfl
  simpa only [P, E, bankPaperCanonicalExponentBandOf,
    bankPaperCanonicalExponentBandLower,
    bankPaperCanonicalExponentBandUpper,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using hp

theorem bankPaperCanonicalExponentBandLower_pos
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (band : BankPaperCanonicalExponentBand M) :
    0 < bankPaperCanonicalExponentBandLower M n W band := by
  have hcut :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
      M hdelta hn hW S).cutoff_le_lower band
  have hWpos : 0 < W := Nat.pos_of_ne_zero hW
  simpa only [bankPaperCanonicalExponentBandLower,
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using
      hWpos.trans_le hcut

/-- Raw `rho`-cell index of a canonical tangent prime inside its exact
Section 8 exponent band. -/
def bankPaperCanonicalRawRatioCellIndex
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Nat :=
  tangentMultiplicativeRawCellIndex
    (bankPaperCanonicalExponentBandLower M n W
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p))
    p.1 rho

/-- Index of the terminal raw fragment in one canonical exponent band. -/
def bankPaperCanonicalLastRawRatioCell
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (rho : Real)
    (band : BankPaperCanonicalExponentBand M) : Nat :=
  tangentMultiplicativeRawCellIndex
    (bankPaperCanonicalExponentBandLower M n W band)
    (bankPaperCanonicalExponentBandUpper M n W band) rho

/-- Last occupied index expected by the earthmover after the possible
terminal raw fragment is merged. -/
def bankPaperCanonicalLastRatioCell
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (rho : Real)
    (band : BankPaperCanonicalExponentBand M) : Nat :=
  tangentMergedRatioLastCell
    (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho band)

/-- Merged canonical ratio-cell index. -/
def bankPaperCanonicalRatioCellIndex
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) : Nat :=
  tangentMergedRatioCellIndex
    (bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p))
    (bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p)

/-- Every raw prime cell lies before the raw terminal fragment. -/
theorem bankPaperCanonicalRawRatioCellIndex_le_lastRaw
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (hrho : 1 < rho)
    (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p <=
      bankPaperCanonicalLastRawRatioCell M (n := n) (W := W) rho
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S p
  have hlower := bankPaperCanonicalExponentBandLower_pos
    M hdelta hn hW S band
  have hpUpper :=
    (bankPaperCanonicalExponentBandOf_mem_interval
      M hdelta hn hW S p).2
  exact tangentMultiplicativeRawCellIndex_mono
    hlower hrho hpUpper

/-- Finite tail coverage in the exact shape required by
`tangentRatioCellEarthmoverFlow`. -/
theorem bankPaperCanonicalRatioCellIndex_le_lastCell
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    (rho : Real) (p : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <=
      bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S p) := by
  exact tangentMergedRatioCellIndex_le_lastCell _ _

/-- Order of labels inside one exponent band is respected by both the raw
and merged cell indices. -/
theorem bankPaperCanonicalRatioCellIndex_mono_of_sameBand
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    {p q : BankPaperCanonicalTangentPrime n W}
    (hband : bankPaperCanonicalExponentBandOf M hdelta hn hW S p =
      bankPaperCanonicalExponentBandOf M hdelta hn hW S q)
    (hpq : p.1 <= q.1) :
    bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p <=
      bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho q := by
  have hlower := bankPaperCanonicalExponentBandLower_pos
    M hdelta hn hW S
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S p)
  have hraw :
      bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho p <=
        bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho q := by
    unfold bankPaperCanonicalRawRatioCellIndex
    rw [← hband]
    exact tangentMultiplicativeRawCellIndex_mono hlower hrho hpq
  unfold bankPaperCanonicalRatioCellIndex
  rw [← hband]
  exact tangentMergedRatioCellIndex_mono hraw

/-- Same or adjacent canonical merged cells have label ratio below
`rho^3`. -/
theorem bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    {source target : BankPaperCanonicalTangentPrime n W}
    (hcell : TangentSameOrAdjacentRatioCell
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
      source target) :
    (((max (bankPaperCanonicalTangentPrimeLabel source)
          (bankPaperCanonicalTangentPrimeLabel target) : Nat) : Real) /
      ((min (bankPaperCanonicalTangentPrimeLabel source)
          (bankPaperCanonicalTangentPrimeLabel target) : Nat) : Real)) <
        rho ^ 3 := by
  let band := bankPaperCanonicalExponentBandOf M hdelta hn hW S source
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  let sourceRaw :=
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho source
  let targetRaw :=
    bankPaperCanonicalRawRatioCellIndex M hdelta hn hW S rho target
  have hband : band =
      bankPaperCanonicalExponentBandOf M hdelta hn hW S target := hcell.1
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  have hsourceLower : lower < source.1 := by
    simpa only [band, lower] using
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S source).1
  have htargetLower : lower < target.1 := by
    have ht :=
      (bankPaperCanonicalExponentBandOf_mem_interval
        M hdelta hn hW S target).1
    simpa only [lower, band, hband] using ht
  have hsourceRaw : sourceRaw <= lastRaw := by
    simpa only [sourceRaw, lastRaw, band] using
      bankPaperCanonicalRawRatioCellIndex_le_lastRaw
        M hdelta hn hW S rho hrho source
  have htargetRaw : targetRaw <= lastRaw := by
    have ht := bankPaperCanonicalRawRatioCellIndex_le_lastRaw
      M hdelta hn hW S rho hrho target
    simpa only [targetRaw, lastRaw, band, hband] using ht
  have hmerged :
      tangentMergedRatioCellIndex lastRaw sourceRaw =
          tangentMergedRatioCellIndex lastRaw targetRaw ∨
        tangentMergedRatioCellIndex lastRaw sourceRaw + 1 =
          tangentMergedRatioCellIndex lastRaw targetRaw ∨
        tangentMergedRatioCellIndex lastRaw targetRaw + 1 =
          tangentMergedRatioCellIndex lastRaw sourceRaw := by
    simpa only [bankPaperCanonicalRatioCellIndex, sourceRaw, targetRaw,
      lastRaw, band, hband] using hcell.2
  have hrawDistance :=
    rawCellIndices_within_two_of_merged_sameOrAdjacent
      hsourceRaw htargetRaw hmerged
  by_cases hlabels : source.1 <= target.1
  · change (((max source.1 target.1 : Nat) : Real) /
      ((min source.1 target.1 : Nat) : Real)) < rho ^ 3
    rw [max_eq_right hlabels, min_eq_left hlabels]
    apply tangentMultiplicativeRawCell_ratio_lt_cube
      hlower hrho htargetLower hsourceLower
    simpa only [sourceRaw, targetRaw,
      bankPaperCanonicalRawRatioCellIndex, lower, band, hband] using
      hrawDistance.2
  · have hreverse : target.1 <= source.1 := Nat.le_of_not_ge hlabels
    change (((max source.1 target.1 : Nat) : Real) /
      ((min source.1 target.1 : Nat) : Real)) < rho ^ 3
    rw [max_eq_left hreverse, min_eq_right hreverse]
    apply tangentMultiplicativeRawCell_ratio_lt_cube
      hlower hrho hsourceLower htargetLower
    simpa only [sourceRaw, targetRaw,
      bankPaperCanonicalRawRatioCellIndex, lower, band, hband] using
      hrawDistance.1

/-- Concrete constructor of the downstream fixed-ratio geometry predicate.
The only numerical fact used after the cell construction is
`rho^3 < r0`. -/
theorem bankPaperCanonical_tangentRatioCellGeometry
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho r0 : Real} (hrho : 1 < rho) (hratio : rho ^ 3 < r0) :
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
      (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 := by
  intro source target hcell
  exact (bankPaperCanonical_sameOrAdjacentRatioCell_ratio_lt_cube
    M hdelta hn hW S hrho hcell).trans hratio |>.le

/-! ## Exact analytic occupancy boundary -/

/-- Uniform fixed-ratio prime occupancy above one fixed cutoff.  This is the
precise PNT consequence needed to populate all *full* raw cells. -/
def TangentFixedRatioPrimeIntervalOccupied
    (W : Nat) (rho : Real) : Prop :=
  forall A : Nat, W <= A ->
    ∃ p : Nat, p.Prime ∧ A < p ∧ p <= ⌊rho * (A : Real)⌋₊

/-- The full raw cells of every canonical exponent band are occupied once
the fixed-ratio PNT input is available.  The possibly short final raw
fragment is not required to be occupied separately because it is merged
into the preceding cell. -/
theorem bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {n W : Nat} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (S : ScaleSeparation M n W)
    {rho : Real} (hrho : 1 < rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho) :
    forall (band : BankPaperCanonicalExponentBand M) (cell : Nat),
      cell <= bankPaperCanonicalLastRatioCell M
        (n := n) (W := W) rho band ->
        tangentRatioCellCard
          (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
          (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
          band cell ≠ 0 := by
  intro band cell hcell
  let P := RegularMeshPrimeCutoffs.Mesh.canonicalPartition
    M hdelta hn hW S
  let E := RegularMeshPrimeCutoffs.Mesh.canonicalCertificate
    M hdelta hn hW S
  let lower := bankPaperCanonicalExponentBandLower M n W band
  let upper := bankPaperCanonicalExponentBandUpper M n W band
  let lastRaw := bankPaperCanonicalLastRawRatioCell M
    (n := n) (W := W) rho band
  have hlower : 0 < lower := by
    exact bankPaperCanonicalExponentBandLower_pos
      M hdelta hn hW S band
  by_cases hlast : lastRaw = 0
  · have hcellZero : cell = 0 := by
      have hcellLe : cell <= 0 := by
        simpa [bankPaperCanonicalLastRatioCell,
          tangentMergedRatioLastCell, lastRaw, hlast] using hcell
      exact Nat.eq_zero_of_le_zero hcellLe
    obtain ⟨p, hpBand⟩ := P.fiber_nonempty band
    have hpMerged :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho p = 0 := by
      unfold bankPaperCanonicalRatioCellIndex
      rw [show bankPaperCanonicalExponentBandOf M hdelta hn hW S p = band by
        simpa only [P, bankPaperCanonicalExponentBandOf] using hpBand]
      simp [lastRaw, hlast, tangentMergedRatioCellIndex]
    unfold tangentRatioCellCard
    rw [← Nat.pos_iff_ne_zero]
    apply Finset.card_pos.mpr
    exact ⟨p, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa only [P, bankPaperCanonicalExponentBandOf] using hpBand,
        hpMerged.trans hcellZero.symm⟩⟩
  · have hcellRaw : cell < lastRaw := by
      have hcell' : cell <= lastRaw - 1 := by
        simpa only [bankPaperCanonicalLastRatioCell,
          tangentMergedRatioLastCell, lastRaw] using hcell
      omega
    let A := tangentMultiplicativeRatioCutoff lower rho cell
    have hWLower : W <= lower := by
      have hcut := E.cutoff_le_lower band
      simpa only [E, lower, bankPaperCanonicalExponentBandLower,
        RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using hcut
    have hlowerBoundary : (lower : Real) <=
        (lower : Real) * rho ^ cell := by
      nth_rewrite 1 [← mul_one (lower : Real)]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg lower)
      exact one_le_pow₀ (by linarith)
    have hlowerA : lower <= A := by
      apply Nat.le_floor
      exact hlowerBoundary
    have hWA : W <= A := hWLower.trans hlowerA
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ := hprime A hWA
    have hAReal : (A : Real) <= (lower : Real) * rho ^ cell := by
      exact Nat.floor_le
        (mul_nonneg (Nat.cast_nonneg lower) (pow_nonneg (by linarith) _))
    have hrhoNonneg : 0 <= rho := by linarith
    have hnextReal : rho * (A : Real) <=
        (lower : Real) * rho ^ (cell + 1) := by
      calc
        rho * (A : Real) <= rho * ((lower : Real) * rho ^ cell) :=
          mul_le_mul_of_nonneg_left hAReal hrhoNonneg
        _ = (lower : Real) * rho ^ (cell + 1) := by
          rw [pow_succ]
          ring
    have hpNext : p <=
        tangentMultiplicativeRatioCutoff lower rho (cell + 1) := by
      exact hpUpper.trans (Nat.floor_mono hnextReal)
    have hcutMono := tangentMultiplicativeRatioCutoff_mono
      (lower := lower) (rho := rho) hrho.le
    have hlastLower :
        tangentMultiplicativeRatioCutoff lower rho lastRaw < upper := by
      have hupperStrict : lower < upper := by
        obtain ⟨q, hq⟩ := P.fiber_nonempty band
        have hqInterval := (E.band_eq_iff q band).mp hq
        exact hqInterval.1.trans_le hqInterval.2
      simpa only [lastRaw, upper, lower,
        bankPaperCanonicalLastRawRatioCell] using
        tangentMultiplicativeRatioCutoff_rawCell_lt_label
          hlower hrho hupperStrict
    have hpUpperBand : p <= upper := by
      exact hpNext.trans
        ((hcutMono (by omega : cell + 1 <= lastRaw)).trans
          hlastLower.le)
    have hpBandNat : p ∈ primeBand n W := by
      apply mem_primeBand.mpr
      exact ⟨hpPrime, hWA.trans_lt hpLower,
        hpUpperBand.trans (by
          simpa only [E, upper, bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              E.upper_le_yNat band)⟩
    let q : BankPaperCanonicalTangentPrime n W := ⟨p, hpBandNat⟩
    have hqBand :
        bankPaperCanonicalExponentBandOf M hdelta hn hW S q = band := by
      have hinterval : E.lower band < q.1 ∧ q.1 <= E.upper band := by
        constructor
        · have hLowerBand : lower <= A := hlowerA
          have : lower < p := hLowerBand.trans_lt hpLower
          simpa only [E, lower, bankPaperCanonicalExponentBandLower,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_lower] using this
        · simpa only [E, upper, bankPaperCanonicalExponentBandUpper,
            RegularMeshPrimeCutoffs.Mesh.canonicalCertificate_upper] using
              hpUpperBand
      have := (E.band_eq_iff q band).mpr hinterval
      simpa only [P, bankPaperCanonicalExponentBandOf] using this
    have hqRaw :
        bankPaperCanonicalRawRatioCellIndex
          M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRawRatioCellIndex
      rw [hqBand]
      exact tangentMultiplicativeRawCellIndex_eq_of_mem
        hlower hrho hpLower hpNext
    have hqCell :
        bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho q = cell := by
      unfold bankPaperCanonicalRatioCellIndex
      rw [hqBand, hqRaw]
      exact tangentMergedRatioCellIndex_eq_self hcell
    unfold tangentRatioCellCard
    rw [← Nat.pos_iff_ne_zero]
    apply Finset.card_pos.mpr
    exact ⟨q, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hqBand, hqCell⟩⟩

/-- Complete finite geometry package consumed by the explicit ratio-cell
earthmover: bounded indices, occupancy, and fixed-ratio locality.  The only
analytic input is the transparent fixed-ratio prime-interval predicate. -/
theorem bankPaperCanonical_ratioCellGeometry_spec
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
        cell <= bankPaperCanonicalLastRatioCell M
          (n := n) (W := W) rho band ->
          tangentRatioCellCard
            (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
            (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)
            band cell ≠ 0) ∧
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) r0 := by
  exact ⟨bankPaperCanonicalRatioCellIndex_le_lastCell
      M hdelta hn hW S rho,
    bankPaperCanonical_ratioCell_occupied_of_fixedRatioPrimeInterval
      M hdelta hn hW S hrho hprime,
    bankPaperCanonical_tangentRatioCellGeometry
      M hdelta hn hW S hrho hratio⟩

end

end Erdos390.WholePaper
