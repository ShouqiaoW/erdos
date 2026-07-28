import Erdos390.WholePaper.BankPaperFourFivePrimeEndpoint

/-!
# Reciprocal-prime bounded-variation transfer for the four/five chamber

This file turns the audited two-endpoint Mertens estimate in
`PrimeBandQuadrature` into a finite signed-measure statement that can be
iterated in the ordered-prime mixture.

On every integer cell `(m-1,m]` we subtract the continuum mass

`log(log m) - log(log (m-1))`

from the actual reciprocal-prime atom.  The prefix of this signed cell
measure is exactly the two-endpoint reciprocal-prime discrepancy.  Finite
Abel summation then bounds its pairing with an arbitrary sequence by the
uniform discrepancy times the right-endpoint value plus the sequence's
discrete variation.  No smoothness hypothesis and no new analytic axiom are
used.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

/-- The actual reciprocal-prime atom at an integer. -/
def fourFiveReciprocalPrimeAtom (m : Nat) : Real :=
  if m.Prime then 1 / (m : Real) else 0

/-- The continuum primitive whose increments model reciprocal-prime mass. -/
def fourFiveLogLogPrimitive (m : Nat) : Real :=
  Real.log (Real.log (m : Real))

/-- The reciprocal-prime atom restricted to the strict tail above `A`. -/
def fourFiveAnchoredReciprocalPrimeAtom (A m : Nat) : Real :=
  if A < m then fourFiveReciprocalPrimeAtom m else 0

/-- Continuum log-log mass of the integer cell `(m-1,m]`, restricted to the
strict tail above `A`. -/
def fourFiveAnchoredLogLogCellAtom (A m : Nat) : Real :=
  if A < m then
    fourFiveLogLogPrimitive m - fourFiveLogLogPrimitive (m - 1)
  else 0

/-- Signed reciprocal-prime cell measure: actual prime atom minus its
continuum log-log cell mass. -/
def fourFiveReciprocalPrimeSignedCell (A m : Nat) : Real :=
  fourFiveAnchoredReciprocalPrimeAtom A m -
    fourFiveAnchoredLogLogCellAtom A m

/-- The cumulative signed reciprocal-prime discrepancy on `(A,Y]`. -/
def fourFiveReciprocalPrimeDiscrepancy (A Y : Nat) : Real :=
  fullReciprocalSum Y - fullReciprocalSum A -
    (fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A)

/-- Right-endpoint plus total discrete variation, the norm produced by
finite Abel summation on `(A,Y]`. -/
def fourFiveRightDiscreteBVNorm (f : Nat -> Real) (A Y : Nat) : Real :=
  |f Y| +
    ∑ m ∈ Finset.Ioc A (Y - 1), |f (m + 1) - f m|

/-- The reciprocal-prime signed measure paired with an arbitrary sequence. -/
def fourFiveReciprocalPrimeBVDefect
    (f : Nat -> Real) (A Y : Nat) : Real :=
  ∑ m ∈ Finset.Ioc A Y,
    f m * fourFiveReciprocalPrimeSignedCell A m

/-- Literal weighted reciprocal-prime sum on `(A,Y]`. -/
def fourFiveWeightedReciprocalPrimeSum
    (f : Nat -> Real) (A Y : Nat) : Real :=
  ∑ m ∈ Finset.Ioc A Y,
    if m.Prime then f m / (m : Real) else 0

/-- Literal weighted continuum log-log cell sum on `(A,Y]`. -/
def fourFiveWeightedLogLogCellSum
    (f : Nat -> Real) (A Y : Nat) : Real :=
  ∑ m ∈ Finset.Ioc A Y,
    f m * (fourFiveLogLogPrimitive m -
      fourFiveLogLogPrimitive (m - 1))

/-- A safe named cutoff which retains the lower endpoint `2` needed for
positive logarithms. -/
noncomputable def fourFiveReciprocalBVSafeCutoff : Nat :=
  max fullReciprocalSumUniformCutoff 2

theorem fourFiveReciprocalBVSafeCutoff_ge_uniformCutoff :
    fullReciprocalSumUniformCutoff <=
      fourFiveReciprocalBVSafeCutoff :=
  le_max_left _ _

theorem fourFiveReciprocalBVSafeCutoff_ge_two :
    2 <= fourFiveReciprocalBVSafeCutoff :=
  le_max_right _ _

/-- Summing the integer atoms through `n` gives the repository's literal
full reciprocal-prime sum. -/
theorem sum_range_fourFiveReciprocalPrimeAtom (n : Nat) :
    (∑ m ∈ Finset.range (n + 1), fourFiveReciprocalPrimeAtom m) =
      fullReciprocalSum n := by
  unfold fourFiveReciprocalPrimeAtom
    Erdos390.Full.PrimeSums.fullReciprocalSum
    Erdos390.Full.PrimeSums.primesUpTo
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hm, hp⟩
      exact ⟨⟨Nat.zero_le m, by omega⟩, hp⟩
    · rintro ⟨⟨_hm0, hmn⟩, hp⟩
      exact ⟨by omega, hp⟩
  · intro m _hm
    rfl

private theorem sum_range_anchored_eq_sub
    (f : Nat -> Real) {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1), if A < m then f m else 0) =
      (∑ m ∈ Finset.range (n + 1), f m) -
        ∑ m ∈ Finset.range (A + 1), f m := by
  have hsubset : Finset.range (A + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_mono (by omega)
  have hfilter :
      (Finset.range (n + 1)).filter (fun m => A < m) =
        Finset.range (n + 1) \ Finset.range (A + 1) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff]
    omega
  rw [← Finset.sum_filter, hfilter]
  exact (eq_sub_iff_add_eq).2 (Finset.sum_sdiff hsubset (f := f))

/-- The anchored actual-prime atoms have the expected two-endpoint mass. -/
theorem sum_range_fourFiveAnchoredReciprocalPrimeAtom
    {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveAnchoredReciprocalPrimeAtom A m) =
      fullReciprocalSum n - fullReciprocalSum A := by
  unfold fourFiveAnchoredReciprocalPrimeAtom
  rw [sum_range_anchored_eq_sub fourFiveReciprocalPrimeAtom hAn,
    sum_range_fourFiveReciprocalPrimeAtom,
    sum_range_fourFiveReciprocalPrimeAtom]

/-- The continuum cell atoms telescope exactly to the log-log increment. -/
theorem sum_range_fourFiveAnchoredLogLogCellAtom
    {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveAnchoredLogLogCellAtom A m) =
      fourFiveLogLogPrimitive n - fourFiveLogLogPrimitive A := by
  induction n with
  | zero =>
      have hA0 : A = 0 := Nat.eq_zero_of_le_zero hAn
      subst A
      simp [fourFiveAnchoredLogLogCellAtom]
  | succ n ih =>
      by_cases hAn' : A <= n
      · rw [Finset.sum_range_succ, ih hAn']
        have hAlt : A < n + 1 := by omega
        simp only [fourFiveAnchoredLogLogCellAtom, if_pos hAlt,
          Nat.add_sub_cancel]
        ring
      · have hAeq : A = n + 1 := by omega
        subst A
        rw [sub_self]
        apply Finset.sum_eq_zero
        intro m hm
        unfold fourFiveAnchoredLogLogCellAtom
        rw [if_neg]
        have hmle : m <= n + 1 := by
          have hm' := Finset.mem_range.mp hm
          omega
        omega

/-- Prefixes of the signed cell measure are exactly the reciprocal-prime
two-endpoint discrepancy. -/
theorem sum_range_fourFiveReciprocalPrimeSignedCell
    {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveReciprocalPrimeSignedCell A m) =
      fourFiveReciprocalPrimeDiscrepancy A n := by
  unfold fourFiveReciprocalPrimeSignedCell
  rw [Finset.sum_sub_distrib,
    sum_range_fourFiveAnchoredReciprocalPrimeAtom hAn,
    sum_range_fourFiveAnchoredLogLogCellAtom hAn]
  rfl

/-- The signed-cell pairing is literally the weighted reciprocal-prime sum
minus the weighted continuum log-log cell sum. -/
theorem fourFiveReciprocalPrimeBVDefect_eq_prime_sub_logLogCells
    (f : Nat -> Real) (A Y : Nat) :
    fourFiveReciprocalPrimeBVDefect f A Y =
      fourFiveWeightedReciprocalPrimeSum f A Y -
        fourFiveWeightedLogLogCellSum f A Y := by
  unfold fourFiveReciprocalPrimeBVDefect
  unfold fourFiveWeightedReciprocalPrimeSum
    fourFiveWeightedLogLogCellSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hAm : A < m := (Finset.mem_Ioc.mp hm).1
  unfold fourFiveReciprocalPrimeSignedCell
    fourFiveAnchoredReciprocalPrimeAtom
    fourFiveAnchoredLogLogCellAtom
    fourFiveReciprocalPrimeAtom
  simp only [if_pos hAm]
  split_ifs <;> ring

/-- Exact finite Abel identity for a centered prefix measure. -/
theorem fourFiveFiniteBV_by_parts
    (c f : Nat -> Real) {A Y : Nat} (hAY : A < Y)
    (hprefixA : ∑ m ∈ Finset.range (A + 1), c m = 0) :
    (∑ m ∈ Finset.Ioc A Y, f m * c m) =
      f Y * (∑ m ∈ Finset.range (Y + 1), c m) -
        ∑ m ∈ Finset.Ioc A (Y - 1),
          (f (m + 1) - f m) *
            (∑ k ∈ Finset.range (m + 1), c k) := by
  have habel := Finset.sum_Ioc_by_parts f c hAY
  simp only [smul_eq_mul] at habel
  rw [hprefixA, mul_zero, sub_zero] at habel
  exact habel

/-- A uniformly bounded centered prefix measure pairs with every sequence at
most its prefix bound times right-endpoint-plus-variation. -/
theorem abs_sum_Ioc_mul_le_prefixBound_mul_rightDiscreteBVNorm
    (c f : Nat -> Real) {A Y : Nat} {E : Real}
    (hAY : A <= Y) (hE : 0 <= E)
    (hprefixA : ∑ m ∈ Finset.range (A + 1), c m = 0)
    (hprefix : ∀ m ∈ Finset.Icc A Y,
      |(∑ k ∈ Finset.range (m + 1), c k)| <= E) :
    |(∑ m ∈ Finset.Ioc A Y, f m * c m)| <=
      E * fourFiveRightDiscreteBVNorm f A Y := by
  by_cases hEq : A = Y
  · subst Y
    have hvarNonneg : 0 <= fourFiveRightDiscreteBVNorm f A A := by
      unfold fourFiveRightDiscreteBVNorm
      positivity
    simp only [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg hE hvarNonneg
  have hlt : A < Y := lt_of_le_of_ne hAY hEq
  rw [fourFiveFiniteBV_by_parts c f hlt hprefixA]
  calc
    |f Y * (∑ m ∈ Finset.range (Y + 1), c m) -
        ∑ m ∈ Finset.Ioc A (Y - 1),
          (f (m + 1) - f m) *
            (∑ k ∈ Finset.range (m + 1), c k)| <=
      |f Y * (∑ m ∈ Finset.range (Y + 1), c m)| +
        |∑ m ∈ Finset.Ioc A (Y - 1),
          (f (m + 1) - f m) *
            (∑ k ∈ Finset.range (m + 1), c k)| := abs_sub _ _
    _ <= |f Y| * E +
        ∑ m ∈ Finset.Ioc A (Y - 1),
          |f (m + 1) - f m| * E := by
      apply add_le_add
      · rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (hprefix Y (Finset.mem_Icc.mpr ⟨hAY, le_rfl⟩))
          (abs_nonneg _)
      · calc
          |∑ m ∈ Finset.Ioc A (Y - 1),
              (f (m + 1) - f m) *
                (∑ k ∈ Finset.range (m + 1), c k)| <=
            ∑ m ∈ Finset.Ioc A (Y - 1),
              |(f (m + 1) - f m) *
                (∑ k ∈ Finset.range (m + 1), c k)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ <= ∑ m ∈ Finset.Ioc A (Y - 1),
              |f (m + 1) - f m| * E := by
            apply Finset.sum_le_sum
            intro m hm
            rw [abs_mul]
            apply mul_le_mul_of_nonneg_left
              (hprefix m (Finset.mem_Icc.mpr (by
                have hm' := Finset.mem_Ioc.mp hm
                constructor
                · exact hm'.1.le
                · omega)))
              (abs_nonneg _)
    _ = E * fourFiveRightDiscreteBVNorm f A Y := by
      unfold fourFiveRightDiscreteBVNorm
      rw [← Finset.sum_mul]
      ring

/-- Uniform cumulative reciprocal-prime discrepancy at every natural
endpoint beyond the safe cutoff. -/
theorem abs_fourFiveReciprocalPrimeDiscrepancy_le_uniform
    {A Y : Nat} (hA : fourFiveReciprocalBVSafeCutoff <= A)
    (hAY : A <= Y) :
    |fourFiveReciprocalPrimeDiscrepancy A Y| <=
      5 * fullReciprocalSumUniformConstant /
        Real.log (A : Real) ^ 3 := by
  unfold fourFiveReciprocalPrimeDiscrepancy fourFiveLogLogPrimitive
  exact fullReciprocalSumUniform_bound A Y
    (fourFiveReciprocalBVSafeCutoff_ge_uniformCutoff.trans hA) hAY

/-- Unconditional reciprocal-prime bounded-variation transfer.  The same
constant and cutoff work for every interval and every real-valued sequence;
only the displayed discrete BV norm of the sequence remains. -/
theorem abs_fourFiveReciprocalPrimeBVDefect_le_uniform
    (f : Nat -> Real) {A Y : Nat}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y) :
    |fourFiveReciprocalPrimeBVDefect f A Y| <=
      (5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 3) *
        fourFiveRightDiscreteBVNorm f A Y := by
  have hA2 : 2 <= A :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hA
  have hlogApos : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hE :
      0 <= 5 * fullReciprocalSumUniformConstant /
        Real.log (A : Real) ^ 3 := by
    exact div_nonneg
      (mul_nonneg (by norm_num) fullReciprocalSumUniformConstant_pos.le)
      (pow_nonneg hlogApos.le 3)
  apply abs_sum_Ioc_mul_le_prefixBound_mul_rightDiscreteBVNorm
    (fourFiveReciprocalPrimeSignedCell A) f hAY hE
  · rw [sum_range_fourFiveReciprocalPrimeSignedCell (A := A)
      (n := A) le_rfl]
    simp [fourFiveReciprocalPrimeDiscrepancy]
  · intro m hm
    rw [sum_range_fourFiveReciprocalPrimeSignedCell
      (A := A) (n := m) (Finset.mem_Icc.mp hm).1]
    exact abs_fourFiveReciprocalPrimeDiscrepancy_le_uniform hA
      (Finset.mem_Icc.mp hm).1

/-- Paper-facing form: the actual weighted reciprocal-prime sum differs
from the weighted log-log cell sum by at most the uniform Mertens discrepancy
times the weight's discrete BV norm. -/
theorem abs_fourFiveWeightedReciprocalPrimeSum_sub_logLogCells_le_uniform
    (f : Nat -> Real) {A Y : Nat}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y) :
    |fourFiveWeightedReciprocalPrimeSum f A Y -
        fourFiveWeightedLogLogCellSum f A Y| <=
      (5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 3) *
        fourFiveRightDiscreteBVNorm f A Y := by
  rw [← fourFiveReciprocalPrimeBVDefect_eq_prime_sub_logLogCells]
  exact abs_fourFiveReciprocalPrimeBVDefect_le_uniform f hA hAY

end Erdos390.WholePaper.BankPaperRealization
