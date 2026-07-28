import Erdos390.WholePaper.BankPaperFourFiveReciprocalPrimeBV

/-! Expanded statement audit for reciprocal-prime BV transfer. -/

open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeBandQuadrature

#check fourFiveReciprocalPrimeAtom
#check fourFiveLogLogPrimitive
#check fourFiveAnchoredReciprocalPrimeAtom
#check fourFiveAnchoredLogLogCellAtom
#check fourFiveReciprocalPrimeSignedCell
#check fourFiveReciprocalPrimeDiscrepancy
#check fourFiveRightDiscreteBVNorm
#check fourFiveReciprocalPrimeBVDefect
#check fourFiveWeightedReciprocalPrimeSum
#check fourFiveWeightedLogLogCellSum
#check fourFiveReciprocalBVSafeCutoff
#check fourFiveReciprocalBVSafeCutoff_ge_uniformCutoff
#check fourFiveReciprocalBVSafeCutoff_ge_two
#check sum_range_fourFiveReciprocalPrimeAtom
#check sum_range_fourFiveAnchoredReciprocalPrimeAtom
#check sum_range_fourFiveAnchoredLogLogCellAtom
#check sum_range_fourFiveReciprocalPrimeSignedCell
#check fourFiveReciprocalPrimeBVDefect_eq_prime_sub_logLogCells
#check fourFiveFiniteBV_by_parts
#check abs_sum_Ioc_mul_le_prefixBound_mul_rightDiscreteBVNorm
#check abs_fourFiveReciprocalPrimeDiscrepancy_le_uniform
#check abs_fourFiveReciprocalPrimeBVDefect_le_uniform
#check abs_fourFiveWeightedReciprocalPrimeSum_sub_logLogCells_le_uniform

example {A n : Nat} (hAn : A <= n) :
    (∑ m ∈ Finset.range (n + 1),
        fourFiveReciprocalPrimeSignedCell A m) =
      fourFiveReciprocalPrimeDiscrepancy A n :=
  sum_range_fourFiveReciprocalPrimeSignedCell hAn

example (c f : Nat -> Real) {A Y : Nat} {E : Real}
    (hAY : A <= Y) (hE : 0 <= E)
    (hprefixA : ∑ m ∈ Finset.range (A + 1), c m = 0)
    (hprefix : ∀ m ∈ Finset.Icc A Y,
      |(∑ k ∈ Finset.range (m + 1), c k)| <= E) :
    |(∑ m ∈ Finset.Ioc A Y, f m * c m)| <=
      E * fourFiveRightDiscreteBVNorm f A Y :=
  abs_sum_Ioc_mul_le_prefixBound_mul_rightDiscreteBVNorm
    c f hAY hE hprefixA hprefix

example (f : Nat -> Real) {A Y : Nat}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y) :
    |fourFiveWeightedReciprocalPrimeSum f A Y -
        fourFiveWeightedLogLogCellSum f A Y| <=
      (5 * fullReciprocalSumUniformConstant /
          Real.log (A : Real) ^ 3) *
        fourFiveRightDiscreteBVNorm f A Y :=
  abs_fourFiveWeightedReciprocalPrimeSum_sub_logLogCells_le_uniform
    f hA hAY

end Erdos390.WholePaper.BankPaperRealization
