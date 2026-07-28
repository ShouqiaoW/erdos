import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalPhysicalReindex

/-! # Statement audit for the exact signed exceptional physical reindex -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

namespace BankPaperRealization

#check roughCanonicalRealExceptionalRoughCutoff
#check roughCanonicalRealExceptionalRoughCutoff_lt_iff
#check roughCanonicalExceptionalClippedRoughInterval
#check roughCanonicalExceptionalUpperPhysicalRoughInterval
#check roughCanonicalExceptionalHighPhysicalRoughInterval
#check roughCanonicalExceptionalBroadPhysicalRoughInterval
#check mem_roughCanonicalExceptionalClippedRoughInterval
#check roughCanonicalExceptionalPhysicalSmoothFiber
#check mem_roughCanonicalExceptionalPhysicalSmoothFiber
#check completeSmoothPart_mul_eq_of_isCompleteRoughLabel_of_smooth
#check roughCanonicalExceptionalPhysicalSmoothFiber_card_eq_clippedRoughInterval
#check paperExceptionalSmoothFiber_eq_physicalSmoothFiber
#check paperExceptionalSmoothFiber_card_eq_upperPhysicalRoughInterval
#check roughCanonicalExceptionalRawLowerSmoothFiber_eq_physical_union
#check roughCanonicalExceptionalPhysicalSmoothFiber_high_disjoint_broad
#check coprime_roughHeadModulus_iff_completeSmoothPart
#check roughHeadCompatibleRawWeight_eq_highCoreCoefficient
#check roughHeadCompatibleRawWeight_eq_broadCoreCoefficient
#check sum_roughCanonicalExceptionalRawLowerSmoothFiber_rawWeight_eq_twoPhysicalIntervals
#check roughCanonicalSignedExceptionalCoreMass_eq_threePhysicalIntervals
#check smooth_of_mem_exceptionalCorePrefix
#check roughCanonicalSignedExceptionalCoreMass_eq_threePhysicalIntervals_of_mem_prefix
#check roughCanonicalSignedExceptionalCoreMass_paper_K0_succ_eq_threePhysicalIntervals

example {n r : Nat} {deltaStar : Real}
    (hn : 0 < n) (hr : 0 < r) :
    roughCanonicalRealExceptionalRoughCutoff n deltaStar < r ↔
      RoughCanonicalExceptionalLabel n deltaStar r :=
  roughCanonicalRealExceptionalRoughCutoff_lt_iff hn hr

example {W n K0 b : Nat} {c deltaStar beta : Real}
    (hn : 0 < n) (hWy : W ≤ yNat n)
    (hb : b ∈ Finset.Icc 1
      (2 * tangentPaperExceptionalCutoff deltaStar n))
    (hcutY : 2 * tangentPaperExceptionalCutoff deltaStar n ≤ yNat n) :
    roughCanonicalSignedExceptionalCoreMass
        n (upperTailLength c n) (K0 + 1) deltaStar
        (roughHeadCompatibleRawWeight
          W n (upperTailLength c n) (K0 + 1)
          (roughHeadBalancedAlpha
            W n (upperTailLength c n) (K0 + 1) beta (L n))
          beta (L n)) b =
      ((roughCanonicalExceptionalUpperPhysicalRoughInterval
        n (upperTailLength c n) deltaStar b).card : Real) -
        ((if Nat.Coprime b (roughHeadModulus W) then
            roughHeadBalancedAlpha
              W n (upperTailLength c n) (K0 + 1) beta (L n)
          else 0) *
            ((roughCanonicalExceptionalHighPhysicalRoughInterval
              n (upperTailLength c n) (K0 + 1) deltaStar b).card : Real) +
          (if Nat.Coprime b (roughHeadModulus W) then
              beta / L n else 0) *
            ((roughCanonicalExceptionalBroadPhysicalRoughInterval
              n (upperTailLength c n) (K0 + 1) deltaStar b).card :
                Real)) :=
  roughCanonicalSignedExceptionalCoreMass_paper_K0_succ_eq_threePhysicalIntervals
    hn hWy hb hcutY

end BankPaperRealization

end Erdos390.WholePaper
