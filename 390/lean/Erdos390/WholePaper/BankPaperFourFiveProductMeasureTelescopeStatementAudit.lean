import Erdos390.WholePaper.BankPaperFourFiveProductMeasureTelescope

/-! Expanded statement audit for the finite product-measure telescope. -/

open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperRealization

#check fourFiveFiniteProductOne
#check fourFiveFiniteProductTwo
#check fourFiveFiniteProductThree
#check fourFiveFiniteProductOne_sub
#check fourFiveFiniteProductTwo_sub
#check fourFiveFiniteProductThree_sub
#check abs_fourFiveFiniteWeightedSum_le_mass_mul
#check fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le
#check fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
#check fourFiveReciprocalBVError
#check fourFiveReciprocalBVError_pos
#check fourFiveActualReciprocalProductOne
#check fourFiveContinuumLogLogProductOne
#check fourFiveActualReciprocalProductTwo
#check fourFiveContinuumLogLogProductTwo
#check fourFiveActualReciprocalProductThree
#check fourFiveContinuumLogLogProductThree
#check fourFiveActualReciprocalProductOne_sub_continuum
#check fourFiveActualReciprocalProductTwo_sub_continuum
#check fourFiveActualReciprocalProductThree_sub_continuum
#check abs_fourFiveActualReciprocalProductOne_sub_continuum_le
#check abs_fourFiveActualReciprocalProductTwo_sub_continuum_le
#check abs_fourFiveActualReciprocalProductThree_sub_continuum_le

example (K : Nat -> Nat -> Nat -> Real) {A Y : Nat} {M V : Real}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A i|) <= M)
    (hVfirst : ∀ j ∈ Finset.Ioc A Y,
      ∀ k ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (fun i => K i j k) A Y <= V)
    (hVsecond : ∀ i ∈ Finset.Ioc A Y,
      ∀ k ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (fun j => K i j k) A Y <= V)
    (hVthird : ∀ i ∈ Finset.Ioc A Y,
      ∀ j ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (K i j) A Y <= V)
    (hV0 : 0 <= V) :
    |fourFiveActualReciprocalProductThree K A Y -
        fourFiveContinuumLogLogProductThree K A Y| <=
      3 * fourFiveReciprocalBVError A * M ^ 2 * V :=
  abs_fourFiveActualReciprocalProductThree_sub_continuum_le
    K hA hAY hactualMass hcontinuumMass
      hVfirst hVsecond hVthird hV0

end Erdos390.WholePaper.BankPaperRealization
