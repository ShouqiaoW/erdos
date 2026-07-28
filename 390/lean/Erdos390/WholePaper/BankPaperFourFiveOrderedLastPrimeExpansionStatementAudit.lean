import Erdos390.WholePaper.BankPaperFourFiveOrderedLastPrimeExpansion

/-! Expanded statement audit for the exact last-prime expansion. -/

open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperRealization

#check fourFivePrimeCoordinateBand
#check fourFiveOrderedPrimeTupleSet
#check mem_fourFivePrimeCoordinateBand
#check mem_fourFiveOrderedPrimeTupleSet
#check fourFiveTupleToListEmbedding
#check map_fourFiveOrderedPrimeTupleSet_eq_factorLists
#check fourFiveOrderedPrimeTupleSet_card_eq_layerMass
#check fourFiveOrderedPrimePrefixSet
#check mem_fourFiveOrderedPrimePrefixSet
#check fourFiveLastPrimeFiber
#check mem_fourFiveLastPrimeFiber
#check fourFiveLastPrimeSplitSet
#check mem_fourFiveLastPrimeSplitSet
#check fourFiveSnocEmbedding
#check map_fourFiveLastPrimeSplitSet_eq_tupleSet
#check fourFiveLastPrimeSplitSet_card_eq_sum_fibers
#check fourFiveOrderedPrimeLayerMass_eq_sum_lastPrimeFibers
#check fourFiveLastPrimeLower
#check fourFiveLastPrimeUpper
#check fourFiveLastPrimeFiber_eq_primeInterval
#check fourFiveOrderedPrimePrefix_prod_pos
#check fourFiveLastPrimeFiber_card_eq_primeCounting_sub
#check fourFiveLastPrimeIntegral
#check fourFiveLastPrimeEndpointError
#check fourFiveLastPrimeLower_ge_y
#check abs_fourFiveLastPrimeFiber_card_sub_integral_le
#check fourFiveOrderedLastPrimeIntegralLayer
#check fourFiveOrderedLastPrimeEndpointErrorLayer
#check abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
#check exists_abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le

example (m y A B : Nat) :
    fourFiveOrderedPrimeLayerMass (m + 1) y A B =
      ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (fourFiveLastPrimeFiber q y A B).card :=
  fourFiveOrderedPrimeLayerMass_eq_sum_lastPrimeFibers m y A B

example :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      forall {m y A B : Nat}, X0 <= (y : Real) ->
        abs ((fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
            fourFiveOrderedLastPrimeIntegralLayer m y A B) <=
          fourFiveOrderedLastPrimeEndpointErrorLayer C m y A B :=
  exists_abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le

end Erdos390.WholePaper.BankPaperRealization
