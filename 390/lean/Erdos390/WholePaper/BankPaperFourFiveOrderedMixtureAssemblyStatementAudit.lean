import Erdos390.WholePaper.BankPaperFourFiveOrderedMixtureAssembly

/-! Expanded statement audit for the final factorial mixture assembly. -/

namespace Erdos390.WholePaper.BankPaperRealization

#check fourFiveContinuumLayerOneMain
#check fourFiveContinuumLayerTwoMain
#check fourFiveContinuumLayerThreeMain
#check fourFiveContinuumLayerFourMain
#check fourFiveContinuumOrderedMixtureMain
#check fourFiveContinuumMixtureIntegralMain
#check fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
#check fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_paperRange
#check fourFiveFactorialErrorLedger
#check fourFiveOrderedPrimeMixture_eq_explicitLayers
#check fourFiveOrderedPrimeMixtureEstimate_of_layerBounds
#check fourFiveMovingFaceProductError
#check FourFiveLastPrimeToContinuumBridge
#check fourFiveOrderedMixtureAssemblyError
#check fourFiveOrderedPrimeMixtureEstimate_of_lastPrime_continuumBridge
#check exists_fourFiveOrderedPrimeMixtureEstimate_of_continuumBridge

example {y A B : Nat} {L1 L2 L3 L4 e1 e2 e3 e4 : Real}
    (h1 : abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) <= e1)
    (h2 : abs ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) <= e2)
    (h3 : abs ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) <= e3)
    (h4 : abs ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) <= e4) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (L1 + L2 / 2 + L3 / 6 + L4 / 24)
      (fourFiveFactorialErrorLedger e1 e2 e3 e4) :=
  fourFiveOrderedPrimeMixtureEstimate_of_layerBounds h1 h2 h3 h4

end Erdos390.WholePaper.BankPaperRealization
