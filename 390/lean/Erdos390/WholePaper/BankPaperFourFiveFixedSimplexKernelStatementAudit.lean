import Erdos390.WholePaper.BankPaperFourFiveFixedSimplexKernel

/-! Expanded statement audit for the fixed-simplex `C^1` kernel layer. -/

open Set

namespace Erdos390.WholePaper.BankPaperRealization

#check fourFiveClosedSimplex
#check isClosed_fourFiveClosedSimplex
#check fourFiveClosedSimplex_subset_Icc
#check isCompact_fourFiveClosedSimplex
#check fourFiveSimplexFactorProduct
#check fourFiveSimplexFactorProductDerivative
#check fourFiveSimplexRemainderFactor
#check fourFiveSimplexDenominator
#check fourFiveSimplexDenominatorDerivative
#check fourFiveFixedSimplexIntegrand
#check fourFiveFixedSimplexIntegrandDerivative
#check fourFiveSimplexDenominator_pos
#check continuousOn_fourFiveFixedSimplexIntegrand
#check continuousOn_fourFiveFixedSimplexIntegrandDerivative
#check hasDerivAt_fourFiveFixedSimplexIntegrand
#check fourFiveFixedSimplexKernel
#check fourFiveFixedSimplexKernelDerivative
#check hasDerivAt_fourFiveFixedSimplexKernel
#check continuousOn_fourFiveFixedSimplexKernelDerivative
#check continuousOn_fourFiveFixedSimplexKernel
#check fourFiveContinuumKernelOne
#check fourFiveContinuumKernelTwo
#check fourFiveContinuumKernelThree
#check fourFiveContinuumKernelFour
#check fourFiveContinuumKernelOneDerivative
#check fourFiveContinuumKernelTwoDerivative
#check fourFiveContinuumKernelThreeDerivative
#check fourFiveContinuumKernelFourDerivative
#check hasDerivAt_fourFiveContinuumKernelOne
#check hasDerivAt_fourFiveContinuumKernelTwo
#check hasDerivAt_fourFiveContinuumKernelThree
#check hasDerivAt_fourFiveContinuumKernelFour
#check fourFiveContinuumMixtureKernel
#check fourFiveContinuumMixtureKernelDerivative
#check hasDerivAt_fourFiveContinuumMixtureKernel
#check continuousOn_fourFiveContinuumMixtureKernel
#check continuousOn_fourFiveContinuumMixtureKernelDerivative
#check exists_fourFiveContinuumMixtureKernel_uniform_C1_bound

example {u : Real}
    (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumMixtureKernel
      (fourFiveContinuumMixtureKernelDerivative u) u :=
  hasDerivAt_fourFiveContinuumMixtureKernel hu

example :
    ∃ C : Real, 0 < C ∧
      ∀ u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        |fourFiveContinuumMixtureKernel u| <= C ∧
        |fourFiveContinuumMixtureKernelDerivative u| <= C :=
  exists_fourFiveContinuumMixtureKernel_uniform_C1_bound

end Erdos390.WholePaper.BankPaperRealization
