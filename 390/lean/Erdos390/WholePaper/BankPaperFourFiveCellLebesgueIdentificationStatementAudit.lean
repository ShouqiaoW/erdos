import Erdos390.WholePaper.BankPaperFourFiveCellLebesgueIdentification

/-! Expanded statement audit for exact cell-to-Lebesgue identification. -/

namespace Erdos390.WholePaper.BankPaperRealization

#check fourFiveLogLogLebesgueDensity
#check hasDerivAt_fourFiveLogLogPrimitiveReal
#check continuousOn_fourFiveLogLogLebesgueDensity
#check integral_fourFiveLogLogLebesgueDensity
#check fourFiveLogLogLebesgueCellAtom
#check fourFiveLogLogCell_eq_lebesgueCell
#check fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell
#check fourFiveWeightedLogLogCellSum_eq_lebesgueCells
#check fourFiveLebesgueCellProductOne
#check fourFiveLebesgueCellProductTwo
#check fourFiveLebesgueCellProductThree
#check fourFiveContinuumLogLogProductOne_eq_lebesgueCells
#check fourFiveContinuumLogLogProductTwo_eq_lebesgueCells
#check fourFiveContinuumLogLogProductThree_eq_lebesgueCells

example {m : Nat} (hm : 3 <= m) :
    fourFiveLogLogPrimitive m - fourFiveLogLogPrimitive (m - 1) =
      fourFiveLogLogLebesgueCellAtom m :=
  fourFiveLogLogCell_eq_lebesgueCell hm

end Erdos390.WholePaper.BankPaperRealization
