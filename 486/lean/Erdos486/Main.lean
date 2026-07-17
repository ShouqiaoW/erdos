import Erdos486.BiasedInterface
import Erdos486.Global

/-! # Final theorems for Erdős Problem 486 -/

namespace Erdos486

/-- The fully instantiated quantitative counterexample. -/
theorem erdos486_quantitativeCounterexample : QuantitativeCounterexample :=
  quantitativeCounterexample_of_dyadicBlockInterface erdos486BlockInterface

/-- Erdős Problem 486 has a negative answer. -/
theorem erdos486_negative : ¬Erdos486Assertion :=
  not_erdos486Assertion_of_dyadicBlockInterface erdos486BlockInterface

end Erdos486
