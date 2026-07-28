import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveGeometryPrecursorConnector

/-!
# Statement audit for the signed exceptional four/five geometry precursor
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

namespace BankPaperRealization

#check eventually_two_mul_tangentPaperExceptionalCutoff_le_yNat
#check roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
#check eventually_roughCanonicalFourFiveFrozenCoordinate_mem_padded_of_deepCore
#check RoughCanonicalSignedExceptionalFourFiveScalarBoundsAt
#check eventually_roughCanonicalSignedExceptionalFourFiveScalarBoundsAt
#check RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
#check RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt.variation_coordinates
#check eventually_roughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt

example {W n : Nat} {deltaStar : Real}
    (h :
      RoughCanonicalSignedExceptionalFourFiveGeometryPrecursorAt
        W n deltaStar) :
    ∀ p : Nat, p.Prime -> W < p ->
      ∀ k ∈ positiveExponents
          (tangentPaperExceptionalCutoff deltaStar n / 2),
        ∀ m ∈ Finset.Icc 1
            ((tangentPaperExceptionalCutoff deltaStar n / 2) / p ^ k),
          roughCanonicalFourFiveFrozenCoordinate n (p ^ k * m) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) :=
  h.variation_coordinates

end BankPaperRealization

end Erdos390.WholePaper
