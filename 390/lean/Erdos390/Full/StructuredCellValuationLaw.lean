import Erdos390.Full.PrimePowerCovariance
import Erdos390.Full.StructuredCells
import Erdos390.Full.UniformFiniteProbability
import Erdos390.Full.ValuationScoreDomination

/-!
# Actual valuation law on a structured smooth cell

This file packages the literal subtype of a structured cell, its genuine
finite probability mass, and the coercion to the sampled positive integer as
one `BoundedValuationLaw`.  It removes a model-interface gap: the prime-power
covariance theorems can now be instantiated directly with the same tilted law
used by the marked-cell asymptotics.
-/

namespace Erdos390.Full.StructuredCellValuationLaw

open ArithmeticModel StructuredCells FiniteProbability
open PrimePowerCovariance ValuationScoreDomination

noncomputable section

/-- Any probability law on the literal structured-cell subtype is an actual
positive integer-valued law bounded by the cell's upper endpoint. -/
def ofProbability (H : HeadPattern.Pattern) (lo hi z : Nat)
    (mu : FiniteProbability (structuredCell H lo hi z)) :
    BoundedValuationLaw (structuredCell H lo hi z) hi where
  probability := mu
  value := fun m => (m : Nat)
  value_pos := by
    intro m
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
  value_le := by
    intro m
    exact (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1

@[simp] theorem ofProbability_probability
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (mu : FiniteProbability (structuredCell H lo hi z)) :
    (ofProbability H lo hi z mu).probability = mu := rfl

@[simp] theorem ofProbability_value
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (mu : FiniteProbability (structuredCell H lo hi z))
    (m : structuredCell H lo hi z) :
    (ofProbability H lo hi z mu).value m = (m : Nat) := rfl

/-- The genuine full valuation tilt on a nonempty structured cell, packaged
as the bounded valuation law used by the prime-power covariance ledger. -/
def valuationTilt
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) :
    BoundedValuationLaw (structuredCell H lo hi z) hi :=
  ofProbability H lo hi z
    ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
      (fun m => valuationScore P eta L m))

@[simp] theorem valuationTilt_probability
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) :
    (valuationTilt H lo hi z hS P eta L).probability =
      (uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m) := rfl

@[simp] theorem valuationTilt_value
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real)
    (m : structuredCell H lo hi z) :
    (valuationTilt H lo hi z hS P eta L).value m = (m : Nat) := rfl

@[simp] theorem valuationTilt_I
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p : Nat) :
    (valuationTilt H lo hi z hS P eta L).I p =
      fun m : structuredCell H lo hi z => divInd p (m : Nat) := rfl

@[simp] theorem valuationTilt_V
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p : Nat) :
    (valuationTilt H lo hi z hS P eta L).V p =
      fun m : structuredCell H lo hi z => valuation p (m : Nat) := rfl

@[simp] theorem valuationTilt_J
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p : Nat) :
    (valuationTilt H lo hi z hS P eta L).J p =
      fun m : structuredCell H lo hi z => higherValuation p (m : Nat) := rfl

@[simp] theorem valuationTilt_covII
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covII p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => divInd p (m : Nat))
          (fun m => divInd q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covJI
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covJI p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => higherValuation p (m : Nat))
          (fun m => divInd q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covIJ
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covIJ p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => divInd p (m : Nat))
          (fun m => higherValuation q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covJJ
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covJJ p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => higherValuation p (m : Nat))
          (fun m => higherValuation q (m : Nat)) := rfl

@[simp] theorem valuationTilt_covVV
    (H : HeadPattern.Pattern) (lo hi z : Nat)
    (hS : (structuredCell H lo hi z).Nonempty)
    (P : Finset Nat) (eta : Nat -> Real) (L : Real) (p q : Nat) :
    (valuationTilt H lo hi z hS P eta L).covVV p q =
      ((uniformOnFinset (structuredCell H lo hi z) hS).exponentialTilt
        (fun m => valuationScore P eta L m)).covariance
          (fun m => valuation p (m : Nat))
          (fun m => valuation q (m : Nat)) := rfl

end

end Erdos390.Full.StructuredCellValuationLaw
