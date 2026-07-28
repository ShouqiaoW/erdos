import Erdos390.WholePaper.AllocationCertificateData
import Erdos390.WholePaper.Constants

/-!
# Small exact-checker primitives for the finite allocation certificate

The arithmetic facts are compiled in several bounded modules.  Keeping the
shared definitions here lets each module reduce only its own small batch.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal range, positivity, and denominator conditions on one entry. -/
def AllocationEntry.Valid (e : AllocationEntry) : Prop :=
  1 ≤ e.row ∧ e.row ≤ 200 ∧
    e.row + 1 ≤ e.cofactor ∧ e.cofactor ≤ 2 * e.row + 1 ∧
      0 < e.numerator ∧ 0 < e.denominator

instance instDecidableAllocationEntryValid (e : AllocationEntry) :
    Decidable e.Valid := by
  unfold AllocationEntry.Valid
  infer_instance

/-- An unreduced nonnegative fraction checked by natural-number arithmetic. -/
structure RawFraction where
  numerator : ℕ
  denominator : ℕ
deriving DecidableEq, Repr

namespace RawFraction

def zero : RawFraction := ⟨0, 1⟩

def add (a b : RawFraction) : RawFraction :=
  ⟨a.numerator * b.denominator + b.numerator * a.denominator,
    a.denominator * b.denominator⟩

def ofEntry (e : AllocationEntry) : RawFraction :=
  ⟨e.numerator, max 1 e.denominator⟩

def toRat (a : RawFraction) : ℚ :=
  (a.numerator : ℚ) / (a.denominator : ℚ)

def sum {α : Type*} (l : List α) (f : α → RawFraction) : RawFraction :=
  match l with
  | [] => zero
  | x :: xs => add (f x) (sum xs f)

def CrossEq (a b : RawFraction) : Prop :=
  a.numerator * b.denominator = b.numerator * a.denominator

def CrossLE (a b : RawFraction) : Prop :=
  a.numerator * b.denominator ≤ b.numerator * a.denominator

instance instDecidableCrossEq (a b : RawFraction) : Decidable (a.CrossEq b) := by
  unfold CrossEq
  infer_instance

instance instDecidableCrossLE (a b : RawFraction) : Decidable (a.CrossLE b) := by
  unfold CrossLE
  infer_instance

end RawFraction

/-- The prime immediately preceding `p` on every range used below. -/
def previousPrime (p : ℕ) : ℕ :=
  Nat.findGreatest Nat.Prime (p - 1)

/-- The finite/tail overlap appearing in the paper's third condition. -/
def finiteTailOverlap (p : ℕ) : ℚ :=
  ∑ r ∈ Finset.Icc (max 201 (previousPrime p)) (p - 1), alpha r

def rawRowMass (r : ℕ) : RawFraction :=
  RawFraction.sum (finiteAllocationRowEntries r) RawFraction.ofEntry

def rawPrimeLoad (p : ℕ) : RawFraction :=
  RawFraction.sum (finiteAllocationPrimeEntries p) RawFraction.ofEntry

def rawAlpha (r : ℕ) : RawFraction :=
  ⟨1, (r + 1) * (2 * r + 1)⟩

def rawCapacity (p : ℕ) : RawFraction :=
  ⟨4029639598, 25970038185 * (p - 1)⟩

def rawTailOverlap (p : ℕ) : RawFraction :=
  let lo := max 201 (previousPrime p)
  RawFraction.sum (List.range' lo ((p - 1) + 1 - lo)) rawAlpha

end

end Erdos390.WholePaper
