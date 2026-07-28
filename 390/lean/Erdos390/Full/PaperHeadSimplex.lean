import Erdos390.Full.HeadPattern

/-!
# The literal finite head-pattern simplex used in Section 8

For a fixed finite head-prime set `P` and a positive exponent `E`, the paper
uses the vertices `0` and `E e_p`.  This module constructs those exact
valuation patterns and proves that two different vertices cannot contain the
same positive integer.  The result discharges the cell-disjointness premise
used when tagged structured cells are returned to literal integer
coordinates.
-/

namespace Erdos390.Full.PaperHeadSimplex

noncomputable section

/-- `none` is the zero pattern and `some p` is the vertex `E e_p`. -/
abbrev Tag (P : Finset Nat) := Option {p : Nat // p ∈ P}

/-- Exact exponent vector of one simplex vertex. -/
def exponent (P : Finset Nat) (E : Nat) (tag : Tag P) (r : Nat) : Nat :=
  match tag with
  | none => 0
  | some p => if r = p.1 then E else 0

/-- All vertices prescribe valuations at the same finite prime set. -/
def pattern (P : Finset Nat) (hprime : ∀ p ∈ P, p.Prime)
    (E : Nat) (tag : Tag P) : HeadPattern.Pattern where
  primes := P
  exponent := exponent P E tag
  prime_mem := hprime

@[simp] theorem exponent_none (P : Finset Nat) (E r : Nat) :
    exponent P E (none : Tag P) r = 0 := rfl

@[simp] theorem exponent_some_self (P : Finset Nat) (E : Nat)
    (p : {p : Nat // p ∈ P}) :
    exponent P E (some p) p.1 = E := by
  simp [exponent]

@[simp] theorem exponent_some_ne (P : Finset Nat) (E : Nat)
    (p : {p : Nat // p ∈ P}) (r : Nat) (hr : r ≠ p.1) :
    exponent P E (some p) r = 0 := by
  simp [exponent, hr]

/-- Distinct simplex vertices disagree at a common head prime. -/
theorem patternsSeparated (P : Finset Nat)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E) :
    forall h k : Tag P, h ≠ k -> exists p,
      p ∈ (pattern P hprime E h).primes ∧
      p ∈ (pattern P hprime E k).primes ∧
      (pattern P hprime E h).exponent p ≠
        (pattern P hprime E k).exponent p := by
  intro h k hne
  cases h with
  | none =>
      cases k with
      | none => exact (hne rfl).elim
      | some q =>
          refine ⟨q.1, q.2, q.2, ?_⟩
          simp only [pattern, exponent_none, exponent_some_self]
          exact Nat.ne_of_lt hE
  | some p =>
      cases k with
      | none =>
          refine ⟨p.1, p.2, p.2, ?_⟩
          simp only [pattern, exponent_some_self, exponent_none]
          exact Nat.ne_of_gt hE
      | some q =>
          have hpq : p.1 ≠ q.1 := by
            intro hpq
            have hpqSubtype : p = q := Subtype.ext hpq
            exact hne (congrArg some hpqSubtype)
          refine ⟨p.1, p.2, p.2, ?_⟩
          simp only [pattern, exponent_some_self]
          rw [exponent_some_ne P E q p.1 hpq]
          exact Nat.ne_of_gt hE

end

end Erdos390.Full.PaperHeadSimplex
