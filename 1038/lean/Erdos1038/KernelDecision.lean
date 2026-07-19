import Mathlib

/-!
# Kernel-checked closed decisions

`native_decide` is deliberately not used in the final proof: it introduces
the compiler-trust axioms `Lean.ofReduceBool` and `Lean.trustCompiler`.

`kernel_decide` first asks the kernel to close a definitionally true goal
with full transparency.  For a closed decidable proposition which is not
itself reflexive, it instead proves `decide p = true` by full kernel
reduction and applies the ordinary theorem `of_decide_eq_true`.  Thus the
resulting declaration contains no native-evaluator trust axiom.
-/

set_option warningAsError true

/-- Discharge a closed decidable proposition by proof-producing kernel
reduction, without `Lean.ofReduceBool` or `Lean.trustCompiler`. -/
macro "kernel_decide" : tactic =>
  `(tactic| first | rfl' | exact of_decide_eq_true (by rfl'))
