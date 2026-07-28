import Erdos390
import Mathlib.Util.AssertNoSorry

/-!
# Axiom audit

These are the five principal theorems of the *earlier conditional skeleton*.
Running `#print axioms` checks that their proofs use no project-defined
global axiom declarations.  This check does **not** discharge theorem parameters or
structure fields: an
analytic estimate supplied as a hypothesis will not appear in this output.
Consequently this file is not an axiom audit of the original paper Lemmas 7.5,
8.4, 8.6 or Proposition 8.7 and must not be read as evidence that any of those
four statements has been fully formalized.
-/

#print axioms Erdos390.Lemma75.relative_primePower_transfer
#print axioms Erdos390.Lemma75.row_primePower_transfer
#print axioms Erdos390.Lemma84.WeightedBandData.full_quotient_gap_of_inputs
#print axioms Erdos390.compensated_coefficient_norm_ledger
#print axioms Erdos390.straight_target_fit_of_lipschitz

/-! The authoritative closed whole-paper theorem. -/

#print axioms Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_sourceFirstMainAsymptotic

assert_no_sorry Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_sourceFirstMainAsymptotic

/-! Formal Conjectures definition and conclusion bridge. -/

#print axioms Erdos390.WholePaper.FormalConjecturesBridge.formalF_eq_wholePaper_f
#print axioms Erdos390.WholePaper.FormalConjecturesBridge.formalF_theta
#print axioms Erdos390.WholePaper.FormalConjecturesBridge.formalF_rhs

assert_no_sorry Erdos390.WholePaper.FormalConjecturesBridge.formalF_eq_wholePaper_f
assert_no_sorry Erdos390.WholePaper.FormalConjecturesBridge.formalF_theta
assert_no_sorry Erdos390.WholePaper.FormalConjecturesBridge.formalF_rhs
