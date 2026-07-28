import Erdos390.WholePaper.BankPaperCanonicalActualMomentReadyEventually
import Mathlib.Util.AssertNoSorry

/-!
# Axiom audit for the canonical `MomentReady` connector

Every public theorem in the connector is printed and checked for `sorry`.
-/

#print axioms Erdos390.WholePaper.eventually_bankPaperCanonical_all_le_scalePoint_lower
#print axioms Erdos390.WholePaper.eventually_bankPaperCanonical_actualMomentReady

assert_no_sorry Erdos390.WholePaper.eventually_bankPaperCanonical_all_le_scalePoint_lower
assert_no_sorry Erdos390.WholePaper.eventually_bankPaperCanonical_actualMomentReady
