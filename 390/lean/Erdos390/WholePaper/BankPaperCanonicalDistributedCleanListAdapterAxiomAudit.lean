import Erdos390.WholePaper.BankPaperCanonicalDistributedCleanListAdapter
import Mathlib.Util.AssertNoSorry

/-! # Assumption audit for the distributed clean-list adapter

The adapter's two public theorems have their assumptions printed and are
checked for proof placeholders in source declaration order.  Imported
dependencies retain their own module audits and are deliberately excluded
from this declaration census.
-/

#print axioms Erdos390.WholePaper.BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed
#print axioms Erdos390.WholePaper.bankPaperCanonicalRoundedSelector_weightedResidual_le_harmonicScale

assert_no_sorry Erdos390.WholePaper.BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed
assert_no_sorry Erdos390.WholePaper.bankPaperCanonicalRoundedSelector_weightedResidual_le_harmonicScale
