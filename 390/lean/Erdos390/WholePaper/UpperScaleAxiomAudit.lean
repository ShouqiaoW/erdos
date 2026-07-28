import Erdos390.WholePaper.UpperScale
import Mathlib.Util.AssertNoSorry

/-! Chunked transitive declaration audit for the elementary real scale. -/

#print axioms Erdos390.WholePaper.log_natCast_div_natCast_tendsto_zero
#print axioms Erdos390.WholePaper.secondOrderScale_tendsto_atTop
#print axioms Erdos390.WholePaper.secondOrderScale_pos
#print axioms Erdos390.WholePaper.eventually_secondOrderScale_pos
#print axioms Erdos390.WholePaper.secondOrderScale_ratio_tendsto_zero

assert_no_sorry Erdos390.WholePaper.secondOrderScale_tendsto_atTop
assert_no_sorry Erdos390.WholePaper.eventually_secondOrderScale_pos
assert_no_sorry Erdos390.WholePaper.secondOrderScale_ratio_tendsto_zero
