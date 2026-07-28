import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpRoundedValuationRateConnector

/-!
# Statement audit for the sharp rounded smooth-source valuation connector

The terminal theorem combines the sharp unrounded common-profile estimate
with the exact rounded decomposition.  The auxiliary checks expose both
finite estimates used to close its two summands.
-/

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

namespace BankPaperRealization

#check
  abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
#check
  abs_bankPaperCanonicalTopFrozenNearestIntegerCellMass_le_quarter
#check
  abs_bankPaperCanonicalTopFrozenNearestIntegerValuationMoment_le
#check
  exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate

end BankPaperRealization

end

end Erdos390.WholePaper
