import Erdos1038.HighKPlatformAffineTableData
import Erdos1038.HighKPlatformAffineSemanticCorner
import Erdos1038.KernelDecision

/-! Generated affine qOuter semantic enclosure for cell 178. -/

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineSemanticCorner

def qOuter_178 : RatInterval :=
  ⟨2902537744142 / 1000000000000,
    2916557263613 / 1000000000000⟩

theorem qEnclosed_178 : EvalEnclosed
    (data ⟨178, by decide⟩).boxes
    (qmaxE scalarSqrtSteps .affine) qOuter_178 := by
  exact evalEnclosed_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
