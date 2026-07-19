import Erdos1038.HighKPlatformAffineTableData
import Erdos1038.HighKPlatformAffineSemanticCorner
import Erdos1038.KernelDecision

/-! Generated affine qOuter semantic enclosure for cell 40. -/

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 RatInterval HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineSemanticCorner

def qOuter_040 : RatInterval :=
  ⟨3039856812649 / 1000000000000,
    3055218668943 / 1000000000000⟩

theorem qEnclosed_040 : EvalEnclosed
    (data ⟨40, by decide⟩).boxes
    (qmaxE scalarSqrtSteps .affine) qOuter_040 := by
  exact evalEnclosed_of_check (by kernel_decide)

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
