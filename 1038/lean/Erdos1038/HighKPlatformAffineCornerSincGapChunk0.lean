import Erdos1038.HighKPlatformAffineCornerQEnclosureChunk0
import Erdos1038.HighKPlatformAffineCornerREnclosureChunk0
import Erdos1038.HighKPlatformAffineCornerSincGapUpperChunk0
import Erdos1038.HighKPlatformAffineTableData
import Erdos1038.HighKPlatformAffineSemanticCorner
import Erdos1038.KernelDecision

/-! Generated affine sincGap semantic corner check for cell 0. -/

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformAffineCornerLeafCertificates

open Erdos1038 HighKIntervalExpr
open Erdos1038.HighKPlatformFormula
open Erdos1038.HighKPlatformAffineCell
open Erdos1038.HighKPlatformAffineTableData
open Erdos1038.HighKPlatformAffineCornerComponents
open Erdos1038.HighKPlatformAffineSemanticCorner

def sincGapLower_000 : Rat := 287999 / 1000000

theorem sincGap_000 : UniformLower (data ⟨0, by decide⟩).boxes
    (sincGapSquareE scalarSqrtSteps scalarTrigDoubles .affine)
    sincGapLower_000 := by
  apply uniformLower_sincGapSquare_of_enclosures
      (qOuter := qOuter_000) (rOuter := rOuter_000)
      (gapUpper := gapUpper_000)
  · kernel_decide
  · kernel_decide
  · exact qEnclosed_000
  · exact rEnclosed_000
  · exact gapUpperCheck_000
  · kernel_decide
  · kernel_decide

end Erdos1038.HighKPlatformAffineCornerLeafCertificates
