import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (overlap batch 1). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_211 :
    (RawFraction.add (rawPrimeLoad 211) (rawTailOverlap 211)).CrossLE
      (rawCapacity 211) := by decide
@[simp] theorem rawOverlapCrossLE_223 :
    (RawFraction.add (rawPrimeLoad 223) (rawTailOverlap 223)).CrossLE
      (rawCapacity 223) := by decide
@[simp] theorem rawOverlapCrossLE_227 :
    (RawFraction.add (rawPrimeLoad 227) (rawTailOverlap 227)).CrossLE
      (rawCapacity 227) := by decide
@[simp] theorem rawOverlapCrossLE_229 :
    (RawFraction.add (rawPrimeLoad 229) (rawTailOverlap 229)).CrossLE
      (rawCapacity 229) := by decide
@[simp] theorem rawOverlapCrossLE_233 :
    (RawFraction.add (rawPrimeLoad 233) (rawTailOverlap 233)).CrossLE
      (rawCapacity 233) := by decide
@[simp] theorem rawOverlapCrossLE_239 :
    (RawFraction.add (rawPrimeLoad 239) (rawTailOverlap 239)).CrossLE
      (rawCapacity 239) := by decide
@[simp] theorem rawOverlapCrossLE_241 :
    (RawFraction.add (rawPrimeLoad 241) (rawTailOverlap 241)).CrossLE
      (rawCapacity 241) := by decide
@[simp] theorem rawOverlapCrossLE_251 :
    (RawFraction.add (rawPrimeLoad 251) (rawTailOverlap 251)).CrossLE
      (rawCapacity 251) := by decide
@[simp] theorem rawOverlapCrossLE_257 :
    (RawFraction.add (rawPrimeLoad 257) (rawTailOverlap 257)).CrossLE
      (rawCapacity 257) := by decide

end Erdos390.WholePaper
