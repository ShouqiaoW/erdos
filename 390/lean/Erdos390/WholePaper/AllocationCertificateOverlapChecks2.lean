import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (overlap batch 2). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_263 :
    (RawFraction.add (rawPrimeLoad 263) (rawTailOverlap 263)).CrossLE
      (rawCapacity 263) := by decide
@[simp] theorem rawOverlapCrossLE_269 :
    (RawFraction.add (rawPrimeLoad 269) (rawTailOverlap 269)).CrossLE
      (rawCapacity 269) := by decide
@[simp] theorem rawOverlapCrossLE_271 :
    (RawFraction.add (rawPrimeLoad 271) (rawTailOverlap 271)).CrossLE
      (rawCapacity 271) := by decide
@[simp] theorem rawOverlapCrossLE_277 :
    (RawFraction.add (rawPrimeLoad 277) (rawTailOverlap 277)).CrossLE
      (rawCapacity 277) := by decide
@[simp] theorem rawOverlapCrossLE_281 :
    (RawFraction.add (rawPrimeLoad 281) (rawTailOverlap 281)).CrossLE
      (rawCapacity 281) := by decide
@[simp] theorem rawOverlapCrossLE_283 :
    (RawFraction.add (rawPrimeLoad 283) (rawTailOverlap 283)).CrossLE
      (rawCapacity 283) := by decide
@[simp] theorem rawOverlapCrossLE_293 :
    (RawFraction.add (rawPrimeLoad 293) (rawTailOverlap 293)).CrossLE
      (rawCapacity 293) := by decide
@[simp] theorem rawOverlapCrossLE_307 :
    (RawFraction.add (rawPrimeLoad 307) (rawTailOverlap 307)).CrossLE
      (rawCapacity 307) := by decide
@[simp] theorem rawOverlapCrossLE_311 :
    (RawFraction.add (rawPrimeLoad 311) (rawTailOverlap 311)).CrossLE
      (rawCapacity 311) := by decide

end Erdos390.WholePaper
