import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (overlap batch 4). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_373 :
    (RawFraction.add (rawPrimeLoad 373) (rawTailOverlap 373)).CrossLE
      (rawCapacity 373) := by decide
@[simp] theorem rawOverlapCrossLE_379 :
    (RawFraction.add (rawPrimeLoad 379) (rawTailOverlap 379)).CrossLE
      (rawCapacity 379) := by decide
@[simp] theorem rawOverlapCrossLE_383 :
    (RawFraction.add (rawPrimeLoad 383) (rawTailOverlap 383)).CrossLE
      (rawCapacity 383) := by decide
@[simp] theorem rawOverlapCrossLE_389 :
    (RawFraction.add (rawPrimeLoad 389) (rawTailOverlap 389)).CrossLE
      (rawCapacity 389) := by decide
@[simp] theorem rawOverlapCrossLE_397 :
    (RawFraction.add (rawPrimeLoad 397) (rawTailOverlap 397)).CrossLE
      (rawCapacity 397) := by decide
@[simp] theorem rawOverlapCrossLE_401 :
    (RawFraction.add (rawPrimeLoad 401) (rawTailOverlap 401)).CrossLE
      (rawCapacity 401) := by decide

end Erdos390.WholePaper
