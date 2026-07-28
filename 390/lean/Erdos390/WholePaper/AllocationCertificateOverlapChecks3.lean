import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (overlap batch 3). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawOverlapCrossLE_313 :
    (RawFraction.add (rawPrimeLoad 313) (rawTailOverlap 313)).CrossLE
      (rawCapacity 313) := by decide
@[simp] theorem rawOverlapCrossLE_317 :
    (RawFraction.add (rawPrimeLoad 317) (rawTailOverlap 317)).CrossLE
      (rawCapacity 317) := by decide
@[simp] theorem rawOverlapCrossLE_331 :
    (RawFraction.add (rawPrimeLoad 331) (rawTailOverlap 331)).CrossLE
      (rawCapacity 331) := by decide
@[simp] theorem rawOverlapCrossLE_337 :
    (RawFraction.add (rawPrimeLoad 337) (rawTailOverlap 337)).CrossLE
      (rawCapacity 337) := by decide
@[simp] theorem rawOverlapCrossLE_347 :
    (RawFraction.add (rawPrimeLoad 347) (rawTailOverlap 347)).CrossLE
      (rawCapacity 347) := by decide
@[simp] theorem rawOverlapCrossLE_349 :
    (RawFraction.add (rawPrimeLoad 349) (rawTailOverlap 349)).CrossLE
      (rawCapacity 349) := by decide
@[simp] theorem rawOverlapCrossLE_353 :
    (RawFraction.add (rawPrimeLoad 353) (rawTailOverlap 353)).CrossLE
      (rawCapacity 353) := by decide
@[simp] theorem rawOverlapCrossLE_359 :
    (RawFraction.add (rawPrimeLoad 359) (rawTailOverlap 359)).CrossLE
      (rawCapacity 359) := by decide
@[simp] theorem rawOverlapCrossLE_367 :
    (RawFraction.add (rawPrimeLoad 367) (rawTailOverlap 367)).CrossLE
      (rawCapacity 367) := by decide

end Erdos390.WholePaper
