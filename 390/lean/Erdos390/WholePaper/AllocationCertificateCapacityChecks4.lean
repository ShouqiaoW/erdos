import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (capacity batch 4). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_283 :
    (rawPrimeLoad 283).CrossLE (rawCapacity 283) := by decide
@[simp] theorem rawCapacityCrossLE_293 :
    (rawPrimeLoad 293).CrossLE (rawCapacity 293) := by decide
@[simp] theorem rawCapacityCrossLE_307 :
    (rawPrimeLoad 307).CrossLE (rawCapacity 307) := by decide
@[simp] theorem rawCapacityCrossLE_311 :
    (rawPrimeLoad 311).CrossLE (rawCapacity 311) := by decide
@[simp] theorem rawCapacityCrossLE_313 :
    (rawPrimeLoad 313).CrossLE (rawCapacity 313) := by decide
@[simp] theorem rawCapacityCrossLE_317 :
    (rawPrimeLoad 317).CrossLE (rawCapacity 317) := by decide
@[simp] theorem rawCapacityCrossLE_331 :
    (rawPrimeLoad 331).CrossLE (rawCapacity 331) := by decide
@[simp] theorem rawCapacityCrossLE_337 :
    (rawPrimeLoad 337).CrossLE (rawCapacity 337) := by decide
@[simp] theorem rawCapacityCrossLE_347 :
    (rawPrimeLoad 347).CrossLE (rawCapacity 347) := by decide
@[simp] theorem rawCapacityCrossLE_349 :
    (rawPrimeLoad 349).CrossLE (rawCapacity 349) := by decide
@[simp] theorem rawCapacityCrossLE_353 :
    (rawPrimeLoad 353).CrossLE (rawCapacity 353) := by decide
@[simp] theorem rawCapacityCrossLE_359 :
    (rawPrimeLoad 359).CrossLE (rawCapacity 359) := by decide
@[simp] theorem rawCapacityCrossLE_367 :
    (rawPrimeLoad 367).CrossLE (rawCapacity 367) := by decide
@[simp] theorem rawCapacityCrossLE_373 :
    (rawPrimeLoad 373).CrossLE (rawCapacity 373) := by decide
@[simp] theorem rawCapacityCrossLE_379 :
    (rawPrimeLoad 379).CrossLE (rawCapacity 379) := by decide
@[simp] theorem rawCapacityCrossLE_383 :
    (rawPrimeLoad 383).CrossLE (rawCapacity 383) := by decide
@[simp] theorem rawCapacityCrossLE_389 :
    (rawPrimeLoad 389).CrossLE (rawCapacity 389) := by decide
@[simp] theorem rawCapacityCrossLE_397 :
    (rawPrimeLoad 397).CrossLE (rawCapacity 397) := by decide
@[simp] theorem rawCapacityCrossLE_401 :
    (rawPrimeLoad 401).CrossLE (rawCapacity 401) := by decide

end Erdos390.WholePaper
