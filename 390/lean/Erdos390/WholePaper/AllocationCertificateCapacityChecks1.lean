import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (capacity batch 1). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_2 :
    (rawPrimeLoad 2).CrossLE (rawCapacity 2) := by decide
@[simp] theorem rawCapacityCrossLE_3 :
    (rawPrimeLoad 3).CrossLE (rawCapacity 3) := by decide
@[simp] theorem rawCapacityCrossLE_5 :
    (rawPrimeLoad 5).CrossLE (rawCapacity 5) := by decide
@[simp] theorem rawCapacityCrossLE_7 :
    (rawPrimeLoad 7).CrossLE (rawCapacity 7) := by decide
@[simp] theorem rawCapacityCrossLE_11 :
    (rawPrimeLoad 11).CrossLE (rawCapacity 11) := by decide
@[simp] theorem rawCapacityCrossLE_13 :
    (rawPrimeLoad 13).CrossLE (rawCapacity 13) := by decide
@[simp] theorem rawCapacityCrossLE_17 :
    (rawPrimeLoad 17).CrossLE (rawCapacity 17) := by decide
@[simp] theorem rawCapacityCrossLE_19 :
    (rawPrimeLoad 19).CrossLE (rawCapacity 19) := by decide
@[simp] theorem rawCapacityCrossLE_23 :
    (rawPrimeLoad 23).CrossLE (rawCapacity 23) := by decide
@[simp] theorem rawCapacityCrossLE_29 :
    (rawPrimeLoad 29).CrossLE (rawCapacity 29) := by decide
@[simp] theorem rawCapacityCrossLE_31 :
    (rawPrimeLoad 31).CrossLE (rawCapacity 31) := by decide
@[simp] theorem rawCapacityCrossLE_37 :
    (rawPrimeLoad 37).CrossLE (rawCapacity 37) := by decide
@[simp] theorem rawCapacityCrossLE_41 :
    (rawPrimeLoad 41).CrossLE (rawCapacity 41) := by decide
@[simp] theorem rawCapacityCrossLE_43 :
    (rawPrimeLoad 43).CrossLE (rawCapacity 43) := by decide
@[simp] theorem rawCapacityCrossLE_47 :
    (rawPrimeLoad 47).CrossLE (rawCapacity 47) := by decide
@[simp] theorem rawCapacityCrossLE_53 :
    (rawPrimeLoad 53).CrossLE (rawCapacity 53) := by decide
@[simp] theorem rawCapacityCrossLE_59 :
    (rawPrimeLoad 59).CrossLE (rawCapacity 59) := by decide
@[simp] theorem rawCapacityCrossLE_61 :
    (rawPrimeLoad 61).CrossLE (rawCapacity 61) := by decide
@[simp] theorem rawCapacityCrossLE_67 :
    (rawPrimeLoad 67).CrossLE (rawCapacity 67) := by decide
@[simp] theorem rawCapacityCrossLE_71 :
    (rawPrimeLoad 71).CrossLE (rawCapacity 71) := by decide

end Erdos390.WholePaper
