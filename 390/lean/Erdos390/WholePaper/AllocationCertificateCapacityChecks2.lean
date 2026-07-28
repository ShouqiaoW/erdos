import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (capacity batch 2). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_73 :
    (rawPrimeLoad 73).CrossLE (rawCapacity 73) := by decide
@[simp] theorem rawCapacityCrossLE_79 :
    (rawPrimeLoad 79).CrossLE (rawCapacity 79) := by decide
@[simp] theorem rawCapacityCrossLE_83 :
    (rawPrimeLoad 83).CrossLE (rawCapacity 83) := by decide
@[simp] theorem rawCapacityCrossLE_89 :
    (rawPrimeLoad 89).CrossLE (rawCapacity 89) := by decide
@[simp] theorem rawCapacityCrossLE_97 :
    (rawPrimeLoad 97).CrossLE (rawCapacity 97) := by decide
@[simp] theorem rawCapacityCrossLE_101 :
    (rawPrimeLoad 101).CrossLE (rawCapacity 101) := by decide
@[simp] theorem rawCapacityCrossLE_103 :
    (rawPrimeLoad 103).CrossLE (rawCapacity 103) := by decide
@[simp] theorem rawCapacityCrossLE_107 :
    (rawPrimeLoad 107).CrossLE (rawCapacity 107) := by decide
@[simp] theorem rawCapacityCrossLE_109 :
    (rawPrimeLoad 109).CrossLE (rawCapacity 109) := by decide
@[simp] theorem rawCapacityCrossLE_113 :
    (rawPrimeLoad 113).CrossLE (rawCapacity 113) := by decide
@[simp] theorem rawCapacityCrossLE_127 :
    (rawPrimeLoad 127).CrossLE (rawCapacity 127) := by decide
@[simp] theorem rawCapacityCrossLE_131 :
    (rawPrimeLoad 131).CrossLE (rawCapacity 131) := by decide
@[simp] theorem rawCapacityCrossLE_137 :
    (rawPrimeLoad 137).CrossLE (rawCapacity 137) := by decide
@[simp] theorem rawCapacityCrossLE_139 :
    (rawPrimeLoad 139).CrossLE (rawCapacity 139) := by decide
@[simp] theorem rawCapacityCrossLE_149 :
    (rawPrimeLoad 149).CrossLE (rawCapacity 149) := by decide
@[simp] theorem rawCapacityCrossLE_151 :
    (rawPrimeLoad 151).CrossLE (rawCapacity 151) := by decide
@[simp] theorem rawCapacityCrossLE_157 :
    (rawPrimeLoad 157).CrossLE (rawCapacity 157) := by decide
@[simp] theorem rawCapacityCrossLE_163 :
    (rawPrimeLoad 163).CrossLE (rawCapacity 163) := by decide
@[simp] theorem rawCapacityCrossLE_167 :
    (rawPrimeLoad 167).CrossLE (rawCapacity 167) := by decide
@[simp] theorem rawCapacityCrossLE_173 :
    (rawPrimeLoad 173).CrossLE (rawCapacity 173) := by decide

end Erdos390.WholePaper
