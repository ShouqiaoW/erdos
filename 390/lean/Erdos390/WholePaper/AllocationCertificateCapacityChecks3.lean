import Erdos390.WholePaper.AllocationCertificateChecker

/-! Bounded kernel checks for the finite allocation certificate (capacity batch 3). -/

namespace Erdos390.WholePaper

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

@[simp] theorem rawCapacityCrossLE_179 :
    (rawPrimeLoad 179).CrossLE (rawCapacity 179) := by decide
@[simp] theorem rawCapacityCrossLE_181 :
    (rawPrimeLoad 181).CrossLE (rawCapacity 181) := by decide
@[simp] theorem rawCapacityCrossLE_191 :
    (rawPrimeLoad 191).CrossLE (rawCapacity 191) := by decide
@[simp] theorem rawCapacityCrossLE_193 :
    (rawPrimeLoad 193).CrossLE (rawCapacity 193) := by decide
@[simp] theorem rawCapacityCrossLE_197 :
    (rawPrimeLoad 197).CrossLE (rawCapacity 197) := by decide
@[simp] theorem rawCapacityCrossLE_199 :
    (rawPrimeLoad 199).CrossLE (rawCapacity 199) := by decide
@[simp] theorem rawCapacityCrossLE_211 :
    (rawPrimeLoad 211).CrossLE (rawCapacity 211) := by decide
@[simp] theorem rawCapacityCrossLE_223 :
    (rawPrimeLoad 223).CrossLE (rawCapacity 223) := by decide
@[simp] theorem rawCapacityCrossLE_227 :
    (rawPrimeLoad 227).CrossLE (rawCapacity 227) := by decide
@[simp] theorem rawCapacityCrossLE_229 :
    (rawPrimeLoad 229).CrossLE (rawCapacity 229) := by decide
@[simp] theorem rawCapacityCrossLE_233 :
    (rawPrimeLoad 233).CrossLE (rawCapacity 233) := by decide
@[simp] theorem rawCapacityCrossLE_239 :
    (rawPrimeLoad 239).CrossLE (rawCapacity 239) := by decide
@[simp] theorem rawCapacityCrossLE_241 :
    (rawPrimeLoad 241).CrossLE (rawCapacity 241) := by decide
@[simp] theorem rawCapacityCrossLE_251 :
    (rawPrimeLoad 251).CrossLE (rawCapacity 251) := by decide
@[simp] theorem rawCapacityCrossLE_257 :
    (rawPrimeLoad 257).CrossLE (rawCapacity 257) := by decide
@[simp] theorem rawCapacityCrossLE_263 :
    (rawPrimeLoad 263).CrossLE (rawCapacity 263) := by decide
@[simp] theorem rawCapacityCrossLE_269 :
    (rawPrimeLoad 269).CrossLE (rawCapacity 269) := by decide
@[simp] theorem rawCapacityCrossLE_271 :
    (rawPrimeLoad 271).CrossLE (rawCapacity 271) := by decide
@[simp] theorem rawCapacityCrossLE_277 :
    (rawPrimeLoad 277).CrossLE (rawCapacity 277) := by decide
@[simp] theorem rawCapacityCrossLE_281 :
    (rawPrimeLoad 281).CrossLE (rawCapacity 281) := by decide

end Erdos390.WholePaper
