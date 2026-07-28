import Erdos390.WholePaper.AllocationCertificateChecker

/-!
# Bounded structural checks for the finite allocation certificate

Every decision here sees at most one twenty-row block, except for the three
linear whole-array audits (length, validity, and primality).
-/

namespace Erdos390.WholePaper

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

def allocationKeyLabeled (key : AllocationEntry → ℕ)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  buckets.Forall fun bucket =>
    bucket.2.Forall fun e => key e = bucket.1

def allocationInnerOutputNodup {β : Type*}
    (output : AllocationEntry → β)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  buckets.Forall fun bucket => (bucket.2.map output).Nodup

theorem finiteAllocationEntries_length :
    finiteAllocationEntries.length = 211 := by
  decide

theorem allocationRowBlockFlat {b : ℕ} (hb : b ≤ 9) :
    finiteAllocationRowBlockEntries b =
      (finiteAllocationRowBlockBuckets b).flatMap fun bucket => bucket.2 := by
  interval_cases b <;> decide

theorem allocationPrimeBlockPerm {b : ℕ} (hb : b ≤ 9) :
    (finiteAllocationRowBlockEntries b).Perm
      ((finiteAllocationPrimeBlockBuckets b).flatMap fun bucket => bucket.2) := by
  interval_cases b <;> decide

theorem allocationRowLabels {b : ℕ} (hb : b ≤ 9) :
    allocationKeyLabeled (fun e => e.row)
      (finiteAllocationRowBlockBuckets b) := by
  unfold allocationKeyLabeled
  interval_cases b <;> decide

theorem allocationPrimeLabels {b : ℕ} (hb : b ≤ 9) :
    allocationKeyLabeled (fun e => e.cofactor)
      (finiteAllocationPrimeBlockBuckets b) := by
  unfold allocationKeyLabeled
  interval_cases b <;> decide

theorem allocationRowCoordinateInnerNodup {b : ℕ} (hb : b ≤ 9) :
    allocationInnerOutputNodup coordinate
      (finiteAllocationRowBlockBuckets b) := by
  unfold allocationInnerOutputNodup finiteAllocationRowBlockBuckets
  interval_cases b <;> decide

private def allocationValidityCheck : Bool :=
  finiteAllocationEntries.all fun e => decide e.Valid

private theorem allocationValidityCheck_eq_true :
    allocationValidityCheck = true := by
  decide

theorem finiteAllocationEntries_valid {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntries) : e.Valid := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp allocationValidityCheck_eq_true) e he)

private def allocationCofactorPrimeCheck : Bool :=
  finiteAllocationEntries.all fun e => decide e.cofactor.Prime

private theorem allocationCofactorPrimeCheck_eq_true :
    allocationCofactorPrimeCheck = true := by
  decide

theorem finiteAllocationEntries_cofactor_prime {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntries) : e.cofactor.Prime := by
  exact of_decide_eq_true
    ((List.all_eq_true.mp allocationCofactorPrimeCheck_eq_true) e he)

end Erdos390.WholePaper
