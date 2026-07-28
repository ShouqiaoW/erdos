import Erdos390.WholePaper.BankPaperCanonicalRoughRowCorrection

/-! # Expanded statement audit for finite canonical row correction -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

#check bankPaperConstantPoolCorrectionDensity
#check bankPaperConstantPoolCorrection

example
    (row pool : Finset ℕ) (x : ℕ → ℝ) (target : ℝ) (a : ℕ) :
    bankPaperConstantPoolCorrection row pool x target a =
      x a + if a ∈ pool then
        (target - ∑ b ∈ row, x b) / (pool.card : ℝ)
      else 0 := by
  rfl

#check bankPaperConstantPoolCorrection_apply_of_mem
#check bankPaperConstantPoolCorrection_apply_of_not_mem
#check sum_bankPaperConstantPoolCorrection_eq_target

example
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target : ℝ}
    (hpool : pool ⊆ row) (hpoolNonempty : pool.Nonempty) :
    ∑ a ∈ row, bankPaperConstantPoolCorrection row pool x target a =
      target :=
  sum_bankPaperConstantPoolCorrection_eq_target hpool hpoolNonempty

#check bankPaperConstantPoolCorrection_mem_unitInterval
#check bankPaperConstantPoolCorrection_mem_unitInterval_of_abs_density_le

example
    {row pool : Finset ℕ} {x : ℕ → ℝ} {target margin : ℝ}
    (hx : ∀ a ∈ row, 0 ≤ x a ∧ x a ≤ 1)
    (hmargin : ∀ a ∈ pool,
      margin ≤ x a ∧ x a ≤ 1 - margin)
    (hdensity :
      |bankPaperConstantPoolCorrectionDensity row pool x target| ≤ margin)
    {a : ℕ} (ha : a ∈ row) :
    0 ≤ bankPaperConstantPoolCorrection row pool x target a ∧
      bankPaperConstantPoolCorrection row pool x target a ≤ 1 :=
  bankPaperConstantPoolCorrection_mem_unitInterval_of_abs_density_le
    hx hmargin hdensity ha

#check roughCanonicalBroadCorrectionPool
#check roughCanonicalBroadCorrectionPool_subset_rawRow
#check roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
#check roughCanonicalRawRowCorrectedWeight
#check roughCanonicalRawRowCorrectionDensity_eq_quotaError_div
#check sum_roughCanonicalRawRowCorrectedWeight_eq_upperTarget

example
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K)) :
    bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) =
      roughCanonicalRawRowQuotaError W n h K y alpha beta L row /
        ((roughCanonicalBroadCorrectionPool W n h K y row.1).card : ℝ) :=
  roughCanonicalRawRowCorrectionDensity_eq_quotaError_div
    W n h K y alpha beta L row

example
    (W n h K y : ℕ) (alpha beta L : ℝ)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hpool :
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty) :
    ∑ a ∈ completeRoughRowFiber y
        (roughRawCandidateSet n h K) row.1,
      roughCanonicalRawRowCorrectedWeight
        W n h K y row.1 alpha beta L a =
      (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) :=
  sum_roughCanonicalRawRowCorrectedWeight_eq_upperTarget
    W n h K y alpha beta L row hpool

#check roughCanonicalRawRowCorrectedWeight_mem_unitInterval
#check roughCanonicalRawRowCorrection_exact_and_feasible
#check roughCanonicalRawCorrectedSelector
#check roughCanonicalRawCorrectedSelector_eq_rowCorrected_of_mem
#check sum_roughCanonicalRawCorrectedSelector_eq_upperTarget
#check roughCanonicalRawCorrectedSelector_mem_unitInterval
#check roughCanonicalRawCorrectedSelector_rowSums_integer
#check roughCanonicalRawCorrectedSelector_finiteState

example
    {W n h K y : ℕ} {alpha beta L margin : ℝ}
    (hpools : ∀ row : CanonicalCompleteRoughRow y
        (roughRawCandidateSet n h K),
      (roughCanonicalBroadCorrectionPool W n h K y row.1).Nonempty)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbeta : 0 ≤ beta / L ∧ beta / L ≤ 1)
    (hmarginLower : margin ≤ beta / L)
    (hmarginUpper : margin ≤ 1 - beta / L)
    (hdensity : ∀ row : CanonicalCompleteRoughRow y
        (roughRawCandidateSet n h K),
      |bankPaperConstantPoolCorrectionDensity
        (completeRoughRowFiber y (roughRawCandidateSet n h K) row.1)
        (roughCanonicalBroadCorrectionPool W n h K y row.1)
        (roughHeadCompatibleRawWeight W n h K alpha beta L)
        (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ)| ≤ margin) :
    (∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ roughCanonicalRawCorrectedSelector
          W n h K y alpha beta L a ∧
        roughCanonicalRawCorrectedSelector
          W n h K y alpha beta L a ≤ 1) ∧
      (∀ label ∈ completeRoughLabelSet y
          (roughRawCandidateSet n h K),
        ∃ k : ℤ,
          ∑ a ∈ completeRoughRowFiber y
              (roughRawCandidateSet n h K) label,
            roughCanonicalRawCorrectedSelector
              W n h K y alpha beta L a = (k : ℝ)) ∧
      ∀ row : CanonicalCompleteRoughRow y
          (roughRawCandidateSet n h K),
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1,
          roughCanonicalRawCorrectedSelector
            W n h K y alpha beta L a =
          (roughUpperCompleteRoughRowTarget n h y row.1 : ℝ) :=
  roughCanonicalRawCorrectedSelector_finiteState hpools halpha hbeta
    hmarginLower hmarginUpper hdensity

#check roughCanonicalCappedUpperQuota
#check roughCanonicalCappedUpperQuotaSelector
#check roughCanonicalCappedUpperQuotaSelector_apply_of_mem
#check roughCanonicalCappedUpperQuotaSelector_apply_of_not_mem
#check roughCanonicalCappedUpperQuotaSelector_mem_unitInterval
#check sum_roughCanonicalCappedUpperQuotaSelector_eq_cappedQuota
#check roughCanonicalCappedUpperQuotaSelector_rowSums_integer
#check roughCanonicalCappedUpperQuota_eq_upperTarget_of_capacity
#check sum_roughCanonicalCappedUpperQuotaSelector_eq_upperTarget_of_capacity
#check roughCanonicalCappedUpperQuotaSelector_finiteState

example (n h K y : ℕ) :
    (∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ roughCanonicalCappedUpperQuotaSelector n h K y a ∧
        roughCanonicalCappedUpperQuotaSelector n h K y a ≤ 1) ∧
      (∀ label ∈ completeRoughLabelSet y
          (roughRawCandidateSet n h K),
        ∃ k : ℤ,
          ∑ a ∈ completeRoughRowFiber y
              (roughRawCandidateSet n h K) label,
            roughCanonicalCappedUpperQuotaSelector n h K y a = (k : ℝ)) ∧
      ∀ row : CanonicalCompleteRoughRow y
          (roughRawCandidateSet n h K),
        ∑ a ∈ completeRoughRowFiber y
            (roughRawCandidateSet n h K) row.1,
          roughCanonicalCappedUpperQuotaSelector n h K y a =
          ((min (roughUpperCompleteRoughRowTarget n h y row.1)
            (completeRoughRowFiber y
              (roughRawCandidateSet n h K) row.1).card : ℕ) : ℝ) :=
  roughCanonicalCappedUpperQuotaSelector_finiteState n h K y

end

end Erdos390.WholePaper
