import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightLedger

/-! # Statement audit for the exact Section 8 smooth quota/height ledger -/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

example (mFrozen qTilde : Real) :
    |bankPaperCanonicalSmoothInitialActiveMass mFrozen qTilde - qTilde| <=
      1 / 2 :=
  bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
    mFrozen qTilde

example (n : Nat) (mu q0 A0 : Real) :
    |(bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) -
        bankPaperCanonicalSmoothHeightCenter n mu q0 A0| <= 1 / 2 :=
  bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le n mu q0 A0

example (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) :
    bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde n =
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde n :=
  bankPaperCanonicalSmoothFinalActiveMassFamily_eq_q0_sub_d
    mu logY Lambda0 mFrozen qTilde n

/-! ## Complete public declaration census -/

#check bankPaperCanonicalRawSmoothBasePool
#check bankPaperCanonicalRawSmoothBaseWeight
#check bankPaperCanonicalRawSmoothBaseMass
#check bankPaperCanonicalRawSmoothBaseWeight_eq_roughRawWeight
#check sum_bankPaperCanonicalRawSmoothBaseWeight
#check isCompleteRoughLabel_one
#check bankPaperCanonicalRawSmoothBasePool_card_eq_headFreeSmoothInterval
#check bankPaperCanonicalRawSmoothBaseMass_eq_headFreeSmoothInterval
#check bankPaperNearestIntegerTieLower
#check bankPaperNearestIntegerTieLower_eq_iff
#check bankPaperNearestIntegerTieLower_intCast
#check bankPaperNearestIntegerTieLower_add_half
#check bankPaperNearestIntegerTieLower_abs_sub_le
#check bankPaperCanonicalSmoothInitialQuota
#check bankPaperCanonicalSmoothInitialActiveMass
#check bankPaperCanonicalSmoothInitialQuota_eq_of_total_eq_intCast
#check bankPaperCanonicalSmoothInitialActiveMass_sub_actual
#check bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le
#check bankPaperCanonicalSmoothQuotaAt
#check bankPaperCanonicalSmoothActiveMassAt
#check bankPaperCanonicalSmoothActiveMassAt_eq_q0_sub
#check bankPaperCanonicalSmoothQuotaAt_cast_eq_frozen_add_active
#check bankPaperCanonicalSmoothOtherFrozenMass
#check bankPaperCanonicalSmoothFlexibleQuotaAt
#check bankPaperCanonicalSmoothQuotaAt_exact_ledger
#check bankPaperCanonicalSmoothFlexibleQuotaAt_exact_ledger
#check bankPaperCanonicalSmoothFrozenHeightDefect
#check bankPaperCanonicalSmoothActiveHeightAt
#check bankPaperCanonicalSmoothActiveHeightAt_eq_defect_add
#check bankPaperCanonicalSmoothHeightCenter
#check bankPaperCanonicalSmoothHeightAdjustment
#check bankPaperCanonicalSmoothHeightAdjustment_abs_sub_center_le
#check bankPaperCanonicalSmoothHeightAdjustedActiveMass
#check bankPaperCanonicalSmoothHeightAdjustedActiveMass_eq_q0_sub_d
#check bankPaperCanonicalSmoothHeightCenter_exact_residual
#check bankPaperCanonicalSmoothHeightAdjustment_centered_residual_bound
#check bankPaperCanonicalSmoothHeightCenter_exact_mean_error
#check bankPaperCanonicalSmoothHeightAdjustment_mean_error_bound
#check bankPaperCanonicalSmoothActiveHeight_centered_residual
#check bankPaperCanonicalSmoothQ0Family
#check bankPaperCanonicalSmoothA0Family
#check bankPaperCanonicalSmoothDStarFamily
#check bankPaperCanonicalSmoothDIntFamily
#check bankPaperCanonicalSmoothDRealFamily
#check bankPaperCanonicalSmoothFinalActiveMassFamily
#check bankPaperCanonicalSmoothFinalActiveHeightFamily
#check bankPaperCanonicalSmoothPhysicalMeanErrorFamily
#check bankPaperCanonicalSmoothFinalActiveMassFamily_eq_q0_sub_d
#check bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
#check bankPaperCanonicalSmoothDRealFamily_abs_sub_dStar_le
#check bankPaperCanonicalSmoothPhysicalMeanErrorFamily_bound

end

end Erdos390.WholePaper
