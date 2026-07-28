import Erdos390.WholePaper.BankPaperFourFiveMovingFaceBV

/-! Expanded statement audit for moving-face BV and compact mass. -/

open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperRealization

#check fourFiveCutoffSequence
#check fourFiveRightDiscreteBVNorm_congr
#check fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
#check fourFiveLogCoordinate
#check fourFiveMovingFaceKernel
#check fourFiveMovingFaceCutoff
#check fourFiveMovingFaceMonotoneExtension
#check fourFiveLogCoordinate_mono
#check fourFiveMovingFace_active_iff_le_cutoff
#check fourFiveMovingFaceKernel_eq_cutoffSequence
#check fourFiveMovingFaceMonotoneExtension_certificate
#check fourFiveRightDiscreteBVNorm_movingFace_le_two
#check fourFiveCompactReciprocalMass
#check fourFiveCompactReciprocalMass_pos
#check fourFiveAnchoredReciprocalPrimeAtom_nonneg
#check fourFiveAnchoredLogLogCellAtom_nonneg
#check sum_Ioc_fourFiveAnchoredReciprocalPrimeAtom
#check sum_Ioc_fourFiveAnchoredLogLogCellAtom
#check sum_abs_fourFiveAnchoredReciprocalPrimeAtom
#check sum_abs_fourFiveAnchoredLogLogCellAtom
#check fourFive_actual_and_continuum_mass_le_compact
#check fourFiveMovingSimplexKernelOne
#check fourFiveMovingSimplexKernelTwo
#check fourFiveMovingSimplexKernelThree
#check fourFiveMovingSimplexKernelTwo_eq_face_first
#check fourFiveMovingSimplexKernelTwo_eq_face_second
#check fourFiveRightDiscreteBVNorm_movingSimplexTwo_first_le_two
#check fourFiveRightDiscreteBVNorm_movingSimplexTwo_second_le_two
#check fourFiveMovingSimplexKernelThree_eq_face_first
#check fourFiveMovingSimplexKernelThree_eq_face_second
#check fourFiveMovingSimplexKernelThree_eq_face_third
#check fourFiveRightDiscreteBVNorm_movingSimplexThree_first_le_two
#check fourFiveRightDiscreteBVNorm_movingSimplexThree_second_le_two
#check fourFiveRightDiscreteBVNorm_movingSimplexThree_third_le_two
#check abs_fourFiveMovingSimplexProductOne_sub_continuum_le
#check abs_fourFiveMovingSimplexProductTwo_sub_continuum_le
#check abs_fourFiveMovingSimplexProductThree_sub_continuum_le

example {A Y y : Nat} {u c : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) :
    fourFiveRightDiscreteBVNorm
        (fourFiveMovingFaceKernel A y u c) A Y <= 2 :=
  fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY

end Erdos390.WholePaper.BankPaperRealization
