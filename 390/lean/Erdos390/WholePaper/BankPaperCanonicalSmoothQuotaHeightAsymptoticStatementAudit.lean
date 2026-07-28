import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic

/-! # Statement audit for the analytic Section 8 quota/height bridge -/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.Scale

noncomputable section

example (W K : Nat) {c betaAct : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct) :=
  bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
    W K hc hbeta

example {mu : Real} (hmu : 0 < mu) (q0 A0 : Nat -> Real)
    (Hq0 : q0 =O[atTop] secondOrderScale)
    (HA0 : A0 =O[atTop] secondOrderScale) :
    (fun n => (bankPaperCanonicalSmoothHeightAdjustment
      n mu (q0 n) (A0 n) : Real)) =O[atTop]
        (fun n => secondOrderScale n / L n) :=
  bankPaperCanonicalSmoothHeightAdjustment_isBigO hmu q0 A0 Hq0 HA0

example (W K : Nat) {c betaAct mu : Real} (hc : 0 < c)
    (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde) :=
  bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
    W K hc hbeta hmu logY Lambda0 mFrozen qTilde Hledger

/-! ## Complete public declaration census -/

#check eventually_bankPaperCanonicalRawSmoothBasePool_linear_lower
#check bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
#check bankPaperCanonicalRawSmoothBaseMass_isBigO
#check BankPaperCanonicalSectionEightAnalyticLedger
#check bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
#check bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
#check bankPaperCanonicalSmoothQ0Family_paperScaleLower
#check bankPaperCanonicalPostGuardSmoothMass_isBigO
#check bankPaperCanonicalSmoothQ0Family_isBigO
#check secondOrderScale_div_L_tendsto_atTop
#check bankPaperCanonical_inv_L_add_mu_isBigO_inv_L
#check bankPaperCanonicalSmoothHeightAdjustment_isBigO
#check bankPaperCanonicalSectionEight_q0_paperScaleLower
#check bankPaperCanonicalSectionEight_d_isBigO
#check bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
#check bankPaperCanonicalSectionEight_physicalMeanError_isBigO
#check eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
#check bankPaperCanonicalSectionEight_headActiveMass_paperScaleLower
#check eventually_one_le_bankPaperCanonicalSectionEight_headActiveMass

end

end Erdos390.WholePaper
