import Erdos390.WholePaper.BankOrdinaryConcreteDemand

/-! # Expanded statement audit for concrete ordinary requests -/

open Filter

namespace Erdos390.WholePaper

noncomputable section

example (n : ℕ) :
    bankOrdinaryPaperRequests n =
      (Finset.univ : Finset (BankOrdinaryPaperRequest n)) := rfl

example {n : ℕ} (request : BankOrdinaryPaperRequest n) :
    IsBankOrdinaryCoreComponent
      (bankOrdinaryPaperRequestSource request)
      (bankOrdinaryPaperRequestTarget request) :=
  bankOrdinaryPaperRequest_component_spec request

example {n : ℕ} (request : BankOrdinaryPaperRequest n) :
    bankOrdinaryScale (bankOrdinaryPaperRequestPool n request).1 ≤
      (Erdos390.Full.ArithmeticModel.yNat n : ℚ) :=
  bankOrdinaryPaperRequest_scale_le_yNat request

example (n : ℕ) (pool : BankOrdinaryOrientationPool) :
    bankOrdinaryPoolDemand n pool =
      ∑ p ∈ bankRoundingPrimeSupport n,
        bankRoundingBeta n p *
          (bankOrdinaryCoreSourcesAtScale p pool.1).card :=
  bankOrdinaryPoolDemand_eq n pool

example (n : ℕ) (pool : BankOrdinaryOrientationPool) (hj : pool.1 ≤ 5) :
    bankOrdinaryPoolDemand n pool ≤ 17 * bankBottomPaperDemand n :=
  bankOrdinaryPoolDemand_le_seventeen_beta n pool hj

example (n : ℕ) (pool : BankOrdinaryOrientationPool) (hj : 6 ≤ pool.1) :
    bankOrdinaryPoolDemand n pool ≤ 2 * bankBottomPaperDemand n :=
  bankOrdinaryPoolDemand_le_two_beta n pool hj

example (n : ℕ) (orientation : BankBottomOrientation) :
    bankOrdinaryPoolDemand n (0, orientation) = 0 :=
  bankOrdinaryPoolDemand_scale_zero n orientation

example {n : ℕ} {pool : BankOrdinaryOrientationPool}
    (hscale : (Erdos390.Full.ArithmeticModel.yNat n : ℚ) <
      bankOrdinaryScale pool.1) :
    bankOrdinaryPoolDemand n pool = 0 :=
  bankOrdinaryPoolDemand_zero_of_scale_gt_yNat hscale

example (n : ℕ) :
    bankOrdinaryWorstMarkerScale n =
      secondOrderScale n /
        max 1 (Erdos390.Full.ArithmeticModel.yNat n : ℝ) := rfl

example :
    Tendsto
      (fun n : ℕ ↦
        (Erdos390.Full.ArithmeticModel.yNat n : ℝ) /
          bankOrdinaryWorstMarkerScale n)
      atTop (nhds 0) :=
  yNat_div_bankOrdinaryWorstMarkerScale_tendsto_zero

example :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomPaperDemand n : ℝ) /
          (secondOrderScale n / max 1
            (Erdos390.Full.ArithmeticModel.yNat n : ℝ)))
      atTop (nhds 0) := by
  simpa only [bankOrdinaryWorstMarkerScale] using
    bankBottomPaperDemand_div_bankOrdinaryWorstMarkerScale_tendsto_zero

example :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =o[atTop]
      bankOrdinaryWorstMarkerScale :=
  bankBottomPaperDemand_isLittleO_bankOrdinaryWorstMarkerScale

example (pool : ℕ → BankOrdinaryOrientationPool)
    (hlarge : ∀ᶠ n : ℕ in atTop, 6 ≤ (pool n).1) :
    (fun n : ℕ ↦ (bankOrdinaryPoolDemand n (pool n) : ℝ))
      =o[atTop] bankOrdinaryWorstMarkerScale :=
  bankOrdinary_largeOrientationDemand_isLittleO pool hlarge

example (scale : SmallDescentScale) (orientation : BankBottomOrientation) :
    (fun n : ℕ ↦
      (bankOrdinaryPoolDemand n
        (smallDescentScaleIndex scale, orientation) : ℝ))
      =o[atTop] bankBottomPrimeScale :=
  bankOrdinary_smallOrientationDemand_isLittleO scale orientation

example :
    ∀ᶠ n : ℕ in atTop, ∀ Q : ℚ,
      Q ≤ (Erdos390.Full.ArithmeticModel.yNat n : ℚ) →
        max (Q : ℝ) (Real.log (n : ℝ)) ≤
          5 * max 1 (Erdos390.Full.ArithmeticModel.yNat n : ℝ) :=
  eventually_bankOrdinary_max_scale_log_le_five_yNat

end

end Erdos390.WholePaper
