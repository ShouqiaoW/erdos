import Erdos390.WholePaper.BankBottomMarkerPools

/-! # Expanded literal statement audit for the four bottom marker pools -/

namespace Erdos390.WholePaper

noncomputable section

example (n M : ℕ) :
    bankBottomMarkerInterval n M .fiveToFour = Finset.Ioc (n / 3) (M / 6) ∧
      bankBottomMarkerInterval n M .fourToThree =
        Finset.Ioc (2 * n / 5) (M / 5) ∧
      bankBottomMarkerInterval n M .threeToTwo =
        Finset.Ioc (2 * n / 3) (M / 3) ∧
      bankBottomMarkerInterval n M .twoToOne = Finset.Ioc (n / 2) (M / 4) := by
  simp [bankBottomMarkerInterval, bankBottomMarkerLower,
    bankBottomMarkerUpper]

example {n M marker : ℕ}
    (hmarker : marker ∈ Finset.Ioc (n / 3) (M / 6)) :
    4 * marker ∈ Finset.Ioc n M ∧
      5 * marker ∈ Finset.Ioc n M ∧
      6 * marker ∈ Finset.Ioc n M := by
  simpa only [bankBottomMarkerInterval, bankBottomMarkerLower,
    bankBottomMarkerUpper, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier, factorInterval] using
      bankBottom_states_donor_mem_factorInterval
        (move := BankBottomMove.fiveToFour) hmarker

example {n M marker : ℕ}
    (hmarker : marker ∈ Finset.Ioc (2 * n / 5) (M / 5)) :
    3 * marker ∈ Finset.Ioc n M ∧
      4 * marker ∈ Finset.Ioc n M ∧
      5 * marker ∈ Finset.Ioc n M := by
  simpa only [bankBottomMarkerInterval, bankBottomMarkerLower,
    bankBottomMarkerUpper, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier, factorInterval] using
      bankBottom_states_donor_mem_factorInterval
        (move := BankBottomMove.fourToThree) hmarker

example {n M marker : ℕ}
    (hmarker : marker ∈ Finset.Ioc (2 * n / 3) (M / 3)) :
    2 * marker ∈ Finset.Ioc n M ∧
      3 * marker ∈ Finset.Ioc n M ∧
      3 * marker ∈ Finset.Ioc n M := by
  simpa only [bankBottomMarkerInterval, bankBottomMarkerLower,
    bankBottomMarkerUpper, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier, factorInterval] using
      bankBottom_states_donor_mem_factorInterval
        (move := BankBottomMove.threeToTwo) hmarker

example {n M marker : ℕ}
    (hmarker : marker ∈ Finset.Ioc (n / 2) (M / 4)) :
    2 * marker ∈ Finset.Ioc n M ∧
      4 * marker ∈ Finset.Ioc n M ∧
      4 * marker ∈ Finset.Ioc n M := by
  simpa only [bankBottomMarkerInterval, bankBottomMarkerLower,
    bankBottomMarkerUpper, bankBottomLowerState,
    bankBottomUpperState, bankBottomDonor,
    bankBottomLowerStateMultiplier, bankBottomUpperStateMultiplier,
    bankBottomDonorMultiplier, factorInterval] using
      bankBottom_states_donor_mem_factorInterval
        (move := BankBottomMove.twoToOne) hmarker

example (marker : ℕ) :
    bankBottomDonor .threeToTwo marker =
        bankBottomUpperState .threeToTwo marker ∧
      bankBottomDonor .twoToOne marker =
        bankBottomUpperState .twoToOne marker := by
  simp

example {n M : ℕ} (hTwoN : 2 * n ≤ M) (hM : 5 * M ≤ 12 * n) :
    ∀ {pool pool' : BankBottomOrientationPool}, pool ≠ pool' →
      Disjoint (bankBottomOrientedMarkerInterval n M pool)
        (bankBottomOrientedMarkerInterval n M pool') := by
  intro pool pool' hpools
  exact bankBottomOrientedMarkerIntervals_disjoint hTwoN hM hpools

example {n M : ℕ} (hTwoN : 2 * n ≤ M) (move : BankBottomMove) :
    Disjoint
        (Finset.Ioc (bankBottomMarkerLower n move)
          (bankBottomOrientationCut n M move))
        (Finset.Ioc (bankBottomOrientationCut n M move)
          (bankBottomMarkerUpper M move)) ∧
      Finset.Ioc (bankBottomMarkerLower n move)
          (bankBottomOrientationCut n M move) ∪
        Finset.Ioc (bankBottomOrientationCut n M move)
          (bankBottomMarkerUpper M move) =
        Finset.Ioc (bankBottomMarkerLower n move)
          (bankBottomMarkerUpper M move) := by
  exact ⟨by simpa only [bankBottomOrientedMarkerInterval] using
      bankBottomOrientationIntervals_disjoint n M move,
    by simpa only [bankBottomOrientedMarkerInterval,
      bankBottomMarkerInterval] using
        bankBottomOrientationIntervals_union hTwoN move⟩

end

end Erdos390.WholePaper
