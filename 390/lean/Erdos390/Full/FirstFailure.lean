import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A compact first-failure principle

This isolates the order/topology step used in the Dickman log-slope
continuation argument.  It prevents the phrase "take the first failure
point" from hiding a compactness argument.
-/

open Set

namespace Erdos390.Full.FirstFailure

/-- If a continuous real function is positive at every point provided it
was positive at every strictly earlier point of a compact interval, then it
is positive throughout that interval. -/
theorem positiveOn_Icc_of_positive_at_first_failure
    (g : ℝ → ℝ) {a b : ℝ} (hg : ContinuousOn g (Icc a b))
    (hstep : ∀ x ∈ Icc a b,
      (∀ y ∈ Icc a x, y < x → 0 < g y) → 0 < g x) :
    ∀ x ∈ Icc a b, 0 < g x := by
  let bad : Set ℝ := Icc a b ∩ {x | g x ≤ 0}
  have hbadCompact : IsCompact bad := by
    have hbadClosed : IsClosed bad := by
      dsimp only [bad]
      exact isClosed_Icc.isClosed_le hg continuousOn_const
    exact isCompact_Icc.of_isClosed_subset hbadClosed (fun _ hx ↦ hx.1)
  by_contra hfail
  push_neg at hfail
  obtain ⟨x₀, hx₀Icc, hx₀bad⟩ := hfail
  have hbadNonempty : bad.Nonempty := ⟨x₀, hx₀Icc, hx₀bad⟩
  obtain ⟨x, hxBad, hxMin⟩ :=
    hbadCompact.exists_isMinOn hbadNonempty continuousOn_id
  have hprev : ∀ y ∈ Icc a x, y < x → 0 < g y := by
    intro y hyIcc hyx
    by_contra hyNot
    have hyNonpos : g y ≤ 0 := le_of_not_gt hyNot
    have hyFull : y ∈ Icc a b := by
      exact ⟨hyIcc.1, hyIcc.2.trans hxBad.1.2⟩
    have hyBad : y ∈ bad := ⟨hyFull, hyNonpos⟩
    have hxy : x ≤ y := hxMin hyBad
    exact (not_lt_of_ge hxy) hyx
  have hxPos := hstep x hxBad.1 hprev
  exact (not_lt_of_ge hxBad.2) hxPos

end Erdos390.Full.FirstFailure
