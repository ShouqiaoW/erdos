import Erdos536.PrimeBandRootRankOneGeometry

/-!
# One-pivot insertion and the root small-ball event

This module isolates the exact one-mark insertion identity used in the
truncated rank-one part of the exposed-root estimate.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-- After inserting one marked support point, the two-dimensional root
small-ball event is exactly the pair of translated scalar inequalities
for the inserted normalized log-weight. -/
theorem supportMarkSmallBall_insert_iff
    {R : Finset ℕ} {T w : ℝ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A)
    (v : NineMark) (m : SupportNineMarking A) :
    SupportMarkSmallBall R T w (insert p A)
        ((supportMarkingInsertEquiv hpA).symm (v, m)) ↔
      |signedDigitReal v.1 * normalizedLogWeight T p.1 -
          (-supportMarkFirstNormalizedSum R T A m)| ≤ w ∧
      |signedDigitReal v.2 * normalizedLogWeight T p.1 -
          (-supportMarkSecondNormalizedSum R T A m)| ≤ w := by
  unfold SupportMarkSmallBall
  rw [supportMarkFirstNormalizedSum_insert,
    supportMarkSecondNormalizedSum_insert]
  simp only [sub_neg_eq_add]

/-- A nonzero inserted mark reduces the root small-ball event to one
translated interval of width `2 * w` for its normalized log-weight. -/
theorem supportMarkSmallBall_insert_forces_interval
    {R : Finset ℕ} {T w : ℝ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A)
    (v : NineMark) (hv : v ≠ zeroNineMark)
    (m : SupportNineMarking A)
    (hsmall :
      SupportMarkSmallBall R T w (insert p A)
        ((supportMarkingInsertEquiv hpA).symm (v, m))) :
    ∃ a : ℝ,
      a ≤ normalizedLogWeight T p.1 ∧
        normalizedLogWeight T p.1 ≤ a + 2 * w := by
  have hcoordinates :=
    (supportMarkSmallBall_insert_iff hpA v m).mp hsmall
  exact nonzero_onePivot_forces_interval hv
    hcoordinates.1 hcoordinates.2

end Erdos536
