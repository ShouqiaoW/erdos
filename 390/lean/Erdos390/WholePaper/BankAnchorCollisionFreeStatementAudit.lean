import Erdos390.WholePaper.BankAnchorCollisionFree

/-! # Expanded statement audit for complete bank/anchor collision freedom -/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, 2 * depth + 1 ≤ yNat n :=
  eventually_bankAnchor_fixed_le_yNat (2 * depth + 1)

example (depth : ℕ) :
    ∀ᶠ n : ℕ in atTop, yNat n < centralAnchorCutoff depth n :=
  eventually_yNat_lt_centralAnchorCutoff depth

example {n yNatValue P core p : ℕ}
    (hP : P.Prime) (hp : p.Prime)
    (hyTwo : 2 ≤ yNatValue) (hPy : yNatValue < P)
    (hcoreSmooth : core ∈ Nat.smoothNumbers (yNatValue + 1))
    (hcoreNonpower : ¬ IsPowerOfTwo core) :
    P * core ≠ promotedCentralFactor n p :=
  marker_mul_nonpower_smooth_ne_promotedCentralFactor
    hP hp hyTwo hPy hcoreSmooth hcoreNonpower

example {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomPaperRequests n)) :
    R.bottom.donorFactor request = R.bottom.upperStateFactor request ∨
      2 * n < R.bottom.donorFactor request :=
  R.bottomDonor_eq_upperState_or_two_mul_n_lt request

example {c : ℝ} {depth n M : ℕ}
    (R : BankPaperRealization n M) (hdepth : 2 ≤ depth)
    (hnCutoff : centralAnchorCutoffThreshold depth ≤ n)
    (hfixed : 2 * depth + 1 ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) :
    Disjoint certificate.anchors R.allComponentOccurrences :=
  R.guardedCentralAnchors_disjoint_allComponentOccurrences
    hdepth hnCutoff hfixed hyCutoff certificate

example (c : ℝ) (depth : ℕ) (hdepth : 2 ≤ depth) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (M : ℕ) (R : BankPaperRealization n M)
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        Disjoint certificate.anchors R.allComponentOccurrences :=
  BankPaperRealization.eventually_guardedCentralAnchors_disjoint_allComponentOccurrences
    c depth hdepth

end

end Erdos390.WholePaper
