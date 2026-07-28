import Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalGeometry

/-!
# Statement audit for literal Section 9 final geometry

The audit expands the collision and seven-fact geometry contracts, checks the
literal ratio-cell flow, and records every public declaration in source
order.  The finite production theorem exposes only the source-agnostic
rounded selector and guarded-slack fields needed by actual-P87 traffic.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Exact state and collision statements -/

example {n M : Nat} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateOneValue slot component =
      R.prechargeAlternateStateValue
        (bankPaperPathComponentRequest slot component) :=
  R.pathStateOneValue_eq_prechargeAlternateStateValue slot component

example {c : Real} {depth n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    R.exactificationState slot selected ⊆
      R.roughCanonicalGuardSet certificate deltaStar :=
  R.exactificationState_subset_roughCanonicalGuardSet
    certificate deltaStar slot selected

example {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) :
    R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar ↔
      Disjoint (R.paperFixedExceptionalFactors deltaStar)
        R.allComponentOccurrences := by
  rfl

/-! ## Exact seven-fact geometry contract -/

example {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat) :
    R.BankPaperCanonicalSectionNineFinalGeometry
        certificate deltaStar K ↔
      let candidates :=
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K
      let fixed := R.paperFixedExceptionalFactors deltaStar
      candidates ⊆
          factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        fixed ⊆
          factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        Disjoint fixed candidates ∧
        (∀ slot selected,
          Disjoint fixed (R.exactificationState slot selected)) ∧
        (∀ slot selected,
          Disjoint candidates (R.exactificationState slot selected)) ∧
        Disjoint certificate.anchors fixed ∧
        Disjoint certificate.anchors candidates := by
  rfl

example {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hKh : K * upperTailLength c n ≤ n)
    (hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar) :
    R.BankPaperCanonicalSectionNineFinalGeometry
      certificate deltaStar K :=
  R.bankPaperCanonicalSectionNineFinalGeometry_of_fixedComponentCollisionFree
    certificate deltaStar hKh hfixedComponents

/-! ## Literal ratio-cell flow -/

example {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c : Real} {depth n W : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat)
    (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W) (rho : Real)
    (selector : Nat → Real) :
    R.bankPaperCanonicalSectionNineRatioCellFlow
        M certificate deltaStar K hdelta hn hW S rho selector =
      tangentRatioCellEarthmoverFlow
        (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
        (bankPaperCanonicalTangentResidual (W := W) R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          selector)
        (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
        (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho) := by
  rfl

/-! ## Complete public declaration census -/

#check pathStateOneValue_eq_prechargeAlternateStateValue
#check exactificationState_subset_roughCanonicalGuardSet
#check BankPaperCanonicalSectionNineFixedComponentCollisionFree
#check BankPaperCanonicalSectionNineFinalGeometry
#check
  bankPaperCanonicalSectionNineFinalGeometry_of_fixedComponentCollisionFree
#check bankPaperCanonicalSectionNineRatioCellFlow
#check BankPaperCanonicalSectionNineFinalPayload
#check
  bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack

end BankPaperRealization

end

end Erdos390.WholePaper
