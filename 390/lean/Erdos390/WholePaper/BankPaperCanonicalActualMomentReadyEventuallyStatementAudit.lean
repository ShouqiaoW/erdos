import Erdos390.WholePaper.BankPaperCanonicalActualMomentReadyEventually

/-!
# Statement audit for the canonical `MomentReady` connector

The complete public declaration census appears below in source order.  The
expanded examples pin down both the general all-cell scale growth statement
and the exact literal-partition payload exported for Section 9.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

/-! ## Complete public declaration census -/

#check eventually_bankPaperCanonical_all_le_scalePoint_lower
#check eventually_bankPaperCanonical_actualMomentReady

example {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) (A : Real) :
    ∀ᶠ n : Nat in atTop,
      ∀ k : Fin M.cellCount, A ≤ scalePoint n (M.lower k) :=
  eventually_bankPaperCanonical_all_le_scalePoint_lower M hdelta A

example {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) :
    ∀ W : Nat, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : Nat in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          (∀ k : Fin M.cellCount,
            (2 : Real) ≤ scalePoint n (M.lower k)) ∧
          ∀ S : ScaleSeparation M n W,
            RegularMeshPrimeCutoffs.Mesh.MomentReady M
              (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta hn hWne S) :=
  eventually_bankPaperCanonical_actualMomentReady M hdelta

end

end Erdos390.WholePaper
