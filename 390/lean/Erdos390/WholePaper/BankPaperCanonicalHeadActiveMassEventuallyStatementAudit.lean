import Erdos390.WholePaper.BankPaperCanonicalHeadActiveMassEventually

/-!
# Statement audit for the eventual head active-mass bridge

The expanded examples expose the minimal lower-bound predicate, the exact
`q₀-d` reduction, and the eventual constructor threshold.  The final
census contains every public declaration in the source module.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

example (q : Nat -> Real)
    (H : BankPaperCanonicalActiveMassPaperScaleLower q) :
    Tendsto q atTop atTop ∧ ∀ᶠ n : Nat in atTop, 1 <= q n := by
  exact ⟨bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower q H,
    eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower q H⟩

example (q0 d : Nat -> Real)
    (Hq0 : BankPaperCanonicalActiveMassPaperScaleLower q0)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    BankPaperCanonicalActiveMassPaperScaleLower
      (fun n => q0 n - d n) :=
  bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
    q0 d Hq0 hd

/-! ## Complete public declaration census -/

#check BankPaperCanonicalActiveMassPaperScaleLower
#check BankPaperCanonicalHeadActiveMassPaperScaleLower
#check bankPaperCanonicalSubunitHeadSimplexReserve
#check bankPaperCanonicalSubunitHeadSimplexReserve_activeMass
#check bankPaperCanonicalSubunitHeadSimplexReserve_not_one_le
#check exists_headSimplexReserve_pos_activeMass_not_one_le
#check bankPaperCanonicalActiveMass_tendsto_atTop_of_paperScaleLower
#check eventually_const_le_bankPaperCanonicalActiveMass_of_paperScaleLower
#check eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
#check bankPaperCanonicalHeadActiveMass_tendsto_atTop_of_paperScaleLower
#check eventually_one_le_bankPaperCanonicalHeadActiveMass
#check secondOrderScale_div_L_isLittleO_secondOrderScale
#check bankPaperCanonicalActiveMassPaperScaleLower_sub_of_isLittleO
#check bankPaperCanonicalActiveMassPaperScaleLower_sub_of_logScale_isBigO
#check bankPaperCanonicalHeadActiveMassPaperScaleLower_of_heightCenter
#check eventually_one_le_bankPaperCanonicalHeadActiveMass_of_heightCenter
#check bankPaperCanonicalLiteralActiveMass_scaledFamily_tendsto_atTop
#check eventually_one_le_bankPaperCanonicalLiteralQMass_scaledFamily
#check eventually_bankPaperCanonicalActualActiveMeasureConstructor_self
#check eventually_one_le_bankPaperCanonicalPaperDataActiveSeedMass
#check eventually_bankPaperCanonicalPaperDataActualActiveMeasureConstructor_self

end

end Erdos390.WholePaper
