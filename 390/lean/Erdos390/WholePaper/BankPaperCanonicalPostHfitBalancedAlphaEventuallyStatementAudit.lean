import Erdos390.WholePaper.BankPaperCanonicalPostHfitBalancedAlphaEventually

/-!
# Statement audit for eventual Post-Hfit balanced-alpha feasibility

The examples below expose both the finite algebra and the uniform bridge
quantifiers used by the post-height supplier.
-/

open Filter Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

#check roughHeadBalancedAlpha_mem_Icc_of_tail_lower

example
    {W n h K : Nat} {c beta ell : Real}
    (hc : 0 < c) (hn : 0 < n) (hKpos : 0 < K)
    (hell : 0 < ell) (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ c / roughHeadDensity W)
    (hKlarge : 1 / roughHeadDensity W ≤ (K : Real))
    (htail : c * (n : Real) / ell ≤ (h : Real)) :
    roughHeadBalancedAlpha W n h K beta ell ∈
      Icc (0 : Real) 1 :=
  roughHeadBalancedAlpha_mem_Icc_of_tail_lower
    hc hn hKpos hell hbeta hbetaUpper hKlarge htail

namespace BankPaperRealization

#check bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
#check eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
#check
  exists_K0_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBeta
#check
  exists_paperParameters_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W K0 : Nat) {c betaProt betaAct : Real} (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real))) :
    ∀ᶠ n : Nat in atTop,
      ∀ B : BridgeData Head Band,
        B.sampleData.n = n →
        B.sampleData.W = W →
        bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 :=
  eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    W K0 hc hbeta hbetaUpper hKlarge

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W : Nat) {c betaProt betaAct : Real}
    (hc : 0 < c) (hbetaProt : 0 < betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaSmall :
      betaProt + betaAct <
        c / (3 * roughHeadDensity W)) :
    ∃ K0 : Nat,
      ∀ᶠ n : Nat in atTop,
        ∀ B : BridgeData Head Band,
          B.sampleData.n = n →
          B.sampleData.W = W →
          bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 :=
  exists_K0_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBeta
    W hc hbetaProt hbetaAct hbetaSmall

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W : Nat) {c : Real} (hc : 0 < c) :
    ∃ betaProt betaAct : Real, ∃ K0 : Nat,
      0 < betaProt ∧
      0 < betaAct ∧
      betaProt + betaAct <
        c / (3 * roughHeadDensity W) ∧
      ∀ᶠ n : Nat in atTop,
        ∀ B : BridgeData Head Band,
          B.sampleData.n = n →
          B.sampleData.W = W →
          bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 :=
  exists_paperParameters_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    W hc

end BankPaperRealization

end

end Erdos390.WholePaper
