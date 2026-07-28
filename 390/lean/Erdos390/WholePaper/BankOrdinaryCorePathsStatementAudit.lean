import Erdos390.WholePaper.BankOrdinaryCorePaths

/-! # Expanded statement audit for actual ordinary core paths -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example : bankSmallCoreStep 6 = 5 := rfl
example : bankSmallCoreStep 22 = 18 := rfl

example {q : ℕ} (hq : 6 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    6 ≤ q ∧
      ¬ IsPowerOfTwo q ∧
      ¬ IsPowerOfTwo (bankOrdinaryCoreStep q) ∧
      5 ≤ bankOrdinaryCoreStep q ∧
      bankOrdinaryCoreStep q < q ∧
      bankOrdinaryCoreStep q = bankOrdinaryCoreStep q ∧
      InGeometricDescentCell
        (bankOrdinaryScale (bankOrdinaryComponentScaleIndex q)) q
          (bankOrdinaryCoreStep q) :=
  bankOrdinaryCoreStep_spec hq hqPower

example {q : ℕ} (hq : 5 ≤ q) :
    (bankOrdinaryCoreVertices q).head? = some q :=
  bankOrdinaryCoreVertices_head?_eq hq

example {q : ℕ} (hq : 5 ≤ q) :
    (bankOrdinaryCoreVertices q).getLast? = some 5 :=
  bankOrdinaryCoreVertices_getLast?_eq_five hq

example {q : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    List.IsChain
      (fun source target ↦
        target = bankOrdinaryCoreStep source ∧
          IsBankOrdinaryCoreComponent source target)
      (bankOrdinaryCoreVertices q) :=
  bankOrdinaryCoreVertices_isChain hq hqPower

example {q : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q) :
    (∑ s ∈ bankOrdinaryCoreSources q,
        factorMoveChange s (bankOrdinaryCoreStep s)) =
      factorMoveChange q 5 :=
  bankOrdinaryFinitePathChange_telescope hq hqPower

example {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    (∑ s ∈ bankOrdinaryCoreSources p,
        factorMoveChange s (bankOrdinaryCoreStep s)) +
          fourBottomMovesChange = -coordinateUnit p :=
  bankOrdinaryFiniteFullPathChange_eq_neg_unit hp hp5

example {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : j ≤ 5) :
    (bankOrdinaryCoreSourcesAtScale q j).card ≤ 17 :=
  bankOrdinaryCoreSourcesAtSmallScale_card_le hq hqPower hj

example {q j : ℕ} (hq : 5 ≤ q) (hqPower : ¬ IsPowerOfTwo q)
    (hj : 6 ≤ j) :
    (bankOrdinaryCoreSourcesAtScale q j).card ≤ 2 :=
  bankOrdinaryCoreSourcesAtLargeScale_card_le_two hq hqPower hj

end

end Erdos390.WholePaper
