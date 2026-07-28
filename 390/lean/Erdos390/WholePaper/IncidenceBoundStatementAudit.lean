import Erdos390.WholePaper.IncidenceBound

open scoped BigOperators

namespace Erdos390.WholePaper

example {carriers selected small : Finset ℕ}
    (hsub : carriers ⊆ selected)
    (hselectedPos : ∀ a ∈ selected, 0 < a)
    (hdiv : ∀ a ∈ carriers,
      ∃ ell ∈ small, ell.Prime ∧ ell ∣ a) :
    carriers.card ≤
      ∑ ell ∈ small, (selected.prod id).factorization ell :=
  card_le_sum_prod_factorization hsub hselectedPos hdiv

example {large selected small : Finset ℕ} {carrier : ℕ → ℕ}
    (hcarrierMem : ∀ p ∈ large, carrier p ∈ selected)
    (hcarrierInj : Set.InjOn carrier (large : Set ℕ))
    (hselectedPos : ∀ a ∈ selected, 0 < a)
    (hdiv : ∀ p ∈ large,
      ∃ ell ∈ small, ell.Prime ∧ ell ∣ carrier p) :
    large.card ≤
      ∑ ell ∈ small, (selected.prod id).factorization ell :=
  card_le_sum_prod_factorization_of_injective_carriers
    hcarrierMem hcarrierInj hselectedPos hdiv

end Erdos390.WholePaper
