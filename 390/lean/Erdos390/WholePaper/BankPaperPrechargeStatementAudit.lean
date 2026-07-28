import Erdos390.WholePaper.BankPaperPrecharge

/-! # Expanded statement audit for the actual precharge layer -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Filter Asymptotics
open scoped BigOperators

noncomputable section

example {n M : ℕ} (R : BankBottomPaperRealization n M)
    (hTwoN : 2 * n ≤ M)
    (request : ↑(bankBottomPaperRequests n)) :
    2 * n < R.donorFactor request :=
  R.two_mul_n_lt_donorFactor hTwoN request

example {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ∈ factorInterval n M ∧
      R.prechargeAlternateStateValue request ∈ factorInterval n M ∧
      R.prechargeDonorValue request ∈ factorInterval n M :=
  ⟨R.prechargeBaseStateValue_mem_factorInterval request,
    R.prechargeAlternateStateValue_mem_factorInterval request,
    R.prechargeDonorValue_mem_factorInterval request⟩

example {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request') :
    Disjoint (R.prechargeComponentOccurrences request)
      (R.prechargeComponentOccurrences request') :=
  R.prechargeComponentOccurrences_disjoint hrequest

example {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    completeRoughSignature (yNat n)
        (R.prechargeBaseStateValue request) =
        completeRoughSignature (yNat n)
          (R.prechargeAlternateStateValue request) ∧
      completeRoughSignature (yNat n)
          (R.prechargeAlternateStateValue request) =
        completeRoughSignature (yNat n)
          (R.prechargeDonorValue request) :=
  R.precharge_completeRoughSignature_eq request

example {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request')
    (endpoint endpoint' : BankPaperPrechargeEndpoint) :
    R.prechargeEndpointValue request endpoint ≠
      R.prechargeEndpointValue request' endpoint' :=
  R.prechargeEndpointValue_ne_of_request_ne
    hrequest endpoint endpoint'

example {n M : ℕ} (R : BankPaperRealization n M)
    {request request' : BankPaperMarkerRequest n}
    (hrequest : request ≠ request')
    (endpoint' : BankPaperPrechargeEndpoint) :
    R.prechargeDonorValue request ≠
      R.prechargeEndpointValue request' endpoint' :=
  R.prechargeDonorValue_ne_endpointValue_of_request_ne
    hrequest endpoint'

example {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeBaseStateValue request ≠
      R.prechargeAlternateStateValue request :=
  R.prechargeBaseStateValue_ne_alternateStateValue request

example {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective
        (fun indexed : BankPaperMarkerRequest n ×
            BankPaperPrechargeEndpoint =>
          R.prechargeEndpointValue indexed.1 indexed.2) ∧
      Function.Injective R.prechargeDonorValue :=
  ⟨R.prechargeStateOccurrence_injective,
    R.prechargeDonorValue_injective⟩

example {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Injective R.prechargeBaseStateValue ∧
      Function.Injective R.prechargeAlternateStateValue :=
  ⟨R.prechargeBaseStateValue_injective,
    R.prechargeAlternateStateValue_injective⟩

example {n M p : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) (hp : yNat n < p) :
    (R.prechargeBaseStateValue request).factorization p =
      (R.prechargeDonorValue request).factorization p :=
  R.prechargeBase_donor_factorization_eq_of_yNat_lt request hp

example {n M : ℕ} (R : BankPaperRealization n M)
    (request : ↑(bankBottomRelevantPaperRequests n))
    (hmove : R.bottom.move
        (bankBottomRelevantRequestToPaperRequest request) = .threeToTwo ∨
      R.bottom.move
        (bankBottomRelevantRequestToPaperRequest request) = .twoToOne) :
    R.prechargeDonorValue (.inl request) =
        R.prechargeBaseStateValue (.inl request) ∨
      R.prechargeDonorValue (.inl request) =
        R.prechargeAlternateStateValue (.inl request) :=
  R.prechargeBottomTerminalDonor_eq_endpoint request hmove

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet ⊆ Finset.Ioc (2 * n) M :=
  R.prechargeDonorSet_subset_tail

example {n M : ℕ} (R : BankPaperRealization n M)
    (request : BankPaperMarkerRequest n) :
    R.prechargeDonorValue request ∈ Finset.Ioc (2 * n) M :=
  R.prechargeDonorValue_mem_tail request

example {n h : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h)) :
    R.prechargeDonorSet.prod id ∣ centralTailProduct n h :=
  R.prechargeDonorSet_prod_dvd_centralTailProduct

example {n M : ℕ} (R : BankPaperRealization n M) :
    Disjoint R.prechargeBaseState R.prechargeAlternateState ∧
      R.prechargeBaseState.card =
        Fintype.card (BankPaperMarkerRequest n) ∧
      R.prechargeAlternateState.card =
        Fintype.card (BankPaperMarkerRequest n) ∧
      R.prechargeDonorSet.card =
        Fintype.card (BankPaperMarkerRequest n) :=
  ⟨R.prechargeBaseState_disjoint_prechargeAlternateState,
    R.prechargeBaseState_card,
    R.prechargeAlternateState_card,
    R.prechargeDonorSet_card⟩

example {n M : ℕ} (R : BankPaperRealization n M) :
    Function.Bijective R.prechargeDonorToBase ∧
      (∀ donor : ↑R.prechargeDonorSet,
        completeRoughSignature (yNat n)
            (R.prechargeDonorToBase donor).1 =
          completeRoughSignature (yNat n) donor.1) :=
  ⟨⟨R.prechargeDonorToBase_injective,
      R.prechargeDonorToBase_surjective⟩,
    R.prechargeDonorToBase_completeRoughSignature⟩

example {n M : ℕ} (R : BankPaperRealization n M) :
    (R.prechargeBaseStateProduct =
        ∏ request : BankPaperMarkerRequest n,
          R.prechargeBaseStateValue request) ∧
      Fintype.card (BankPaperMarkerRequest n) ≤
        bankPaperAnchorMarkerBudget n :=
  ⟨R.prechargeBaseStateProduct_eq_componentProduct,
    R.prechargeComponentCount_le_anchorMarkerBudget⟩

example {n M : ℕ} (R : BankPaperRealization n M) :
    R.prechargeDonorSet.prod id =
      ∏ request : BankPaperMarkerRequest n,
        R.prechargeDonorValue request :=
  R.prechargeDonorSet_prod_eq_componentProduct

example {n M ℓ : ℕ} (R : BankPaperRealization n M)
    (hℓ : ℓ.Prime) :
    (R.prechargeBaseStateProduct).factorization ℓ ≤
      Fintype.card (BankPaperMarkerRequest n) * Nat.log 2 M :=
  R.prechargeBaseStateProduct_factorization_le hℓ

example {n M ℓ : ℕ} (R : BankPaperRealization n M)
    (hℓ : ℓ.Prime) :
    (R.prechargeBaseStateProduct).factorization ℓ ≤
      bankPaperAnchorMarkerBudget n * Nat.log 2 M :=
  R.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget hℓ

example {n M p : ℕ} (R : BankPaperRealization n M)
    (hp : yNat n < p) :
    (R.prechargeBaseStateProduct).factorization p =
      (R.prechargeDonorSet.prod id).factorization p :=
  R.prechargeBaseStateProduct_factorization_eq_donorSet_prod hp

example :
    (fun n : ℕ ↦ (Fintype.card (BankPaperMarkerRequest n) : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ) ^ 2) :=
  BankPaperRealization.prechargeComponentCount_isBigO_yNat_sq

end

end Erdos390.WholePaper
