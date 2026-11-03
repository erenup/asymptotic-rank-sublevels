import TR23.ExchangeFiniteBasics

namespace TR23.Exchange

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem finite_digit_bijection : Function.Bijective mainDigits := by
  decide

theorem finite_tight_dimension : Fintype.card TightCoord = 19 := by
  simp [TightCoord, ResidualCoord, finite_set_cards.2.2]

theorem finite_tight_injective : Function.Injective tightWeight := by
  decide

theorem finite_tight_support_card : tightSupport.card = 54 := by
  decide

theorem finite_tight_weight_sum : ∀ p ∈ tightSupport,
    tightWeight p.1.1 + tightWeight p.1.2 + tightWeight p.2 = 0 := by
  simp only [tightSupport, Finset.mem_filter, Finset.mem_univ, true_and]
  decide

theorem finite_tight_marginals : ∀ mode : Fin 3, ∀ x : TightCoord,
    (tightSupport.filter fun p => tripleCoord p mode = x).card =
      if x = .inl () then 18 else 2 := by
  decide

end TR23.Exchange
