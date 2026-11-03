import TR23.ExchangeFinite
import TR23.ExchangeLaurent

namespace TR23.Exchange

/-- The complete finite integer Laurent-exchange certificate, with all output
coordinates and all Laurent degrees universally quantified in its fields. -/
theorem exchangeCertificate : ExchangeCertificate where
  group_card := finite_group_card
  set_cards := finite_set_cards
  dimensions := finite_dimensions
  inner_translation := finite_inner_translation
  residual_translation := finite_residual_translation
  shift_fixed_point_free := finite_shift_fixed_point_free
  digit_bijection := finite_digit_bijection
  walsh := walsh_identity
  contraction_factorization := contraction_factorization
  negative_coefficients := negative_coefficients
  constant_coefficient := constant_coefficient
  upper_degree := upper_degree
  tight_dimension := finite_tight_dimension
  tight_injective := finite_tight_injective
  tight_support_card := finite_tight_support_card
  tight_weight_sum := finite_tight_weight_sum
  tight_marginals := finite_tight_marginals

end TR23.Exchange
