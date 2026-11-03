import TR23.ExchangeDefinitions
import Mathlib.Tactic

namespace TR23.Exchange

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem finite_group_card : Fintype.card Group64 = 64 := by
  norm_num [Group64, BitPair]

theorem finite_set_cards :
    mainSet.card = 27 ∧ innerSet.card = 8 ∧ residualSet.card = 18 := by
  decide

theorem finite_dimensions :
    Fintype.card SourceCoord = 73 ∧ Fintype.card TargetCoord = 46 := by
  simp [SourceCoord, TargetCoord, TightCoord, InnerCoord, MainCoord, ResidualCoord,
    finite_set_cards.1, finite_set_cards.2.1, finite_set_cards.2.2]

theorem finite_inner_translation :
    ∀ g : Group64, g ∈ innerSet ↔ g + shift ∈ innerSet := by
  decide

theorem finite_residual_translation :
    ∀ g : Group64, g ∈ residualSet ↔ g + shift ∈ residualSet := by
  decide

theorem finite_shift_fixed_point_free : ∀ g : Group64, g + shift ≠ g := by
  decide

end TR23.Exchange
