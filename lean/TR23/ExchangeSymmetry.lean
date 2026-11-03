import TR23.ExchangeDefinitions
import Mathlib.Tactic

namespace TR23.Exchange

theorem sourceCoefficient_swap12 (u v w : SourceCoord) :
    sourceCoefficient u v w = sourceCoefficient v u w := by
  rcases u with u | (_ | u) <;>
    rcases v with v | (_ | v) <;>
    rcases w with w | (_ | w) <;>
    simp only [sourceCoefficient]
  all_goals first
    | rfl
    | simp only [add_comm]
    | split_ifs <;> simp_all

theorem sourceCoefficient_swap23 (u v w : SourceCoord) :
    sourceCoefficient u v w = sourceCoefficient u w v := by
  rcases u with u | (_ | u) <;>
    rcases v with v | (_ | v) <;>
    rcases w with w | (_ | w) <;>
    simp only [sourceCoefficient]
  all_goals first
    | rfl
    | simp only [add_comm]
    | split_ifs <;> simp_all

theorem contraction_swap12 (a b c : TargetCoord) :
    contraction a b c = contraction b a c := by
  unfold contraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [sourceCoefficient_swap12 v u w]
  ring

theorem contraction_swap23 (a b c : TargetCoord) :
    contraction a b c = contraction a c b := by
  unfold contraction
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  rw [sourceCoefficient_swap23 u w v]
  ring

end TR23.Exchange
