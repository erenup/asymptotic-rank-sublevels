import TR23.ExchangeDefinitions
import Mathlib.Tactic

namespace TR23.Exchange

theorem contraction_factorization (a b c : TargetCoord) :
    contraction a b c = sparseContraction a b c := by
  classical
  simp [contraction, sparseContraction, Fintype.sum_sum_type,
    sourceCoefficient, rowMap, ite_and, ite_mul, mul_ite,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

end TR23.Exchange
