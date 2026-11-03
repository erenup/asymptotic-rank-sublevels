import TR23.ExchangeDefinitions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace TR23.Exchange

theorem pair_walsh (x y z : BitPair) :
    (∑ g : BitPair, pairCharacter x g * pairCharacter y g * pairCharacter z g) =
      if x + y + z = 0 then (4 : ℤ) else 0 := by
  rcases x with ⟨x₀, x₁⟩
  rcases y with ⟨y₀, y₁⟩
  rcases z with ⟨z₀, z₁⟩
  fin_cases x₀ <;> fin_cases x₁ <;> fin_cases y₀ <;> fin_cases y₁ <;>
    fin_cases z₀ <;> fin_cases z₁ <;> decide

theorem walsh_identity (x y z : Group64) :
    (∑ g : Group64, character x g * character y g * character z g) =
      if x + y + z = 0 then (64 : ℤ) else 0 := by
  classical
  have factor : (∑ g : Group64, character x g * character y g * character z g) =
      ∏ j : Fin 3, ∑ b : BitPair,
        pairCharacter (x j) b * pairCharacter (y j) b * pairCharacter (z j) b := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro g _
    simp only [character, Finset.prod_mul_distrib]
  rw [factor]
  simp_rw [pair_walsh]
  by_cases h : x + y + z = 0
  · have hj (j : Fin 3) : x j + y j + z j = 0 := congrFun h j
    simp [h, hj]
  · have hj : ∃ j : Fin 3, x j + y j + z j ≠ 0 := by
      by_contra hn
      push Not at hn
      apply h
      funext j
      exact hn j
    obtain ⟨j, hj⟩ := hj
    simp only [h, ite_false]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

end TR23.Exchange
