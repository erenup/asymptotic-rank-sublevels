import TR23.ExchangeDefinitions
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace TR23.Exchange

set_option maxRecDepth 10000
set_option maxHeartbeats 200000

/-- On the three nonzero two-bit symbols, zero sum is exactly a permutation. -/
theorem bitpair_permutation : ∀ x y z : BitPair,
    x ≠ (0, 0) → y ≠ (0, 0) → z ≠ (0, 0) →
    (if x + y + z = 0 then (1 : ℤ) else 0) =
      permutationCoefficient
        (Fin.ofNat 3 (pairCode x - 1))
        (Fin.ofNat 3 (pairCode y - 1))
        (Fin.ofNat 3 (pairCode z - 1)) := by
  decide

theorem main_coordinate_nonzero (a : MainCoord) (j : Fin 3) :
    a.val j ≠ (0, 0) :=
  (Finset.mem_filter.mp a.property).2 j

/-- The all-main group-tensor coefficient is the threefold permutation coefficient. -/
theorem main_group_permutation (a b c : MainCoord) :
    (if a.val + b.val + c.val = 0 then (1 : ℤ) else 0) =
      ∏ j : Fin 3, permutationCoefficient
        (mainDigits a j) (mainDigits b j) (mainDigits c j) := by
  classical
  by_cases h : a.val + b.val + c.val = 0
  · rw [ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro j _
    change permutationCoefficient
      (Fin.ofNat 3 (pairCode (a.val j) - 1))
      (Fin.ofNat 3 (pairCode (b.val j) - 1))
      (Fin.ofNat 3 (pairCode (c.val j) - 1)) = 1
    rw [← bitpair_permutation (a.val j) (b.val j) (c.val j)
      (main_coordinate_nonzero a j) (main_coordinate_nonzero b j)
      (main_coordinate_nonzero c j)]
    have hj : a.val j + b.val j + c.val j = 0 := congrFun h j
    rw [ite_eq_left hj]
  · rw [ite_eq_right h]
    have hn : ¬ ∀ j : Fin 3, a.val j + b.val j + c.val j = 0 := by
      intro hall
      apply h
      funext j
      exact hall j
    obtain ⟨j, hj⟩ := not_forall.mp hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    change permutationCoefficient
      (Fin.ofNat 3 (pairCode (a.val j) - 1))
      (Fin.ofNat 3 (pairCode (b.val j) - 1))
      (Fin.ofNat 3 (pairCode (c.val j) - 1)) = 0
    rw [← bitpair_permutation (a.val j) (b.val j) (c.val j)
      (main_coordinate_nonzero a j) (main_coordinate_nonzero b j)
      (main_coordinate_nonzero c j)]
    rw [ite_eq_right hj]

end TR23.Exchange
