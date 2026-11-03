import TR23.ExchangeWalsh
import TR23.ExchangeContraction
import Mathlib.Algebra.CharP.Two

namespace TR23.Exchange

theorem group_self_add (g : Group64) : g + g = 0 := by
  funext j
  apply Prod.ext <;> exact CharTwo.add_self_eq_zero _

theorem shift_ne_zero : shift ≠ 0 := by decide

theorem main_ne_zero (g : MainCoord) : g.val ≠ 0 := by
  intro h
  have hn := (Finset.mem_filter.mp g.property).2 (0 : Fin 3)
  apply hn
  rw [h]
  rfl

theorem residual_ne_zero (g : ResidualCoord) : g.val ≠ 0 := by
  intro h
  have hn := (Finset.mem_filter.mp g.property).2.2
  apply hn
  simpa [h] using (show shift ∈ mainSet by decide)

theorem pair_in_inner (a b : MainCoord) (h : a.val + b.val = shift) :
    a.val ∈ innerSet ∧ b.val ∈ innerSet := by
  have ha : a.val + shift = b.val := by
    rw [← h]
    calc
      a.val + (a.val + b.val) = (a.val + a.val) + b.val := by abel
      _ = b.val := by rw [group_self_add, zero_add]
  have hb : b.val + shift = a.val := by
    rw [← h]
    calc
      b.val + (a.val + b.val) = (b.val + b.val) + a.val := by abel
      _ = a.val := by rw [group_self_add, zero_add]
  exact ⟨Finset.mem_filter.mpr ⟨a.property, ha ▸ b.property⟩,
    Finset.mem_filter.mpr ⟨b.property, hb ▸ a.property⟩⟩

theorem aux_pair_sum (a b : Group64) :
    (∑ i : InnerCoord, ∑ j : InnerCoord,
      if a = i.val then if b = j.val then
        if i.val + j.val = shift then (-1 : ℤ) else 0 else 0 else 0) =
    if a ∈ innerSet then if b ∈ innerSet then
      if a + b = shift then -1 else 0 else 0 else 0 := by
  classical
  rw [Finset.sum_coe_sort innerSet (fun i : Group64 =>
    ∑ j : InnerCoord, if a = i then if b = j.val then
      if i + j.val = shift then (-1 : ℤ) else 0 else 0 else 0)]
  have inner (i : Group64) :
      (∑ j : InnerCoord, if a = i then if b = j.val then
        if i + j.val = shift then (-1 : ℤ) else 0 else 0 else 0) =
      ∑ j ∈ innerSet, if a = i then if b = j then
        if i + j = shift then (-1 : ℤ) else 0 else 0 else 0 :=
    Finset.sum_coe_sort innerSet (fun j : Group64 =>
      if a = i then if b = j then if i + j = shift then (-1 : ℤ) else 0 else 0 else 0)
  simp_rw [inner]
  simp

theorem head_main_main (a b : MainCoord) :
    contraction (.inr (.inl ())) (.inl a) (.inl b) = 0 := by
  classical
  rw [contraction_factorization]
  simp only [sparseContraction, targetMask, walsh_identity, rowMap]
  have select (i j : InnerCoord) :
      (if i.val + j.val = shift then
        -1 * (if a.val = i.val then (1 : ℤ) else 0) * (if b.val = j.val then 1 else 0) +
        0 * 0 * (if b.val = j.val then 1 else 0) + 0 * (if a.val = j.val then 1 else 0) * 0
      else 0) =
      (if a.val = i.val then if b.val = j.val then
        if i.val + j.val = shift then -1 else 0 else 0 else 0) := by
    split_ifs <;> norm_num
  simp_rw [select]
  rw [aux_pair_sum]
  by_cases h : a.val + b.val = shift
  · obtain ⟨ha, hb⟩ := pair_in_inner a b h
    have hz : shift + a.val + b.val = 0 := by
      rw [add_assoc, h, group_self_add]
    simp [hz, h, ha, hb]
  · have hz : shift + a.val + b.val ≠ 0 := by
      intro hz
      apply h
      calc
        a.val + b.val = (shift + shift) + (a.val + b.val) := by rw [group_self_add, zero_add]
        _ = shift + (shift + a.val + b.val) := by abel
        _ = shift := by rw [hz, add_zero]
    simp [hz, h]

theorem group_add_eq_zero_iff (a b : Group64) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have hh := congrArg (fun x : Group64 => x + b) h
    simpa [add_assoc, group_self_add] using hh
  · intro h
    rw [h, group_self_add]

theorem shift_sum_iff (a b : Group64) :
    shift + a + b = 0 ↔ a + b = shift := by
  rw [add_assoc, group_add_eq_zero_iff]
  exact eq_comm

theorem main_residual_unpaired (a : MainCoord) (b : ResidualCoord) :
    a.val + b.val ≠ shift := by
  intro h
  have hb : b.val + shift = a.val := by
    rw [← h]
    calc
      b.val + (a.val + b.val) = (b.val + b.val) + a.val := by abel
      _ = a.val := by rw [group_self_add, zero_add]
  apply (Finset.mem_filter.mp b.property).2.2
  rw [hb]
  exact a.property

theorem head_head_main (a : MainCoord) :
    contraction (.inr (.inl ())) (.inr (.inl ())) (.inl a) = 0 := by
  rw [contraction_factorization]
  simp [sparseContraction, targetMask, walsh_identity, rowMap,
    group_self_add, main_ne_zero]

theorem head_head_head :
    contraction (.inr (.inl ())) (.inr (.inl ())) (.inr (.inl ())) = 0 := by
  rw [contraction_factorization]
  simp [sparseContraction, targetMask, walsh_identity, rowMap,
    group_self_add, shift_ne_zero]

theorem head_head_residual (a : ResidualCoord) :
    contraction (.inr (.inl ())) (.inr (.inl ())) (.inr (.inr a)) = 0 := by
  rw [contraction_factorization]
  simp [sparseContraction, targetMask, walsh_identity, rowMap,
    group_self_add, residual_ne_zero]

theorem head_main_residual (a : MainCoord) (b : ResidualCoord) :
    contraction (.inr (.inl ())) (.inl a) (.inr (.inr b)) = 0 := by
  rw [contraction_factorization]
  simp [sparseContraction, targetMask, walsh_identity, rowMap,
    shift_sum_iff, main_residual_unpaired]

theorem head_residual_residual (a b : ResidualCoord) :
    contraction (.inr (.inl ())) (.inr (.inr a)) (.inr (.inr b)) =
      64 * (if a.val + b.val = shift then 1 else 0) := by
  rw [contraction_factorization]
  simp [sparseContraction, targetMask, walsh_identity, rowMap, shift_sum_iff]

end TR23.Exchange
