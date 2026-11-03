import TR23.ExchangeCoefficients
import TR23.ExchangePermutation
import TR23.ExchangeSymmetry

namespace TR23.Exchange

attribute [local irreducible] contraction

theorem main_main_main (a b c : MainCoord) :
    contraction (.inl a) (.inl b) (.inl c) =
      64 * targetCoefficient (.inl a) (.inl b) (.inl c) := by
  rw [contraction_factorization]
  simp [sparseContraction, targetMask, walsh_identity, rowMap, targetCoefficient]
  rw [← main_group_permutation]
  split_ifs <;> norm_num

theorem head_negative (b c : TargetCoord)
    (h : -2 + rowDegree b + rowDegree c < 0) :
    contraction (.inr (.inl ())) b c = 0 := by
  rcases b with b | (⟨⟩ | b) <;> rcases c with c | (⟨⟩ | c)
  all_goals try cases_type Unit
  all_goals simp only [rowDegree] at h
  all_goals first
    | exact head_main_main _ _
    | exact head_head_main _
    | exact head_head_head
    | exact head_head_residual _
    | exact head_main_residual _ _
    | (rw [contraction_swap23]; exact head_head_main _)
    | (rw [contraction_swap23]; exact head_head_residual _)
    | (rw [contraction_swap23]; exact head_main_residual _ _)
    | omega

theorem contraction_negative (a b c : TargetCoord)
    (h : rowDegree a + rowDegree b + rowDegree c < 0) :
    contraction a b c = 0 := by
  rcases a with a | (⟨⟩ | a) <;> rcases b with b | (⟨⟩ | b) <;>
    rcases c with c | (⟨⟩ | c)
  all_goals try cases_type Unit
  all_goals simp only [rowDegree] at h
  all_goals first
    | omega
    | (apply head_negative; simpa only [rowDegree] using h)
    | (rw [contraction_swap12]; apply head_negative; simp only [rowDegree]; omega)
    | (rw [contraction_swap23, contraction_swap12]; apply head_negative;
        simp only [rowDegree]; omega)

theorem negative_coefficients (n : ℤ) (hn : n < 0) (a b c : TargetCoord) :
    laurentCoefficient n a b c = 0 := by
  unfold laurentCoefficient
  split_ifs with h
  · exact contraction_negative a b c (by omega)
  · rfl

theorem constant_coefficient (a b c : TargetCoord) :
    laurentCoefficient 0 a b c = 64 * targetCoefficient a b c := by
  rcases a with a | (⟨⟩ | a) <;> rcases b with b | (⟨⟩ | b) <;>
    rcases c with c | (⟨⟩ | c)
  all_goals try cases_type Unit
  all_goals norm_num [laurentCoefficient, rowDegree, targetCoefficient, tightCoefficient]
  · exact main_main_main a b c
  · simpa using head_residual_residual b c
  · rw [contraction_swap12]
    simpa using head_residual_residual a c
  · rw [contraction_swap23, contraction_swap12]
    simpa using head_residual_residual a b

theorem degree_sum_le_three (a b c : TargetCoord) :
    rowDegree a + rowDegree b + rowDegree c ≤ 3 := by
  rcases a with a | (⟨⟩ | a) <;> rcases b with b | (⟨⟩ | b) <;>
    rcases c with c | (⟨⟩ | c) <;> norm_num [rowDegree]

theorem upper_degree (n : ℤ) (hn : 3 < n) (a b c : TargetCoord) :
    laurentCoefficient n a b c = 0 := by
  have hd := degree_sum_le_three a b c
  have hne : n ≠ rowDegree a + rowDegree b + rowDegree c := by omega
  simp [laurentCoefficient, hne]

end TR23.Exchange
