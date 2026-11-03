import TR23.GeometryRankRows
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace TR23.Geometry

set_option backward.isDefEq.respectTransparency false

theorem P_kernel (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S = 0 ↔ ∃ c : ℂ, S = c • P ℂ := by
  constructor
  · intro h
    have z0 : S 0 = 0 := by
      simpa only [rank_action_0, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 0, 2)
    have z1 : S 1 = 0 := by
      simpa only [rank_action_1, Pi.zero_apply, neg_eq_zero] using congrFun h (2, 1, 2)
    have z2 : S 2 = 0 := by
      simpa only [rank_action_2, Pi.zero_apply, neg_eq_zero] using congrFun h (2, 2, 2)
    have z3 : S 3 = 0 := by
      simpa only [rank_action_3, Pi.zero_apply, neg_eq_zero] using congrFun h (1, 1, 2)
    have z4 : S 4 = 0 := by
      simpa only [rank_action_4, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 0, 61)
    have z6 : S 6 = 0 := by
      simpa only [rank_action_5, Pi.zero_apply, neg_eq_zero] using congrFun h (1, 2, 2)
    have z8 : S 8 = 0 := by
      simpa only [rank_action_6, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 0, 67)
    have z9 : S 9 = 0 := by
      simpa only [rank_action_7, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 1, 2)
    have z10 : S 10 = 0 := by
      simpa only [rank_action_8, Pi.zero_apply, neg_eq_zero] using congrFun h (1, 0, 61)
    have z12 : S 12 = 0 := by
      simpa only [rank_action_9, Pi.zero_apply, neg_eq_zero] using congrFun h (2, 0, 61)
    have z13 : S 13 = 0 := by
      simpa only [rank_action_10, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 1, 61)
    have z14 : S 14 = 0 := by
      simpa only [rank_action_11, Pi.zero_apply, neg_eq_zero] using congrFun h (2, 2, 61)
    have z16 : S 16 = 0 := by
      simpa only [rank_action_12, Pi.zero_apply, neg_eq_zero] using congrFun h (1, 2, 61)
    have z17 : S 17 = 0 := by
      simpa only [rank_action_13, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 1, 67)
    have z18 : S 18 = 0 := by
      simpa only [rank_action_14, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 2, 2)
    have z20 : S 20 = 0 := by
      simpa only [rank_action_15, Pi.zero_apply, neg_eq_zero] using congrFun h (1, 0, 67)
    have z22 : S 22 = 0 := by
      simpa only [rank_action_16, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 2, 61)
    have z23 : S 23 = 0 := by
      simpa only [rank_action_17, Pi.zero_apply, neg_eq_zero] using congrFun h (1, 1, 67)
    have z24 : S 24 = 0 := by
      simpa only [rank_action_18, Pi.zero_apply, neg_eq_zero] using congrFun h (2, 0, 67)
    have z25 : S 25 = 0 := by
      simpa only [rank_action_19, Pi.zero_apply, neg_eq_zero] using congrFun h (2, 1, 67)
    have z26 : S 26 = 0 := by
      simpa only [rank_action_20, Pi.zero_apply, neg_eq_zero] using congrFun h (0, 2, 67)
    have e7 : S 7 = S 5 := by
      have hz := congrFun h (0, 0, 66)
      rw [rank_action_21] at hz
      simp only [Pi.zero_apply] at hz
      linear_combination -hz
    have p7 : S 7 = S 5 := e7
    have e21 : S 21 = S 5 := by
      have hz := congrFun h (1, 1, 65)
      rw [rank_action_22] at hz
      simp only [Pi.zero_apply] at hz
      linear_combination -hz
    have p21 : S 21 = S 5 := e21
    have e19 : S 19 = S 21 := by
      have hz := congrFun h (0, 2, 57)
      rw [rank_action_23] at hz
      simp only [Pi.zero_apply] at hz
      linear_combination -hz
    have p19 : S 19 = S 5 := e19.trans p21
    have e11 : S 11 = S 19 := by
      have hz := congrFun h (1, 0, 66)
      rw [rank_action_24] at hz
      simp only [Pi.zero_apply] at hz
      linear_combination hz
    have p11 : S 11 = S 5 := e11.trans p19
    have e15 : S 15 = S 11 := by
      have hz := congrFun h (0, 1, 65)
      rw [rank_action_25] at hz
      simp only [Pi.zero_apply] at hz
      linear_combination -hz
    have p15 : S 15 = S 5 := e15.trans p11
    refine ⟨S 5, ?_⟩
    funext p
    fin_cases p
    · change S 0 = S 5 * 0
      simpa using z0
    · change S 1 = S 5 * 0
      simpa using z1
    · change S 2 = S 5 * 0
      simpa using z2
    · change S 3 = S 5 * 0
      simpa using z3
    · change S 4 = S 5 * 0
      simpa using z4
    · change S 5 = S 5 * 1
      simp
    · change S 6 = S 5 * 0
      simpa using z6
    · change S 7 = S 5 * 1
      simpa using p7
    · change S 8 = S 5 * 0
      simpa using z8
    · change S 9 = S 5 * 0
      simpa using z9
    · change S 10 = S 5 * 0
      simpa using z10
    · change S 11 = S 5 * 1
      simpa using p11
    · change S 12 = S 5 * 0
      simpa using z12
    · change S 13 = S 5 * 0
      simpa using z13
    · change S 14 = S 5 * 0
      simpa using z14
    · change S 15 = S 5 * 1
      simpa using p15
    · change S 16 = S 5 * 0
      simpa using z16
    · change S 17 = S 5 * 0
      simpa using z17
    · change S 18 = S 5 * 0
      simpa using z18
    · change S 19 = S 5 * 1
      simpa using p19
    · change S 20 = S 5 * 0
      simpa using z20
    · change S 21 = S 5 * 1
      simpa using p21
    · change S 22 = S 5 * 0
      simpa using z22
    · change S 23 = S 5 * 0
      simpa using z23
    · change S 24 = S 5 * 0
      simpa using z24
    · change S 25 = S 5 * 0
      simpa using z25
    · change S 26 = S 5 * 0
      simpa using z26
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul, self_kernel, smul_zero]

theorem P_ne_zero : P ℂ ≠ 0 := by
  intro h
  have hh := congrFun h 5
  change (1 : ℂ) = 0 at hh
  norm_num at hh

theorem P_kernel_submodule :
    LinearMap.ker (L (P ℂ)).mulVecLin = Submodule.span ℂ {P ℂ} := by
  ext S
  change ((L (P ℂ)).mulVec S = 0) ↔ S ∈ Submodule.span ℂ {P ℂ}
  rw [P_kernel, Submodule.mem_span_singleton]
  exact exists_congr fun c => eq_comm

theorem P_kernel_finrank :
    Module.finrank ℂ (LinearMap.ker (L (P ℂ)).mulVecLin) = 1 := by
  rw [P_kernel_submodule]
  exact finrank_span_singleton P_ne_zero

theorem P_minor_rank : (L (P ℂ)).rank = 26 := by
  have h := LinearMap.finrank_range_add_finrank_ker (L (P ℂ)).mulVecLin
  change (L (P ℂ)).rank +
    Module.finrank ℂ (LinearMap.ker (L (P ℂ)).mulVecLin) =
    Module.finrank ℂ (Fin 27 → ℂ) at h
  rw [P_kernel_finrank] at h
  norm_num at h
  omega

end TR23.Geometry
