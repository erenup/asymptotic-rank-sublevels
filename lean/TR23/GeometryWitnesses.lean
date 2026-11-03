import TR23.GeometryDefinitions
import Mathlib.Tactic

namespace TR23.Geometry

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem witness_P_flattening_rank (m : Fin 3) : (flatten (P ℂ) m).rank = 3 := by
  have hminor : (flatten (P ℂ) m).submatrix
      (![5, 2, 1] : Fin 3 → Fin 9) id = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    fin_cases m <;> fin_cases i <;> fin_cases j <;> rfl
  apply le_antisymm (Matrix.rank_le_width _) ?_
  have h := Matrix.rank_submatrix_le (flatten (P ℂ) m)
    (![5, 2, 1] : Fin 3 → Fin 9) id
  simpa [hminor] using h

theorem witness_x_fourth_rank : (dFlatten (x ℂ)).rank = 1 := by
  have houter : dFlatten (x ℂ) =
      Matrix.vecMulVec (P ℂ) (fun d : Fin 2 => if d = 0 then 1 else 0) := by
    ext p d
    fin_cases d <;> simp [dFlatten, x, Matrix.vecMulVec]
  have hminor : (dFlatten (x ℂ)).submatrix
      (fun _ : Fin 1 => encode 0 1 2) (fun _ : Fin 1 => (0 : Fin 2)) =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i; fin_cases j; rfl
  apply le_antisymm ?_ ?_
  · rw [houter]
    exact Matrix.rank_vecMulVec_le _ _
  · have h := Matrix.rank_submatrix_le (dFlatten (x ℂ))
      (fun _ : Fin 1 => encode 0 1 2) (fun _ : Fin 1 => (0 : Fin 2))
    simpa [hminor] using h

theorem witness_y_fourth_rank : (dFlatten (y ℂ)).rank = 2 := by
  have hminor : (dFlatten (y ℂ)).submatrix
      (![encode 0 0 0, encode 1 1 1] : Fin 2 → Fin 27) id =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [dFlatten, y, coordinateTerm, encode, finProdFinEquiv]
  apply le_antisymm (Matrix.rank_le_width _) ?_
  have h := Matrix.rank_submatrix_le (dFlatten (y ℂ))
    (![encode 0 0 0, encode 1 1 1] : Fin 2 → Fin 27) id
  simpa [hminor] using h

theorem witness_y_outside_rank_one : ¬ FourthRankOne (y ℂ) := by
  simp [FourthRankOne, witness_y_fourth_rank]

theorem witness_y_balanced_rank (m : Fin 3) : (balancedFlatten (y ℂ) m).rank = 2 := by
  have hminor : (balancedFlatten (y ℂ) m).submatrix
      (![0, 4] : Fin 2 → Fin 9)
      (![(0, 0), (1, 1)] : Fin 2 → Fin 3 × Fin 2) =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j
    fin_cases m <;> fin_cases i <;> fin_cases j <;>
      norm_num [balancedFlatten, y, coordinateTerm, flatCoord, encode,
        finProdFinEquiv, Fin.divNat, Fin.modNat]
  apply le_antisymm ?_ ?_
  · have hsupport : Function.support (balancedFlatten (y ℂ) m).row ⊆
        ({0, 4} : Finset (Fin 9)) := by
      intro r hr
      by_contra hn
      apply hr
      ext cd
      rcases cd with ⟨c, d⟩
      fin_cases m <;> fin_cases r <;> simp at hn
      all_goals fin_cases c <;> fin_cases d <;>
        norm_num [Matrix.row, balancedFlatten, y, coordinateTerm, flatCoord,
          encode, finProdFinEquiv, Fin.divNat, Fin.modNat]
    have h := Matrix.rank_le_card_of_support_subset
      (balancedFlatten (y ℂ) m) ({0, 4} : Finset (Fin 9)) hsupport
    simpa using h
  · have h := Matrix.rank_submatrix_le (balancedFlatten (y ℂ) m)
      (![0, 4] : Fin 2 → Fin 9)
      (![(0, 0), (1, 1)] : Fin 2 → Fin 3 × Fin 2)
    simpa [hminor] using h

theorem witness_basis_determinant : basisChange.det = -2 * Complex.I := by
  rw [Matrix.det_fin_three]
  change (1 : ℂ) * 1 * (-Complex.I) - 1 * 1 * Complex.I -
    0 * 0 * (-Complex.I) + 0 * 1 * 0 + 0 * 0 * Complex.I - 0 * 1 * 0 =
      -2 * Complex.I
  ring

theorem witness_basis_nonsingular : basisChange.det ≠ 0 := by
  rw [witness_basis_determinant]
  exact mul_ne_zero (by norm_num) Complex.I_ne_zero

theorem witness_basis_image : basisAction basisChange (P ℂ) = (2 : ℂ) • cw2 ℂ := by
  ext p
  fin_cases p <;>
    norm_num [basisAction, basisChange, P, cw2, decode, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.sum_univ_succ, Complex.I_sq]

end TR23.Geometry
