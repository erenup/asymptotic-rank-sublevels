import TR23.GeometryDefinitions
import Mathlib.Tactic

namespace TR23.Geometry

set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem rows_strictMono (r : Fin 126) : StrictMono (rows4 r) := by
  fin_cases r
  · change StrictMono (![0, 1, 2, 3] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 2, 4] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 2, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 2, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 2, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 2, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 3, 4] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 3, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 3, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 3, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 3, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 4, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 4, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 4, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 4, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 1, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 3, 4] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 3, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 3, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 3, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 3, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 4, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 4, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 4, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 4, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 2, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 4, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 4, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 4, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 4, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 3, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 4, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 4, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 4, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 4, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 4, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 4, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 5, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 5, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 5, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![0, 6, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 3, 4] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 3, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 3, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 3, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 3, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 4, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 4, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 4, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 4, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 2, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 4, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 4, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 4, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 4, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 3, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 4, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 4, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 4, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 4, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 4, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 4, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 5, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 5, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 5, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![1, 6, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 4, 5] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 4, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 4, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 4, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 3, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 4, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 4, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 4, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 4, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 4, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 4, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 5, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 5, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 5, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![2, 6, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 4, 5, 6] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 4, 5, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 4, 5, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 4, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 4, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 4, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 5, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 5, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 5, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![3, 6, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![4, 5, 6, 7] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![4, 5, 6, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![4, 5, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![4, 6, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide
  · change StrictMono (![5, 6, 7, 8] : Fin 4 → Fin 9)
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> decide

def rowCode (r : Fin 126) : ℕ :=
  729 * (rows4 r 0).val + 81 * (rows4 r 1).val +
    9 * (rows4 r 2).val + (rows4 r 3).val

theorem rowCode_strictMono : StrictMono rowCode := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · change 102 < 103
    decide
  · change 103 < 104
    decide
  · change 104 < 105
    decide
  · change 105 < 106
    decide
  · change 106 < 107
    decide
  · change 107 < 112
    decide
  · change 112 < 113
    decide
  · change 113 < 114
    decide
  · change 114 < 115
    decide
  · change 115 < 116
    decide
  · change 116 < 122
    decide
  · change 122 < 123
    decide
  · change 123 < 124
    decide
  · change 124 < 125
    decide
  · change 125 < 132
    decide
  · change 132 < 133
    decide
  · change 133 < 134
    decide
  · change 134 < 142
    decide
  · change 142 < 143
    decide
  · change 143 < 152
    decide
  · change 152 < 193
    decide
  · change 193 < 194
    decide
  · change 194 < 195
    decide
  · change 195 < 196
    decide
  · change 196 < 197
    decide
  · change 197 < 203
    decide
  · change 203 < 204
    decide
  · change 204 < 205
    decide
  · change 205 < 206
    decide
  · change 206 < 213
    decide
  · change 213 < 214
    decide
  · change 214 < 215
    decide
  · change 215 < 223
    decide
  · change 223 < 224
    decide
  · change 224 < 233
    decide
  · change 233 < 284
    decide
  · change 284 < 285
    decide
  · change 285 < 286
    decide
  · change 286 < 287
    decide
  · change 287 < 294
    decide
  · change 294 < 295
    decide
  · change 295 < 296
    decide
  · change 296 < 304
    decide
  · change 304 < 305
    decide
  · change 305 < 314
    decide
  · change 314 < 375
    decide
  · change 375 < 376
    decide
  · change 376 < 377
    decide
  · change 377 < 385
    decide
  · change 385 < 386
    decide
  · change 386 < 395
    decide
  · change 395 < 466
    decide
  · change 466 < 467
    decide
  · change 467 < 476
    decide
  · change 476 < 557
    decide
  · change 557 < 922
    decide
  · change 922 < 923
    decide
  · change 923 < 924
    decide
  · change 924 < 925
    decide
  · change 925 < 926
    decide
  · change 926 < 932
    decide
  · change 932 < 933
    decide
  · change 933 < 934
    decide
  · change 934 < 935
    decide
  · change 935 < 942
    decide
  · change 942 < 943
    decide
  · change 943 < 944
    decide
  · change 944 < 952
    decide
  · change 952 < 953
    decide
  · change 953 < 962
    decide
  · change 962 < 1013
    decide
  · change 1013 < 1014
    decide
  · change 1014 < 1015
    decide
  · change 1015 < 1016
    decide
  · change 1016 < 1023
    decide
  · change 1023 < 1024
    decide
  · change 1024 < 1025
    decide
  · change 1025 < 1033
    decide
  · change 1033 < 1034
    decide
  · change 1034 < 1043
    decide
  · change 1043 < 1104
    decide
  · change 1104 < 1105
    decide
  · change 1105 < 1106
    decide
  · change 1106 < 1114
    decide
  · change 1114 < 1115
    decide
  · change 1115 < 1124
    decide
  · change 1124 < 1195
    decide
  · change 1195 < 1196
    decide
  · change 1196 < 1205
    decide
  · change 1205 < 1286
    decide
  · change 1286 < 1742
    decide
  · change 1742 < 1743
    decide
  · change 1743 < 1744
    decide
  · change 1744 < 1745
    decide
  · change 1745 < 1752
    decide
  · change 1752 < 1753
    decide
  · change 1753 < 1754
    decide
  · change 1754 < 1762
    decide
  · change 1762 < 1763
    decide
  · change 1763 < 1772
    decide
  · change 1772 < 1833
    decide
  · change 1833 < 1834
    decide
  · change 1834 < 1835
    decide
  · change 1835 < 1843
    decide
  · change 1843 < 1844
    decide
  · change 1844 < 1853
    decide
  · change 1853 < 1924
    decide
  · change 1924 < 1925
    decide
  · change 1925 < 1934
    decide
  · change 1934 < 2015
    decide
  · change 2015 < 2562
    decide
  · change 2562 < 2563
    decide
  · change 2563 < 2564
    decide
  · change 2564 < 2572
    decide
  · change 2572 < 2573
    decide
  · change 2573 < 2582
    decide
  · change 2582 < 2653
    decide
  · change 2653 < 2654
    decide
  · change 2654 < 2663
    decide
  · change 2663 < 2744
    decide
  · change 2744 < 3382
    decide
  · change 3382 < 3383
    decide
  · change 3383 < 3392
    decide
  · change 3392 < 3473
    decide
  · change 3473 < 4202
    decide

theorem rows_injective : Function.Injective rows4 := by
  intro r s h
  apply rowCode_strictMono.injective
  simp only [rowCode, h]

theorem ordered_rows_complete (a b c d : Fin 9)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ r : Fin 126, rows4 r = ![a, b, c, d] := by
  fin_cases a <;> fin_cases b <;> norm_num at hab
  all_goals fin_cases c <;> norm_num at hbc
  all_goals fin_cases d <;> norm_num at hcd
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩
  · exact ⟨11, rfl⟩
  · exact ⟨12, rfl⟩
  · exact ⟨13, rfl⟩
  · exact ⟨14, rfl⟩
  · exact ⟨15, rfl⟩
  · exact ⟨16, rfl⟩
  · exact ⟨17, rfl⟩
  · exact ⟨18, rfl⟩
  · exact ⟨19, rfl⟩
  · exact ⟨20, rfl⟩
  · exact ⟨21, rfl⟩
  · exact ⟨22, rfl⟩
  · exact ⟨23, rfl⟩
  · exact ⟨24, rfl⟩
  · exact ⟨25, rfl⟩
  · exact ⟨26, rfl⟩
  · exact ⟨27, rfl⟩
  · exact ⟨28, rfl⟩
  · exact ⟨29, rfl⟩
  · exact ⟨30, rfl⟩
  · exact ⟨31, rfl⟩
  · exact ⟨32, rfl⟩
  · exact ⟨33, rfl⟩
  · exact ⟨34, rfl⟩
  · exact ⟨35, rfl⟩
  · exact ⟨36, rfl⟩
  · exact ⟨37, rfl⟩
  · exact ⟨38, rfl⟩
  · exact ⟨39, rfl⟩
  · exact ⟨40, rfl⟩
  · exact ⟨41, rfl⟩
  · exact ⟨42, rfl⟩
  · exact ⟨43, rfl⟩
  · exact ⟨44, rfl⟩
  · exact ⟨45, rfl⟩
  · exact ⟨46, rfl⟩
  · exact ⟨47, rfl⟩
  · exact ⟨48, rfl⟩
  · exact ⟨49, rfl⟩
  · exact ⟨50, rfl⟩
  · exact ⟨51, rfl⟩
  · exact ⟨52, rfl⟩
  · exact ⟨53, rfl⟩
  · exact ⟨54, rfl⟩
  · exact ⟨55, rfl⟩
  · exact ⟨56, rfl⟩
  · exact ⟨57, rfl⟩
  · exact ⟨58, rfl⟩
  · exact ⟨59, rfl⟩
  · exact ⟨60, rfl⟩
  · exact ⟨61, rfl⟩
  · exact ⟨62, rfl⟩
  · exact ⟨63, rfl⟩
  · exact ⟨64, rfl⟩
  · exact ⟨65, rfl⟩
  · exact ⟨66, rfl⟩
  · exact ⟨67, rfl⟩
  · exact ⟨68, rfl⟩
  · exact ⟨69, rfl⟩
  · exact ⟨70, rfl⟩
  · exact ⟨71, rfl⟩
  · exact ⟨72, rfl⟩
  · exact ⟨73, rfl⟩
  · exact ⟨74, rfl⟩
  · exact ⟨75, rfl⟩
  · exact ⟨76, rfl⟩
  · exact ⟨77, rfl⟩
  · exact ⟨78, rfl⟩
  · exact ⟨79, rfl⟩
  · exact ⟨80, rfl⟩
  · exact ⟨81, rfl⟩
  · exact ⟨82, rfl⟩
  · exact ⟨83, rfl⟩
  · exact ⟨84, rfl⟩
  · exact ⟨85, rfl⟩
  · exact ⟨86, rfl⟩
  · exact ⟨87, rfl⟩
  · exact ⟨88, rfl⟩
  · exact ⟨89, rfl⟩
  · exact ⟨90, rfl⟩
  · exact ⟨91, rfl⟩
  · exact ⟨92, rfl⟩
  · exact ⟨93, rfl⟩
  · exact ⟨94, rfl⟩
  · exact ⟨95, rfl⟩
  · exact ⟨96, rfl⟩
  · exact ⟨97, rfl⟩
  · exact ⟨98, rfl⟩
  · exact ⟨99, rfl⟩
  · exact ⟨100, rfl⟩
  · exact ⟨101, rfl⟩
  · exact ⟨102, rfl⟩
  · exact ⟨103, rfl⟩
  · exact ⟨104, rfl⟩
  · exact ⟨105, rfl⟩
  · exact ⟨106, rfl⟩
  · exact ⟨107, rfl⟩
  · exact ⟨108, rfl⟩
  · exact ⟨109, rfl⟩
  · exact ⟨110, rfl⟩
  · exact ⟨111, rfl⟩
  · exact ⟨112, rfl⟩
  · exact ⟨113, rfl⟩
  · exact ⟨114, rfl⟩
  · exact ⟨115, rfl⟩
  · exact ⟨116, rfl⟩
  · exact ⟨117, rfl⟩
  · exact ⟨118, rfl⟩
  · exact ⟨119, rfl⟩
  · exact ⟨120, rfl⟩
  · exact ⟨121, rfl⟩
  · exact ⟨122, rfl⟩
  · exact ⟨123, rfl⟩
  · exact ⟨124, rfl⟩
  · exact ⟨125, rfl⟩

theorem rows_complete : RowsComplete := by
  refine ⟨rows_strictMono, rows_injective, ?_⟩
  intro f hf
  obtain ⟨r, hr⟩ := ordered_rows_complete (f 0) (f 1) (f 2) (f 3)
    (hf (by decide)) (hf (by decide)) (hf (by decide))
  refine ⟨r, hr.trans ?_⟩
  funext i
  fin_cases i <;> rfl

end TR23.Geometry
