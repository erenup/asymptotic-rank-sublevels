import TR23.GeometryDefinitions
import Mathlib.Tactic

open scoped BigOperators

namespace TR23.Geometry

theorem L_action_cofactor {R : Type*} [CommRing R]
    (T S : Tensor3 R) (r : MinorRow) :
    (L T).mulVec S r =
      ∑ i : Fin 4, cofactor T r.1 r.2.2 i *
        flatten S r.1 (rows4 r.2.2 i) r.2.1 := by
  simp only [Matrix.mulVec, dotProduct, L, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [mul_ite, ite_mul, flatten]

theorem appended_minor_identity {R : Type*} [CommRing R]
    (T S : Tensor3 R) (r : MinorRow) :
    (L T).mulVec S r = (appendedMinor T S r).det := by
  have hlast (b : Fin 3) : (3 : Fin 4).succAbove b = b.castSucc := by
    fin_cases b <;> rfl
  have hsub (i : Fin 4) :
      (appendedMinor T S r).submatrix i.succAbove (3 : Fin 4).succAbove =
        (fun a b : Fin 3 => flatten T r.1 (rows4 r.2.2 (i.succAbove a)) b) := by
    ext a b
    simp [Matrix.submatrix, hlast, appendedMinor]
  rw [L_action_cofactor, Matrix.det_succ_column _ (3 : Fin 4)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hsub]
  dsimp [cofactor, appendedMinor]
  ring

theorem self_kernel {R : Type*} [CommRing R] (T : Tensor3 R) :
    (L T).mulVec T = 0 := by
  funext r
  rw [appended_minor_identity]
  apply Matrix.det_zero_of_column_eq (i := r.2.1.castSucc) (j := 3)
  · intro h
    have hv := congrArg Fin.val h
    have hc := r.2.1.isLt
    change r.2.1.val = 3 at hv
    omega
  · intro k
    simp [appendedMinor]

end TR23.Geometry
