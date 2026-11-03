import TR23.GeometryMinors
import Mathlib.Tactic

open scoped BigOperators
namespace TR23.Geometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem cofactor_0_2 (i : Fin 4) :
    cofactor (P ℂ) 0 2 i = (![1, 0, 0, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 2 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 2 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 2 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 2 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_0_57 (i : Fin 4) :
    cofactor (P ℂ) 0 57 i = (![-1, 0, 1, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 57 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 57 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 57 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 57 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_0_61 (i : Fin 4) :
    cofactor (P ℂ) 0 61 i = (![0, 0, 1, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 61 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 61 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 61 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 61 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_0_65 (i : Fin 4) :
    cofactor (P ℂ) 0 65 i = (![0, 1, 0, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 65 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 65 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 65 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 65 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_0_66 (i : Fin 4) :
    cofactor (P ℂ) 0 66 i = (![0, 0, 1, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 66 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 66 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 66 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 66 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_0_67 (i : Fin 4) :
    cofactor (P ℂ) 0 67 i = (![0, 0, 0, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 67 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 67 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 67 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 0 (rows4 67 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_1_2 (i : Fin 4) :
    cofactor (P ℂ) 1 2 i = (![1, 0, 0, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 2 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 2 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 2 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 2 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_1_61 (i : Fin 4) :
    cofactor (P ℂ) 1 61 i = (![0, 0, 1, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 61 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 61 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 61 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 61 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_1_65 (i : Fin 4) :
    cofactor (P ℂ) 1 65 i = (![0, 1, 0, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 65 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 65 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 65 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 65 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_1_66 (i : Fin 4) :
    cofactor (P ℂ) 1 66 i = (![0, 0, 1, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 66 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 66 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 66 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 66 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_1_67 (i : Fin 4) :
    cofactor (P ℂ) 1 67 i = (![0, 0, 0, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 67 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 67 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 67 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 1 (rows4 67 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_2_2 (i : Fin 4) :
    cofactor (P ℂ) 2 2 i = (![1, 0, 0, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 2 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 2 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 0], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 2 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 0], ![0, 0, 1], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 2 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 0], ![0, 0, 1], ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_2_61 (i : Fin 4) :
    cofactor (P ℂ) 2 61 i = (![0, 0, 1, 0] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 61 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 61 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![0, 0, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 61 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 61 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem cofactor_2_67 (i : Fin 4) :
    cofactor (P ℂ) 2 67 i = (![0, 0, 0, -1] : Fin 4 → ℂ) i := by
  fin_cases i
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 67 ((0 : Fin 4).succAbove a)) b) =
        (![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 3 * Matrix.det (![![0, 1, 0], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 3 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 67 ((1 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 4 * Matrix.det (![![0, 0, 1], ![1, 0, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 4 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 67 ((2 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 5 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![0, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 5 * z) hd).trans hc
  · unfold cofactor
    have hm : (fun a b : Fin 3 =>
        flatten (P ℂ) 2 (rows4 67 ((3 : Fin 4).succAbove a)) b) =
        (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) := by
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    have hd := congrArg Matrix.det hm
    have hc : (-1 : ℂ) ^ 6 * Matrix.det (![![0, 0, 1], ![0, 1, 0], ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) ℂ) = -1 := by
      norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]
    exact (congrArg (fun z : ℂ => (-1 : ℂ) ^ 6 * z) hd).trans hc

theorem rank_action_0 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 0, 2) = S 0 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 0 + ((0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((0 : ℂ) * S 5 + (0)))) = S 0
  ring

theorem rank_action_1 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (2, 1, 2) = S 1 := by
  rw [L_action_cofactor]
  simp only [cofactor_2_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 1 + ((0 : ℂ) * S 4 + ((0 : ℂ) * S 7 + ((0 : ℂ) * S 16 + (0)))) = S 1
  ring

theorem rank_action_2 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (2, 2, 2) = S 2 := by
  rw [L_action_cofactor]
  simp only [cofactor_2_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 2 + ((0 : ℂ) * S 5 + ((0 : ℂ) * S 8 + ((0 : ℂ) * S 17 + (0)))) = S 2
  ring

theorem rank_action_3 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 1, 2) = S 3 := by
  rw [L_action_cofactor]
  simp only [cofactor_1_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 3 + ((0 : ℂ) * S 4 + ((0 : ℂ) * S 5 + ((0 : ℂ) * S 14 + (0)))) = S 3
  ring

theorem rank_action_4 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 0, 61) = S 4 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((1 : ℂ) * S 4 + ((0 : ℂ) * S 5 + (0)))) = S 4
  ring

theorem rank_action_5 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 2, 2) = S 6 := by
  rw [L_action_cofactor]
  simp only [cofactor_1_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 6 + ((0 : ℂ) * S 7 + ((0 : ℂ) * S 8 + ((0 : ℂ) * S 17 + (0)))) = S 6
  ring

theorem rank_action_6 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 0, 67) = (-S 8) := by
  rw [L_action_cofactor]
  simp only [cofactor_0_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((0 : ℂ) * S 5 + ((-1 : ℂ) * S 8 + (0)))) = (-S 8)
  ring

theorem rank_action_7 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 1, 2) = S 9 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 9 + ((0 : ℂ) * S 10 + ((0 : ℂ) * S 11 + ((0 : ℂ) * S 14 + (0)))) = S 9
  ring

theorem rank_action_8 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 0, 61) = S 10 := by
  rw [L_action_cofactor]
  simp only [cofactor_1_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((1 : ℂ) * S 10 + ((0 : ℂ) * S 11 + (0)))) = S 10
  ring

theorem rank_action_9 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (2, 0, 61) = S 12 := by
  rw [L_action_cofactor]
  simp only [cofactor_2_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 3 + ((0 : ℂ) * S 6 + ((1 : ℂ) * S 12 + ((0 : ℂ) * S 15 + (0)))) = S 12
  ring

theorem rank_action_10 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 1, 61) = S 13 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 10 + ((0 : ℂ) * S 11 + ((1 : ℂ) * S 13 + ((0 : ℂ) * S 14 + (0)))) = S 13
  ring

theorem rank_action_11 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (2, 2, 61) = S 14 := by
  rw [L_action_cofactor]
  simp only [cofactor_2_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 5 + ((0 : ℂ) * S 8 + ((1 : ℂ) * S 14 + ((0 : ℂ) * S 17 + (0)))) = S 14
  ring

theorem rank_action_12 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 2, 61) = S 16 := by
  rw [L_action_cofactor]
  simp only [cofactor_1_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 7 + ((0 : ℂ) * S 8 + ((1 : ℂ) * S 16 + ((0 : ℂ) * S 17 + (0)))) = S 16
  ring

theorem rank_action_13 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 1, 67) = (-S 17) := by
  rw [L_action_cofactor]
  simp only [cofactor_0_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 10 + ((0 : ℂ) * S 11 + ((0 : ℂ) * S 14 + ((-1 : ℂ) * S 17 + (0)))) = (-S 17)
  ring

theorem rank_action_14 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 2, 2) = S 18 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_2, Fin.sum_univ_succ]
  change (1 : ℂ) * S 18 + ((0 : ℂ) * S 19 + ((0 : ℂ) * S 20 + ((0 : ℂ) * S 23 + (0)))) = S 18
  ring

theorem rank_action_15 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 0, 67) = (-S 20) := by
  rw [L_action_cofactor]
  simp only [cofactor_1_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((0 : ℂ) * S 11 + ((-1 : ℂ) * S 20 + (0)))) = (-S 20)
  ring

theorem rank_action_16 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 2, 61) = S 22 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_61, Fin.sum_univ_succ]
  change (0 : ℂ) * S 19 + ((0 : ℂ) * S 20 + ((1 : ℂ) * S 22 + ((0 : ℂ) * S 23 + (0)))) = S 22
  ring

theorem rank_action_17 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 1, 67) = (-S 23) := by
  rw [L_action_cofactor]
  simp only [cofactor_1_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 4 + ((0 : ℂ) * S 5 + ((0 : ℂ) * S 14 + ((-1 : ℂ) * S 23 + (0)))) = (-S 23)
  ring

theorem rank_action_18 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (2, 0, 67) = (-S 24) := by
  rw [L_action_cofactor]
  simp only [cofactor_2_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 3 + ((0 : ℂ) * S 6 + ((0 : ℂ) * S 15 + ((-1 : ℂ) * S 24 + (0)))) = (-S 24)
  ring

theorem rank_action_19 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (2, 1, 67) = (-S 25) := by
  rw [L_action_cofactor]
  simp only [cofactor_2_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 4 + ((0 : ℂ) * S 7 + ((0 : ℂ) * S 16 + ((-1 : ℂ) * S 25 + (0)))) = (-S 25)
  ring

theorem rank_action_20 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 2, 67) = (-S 26) := by
  rw [L_action_cofactor]
  simp only [cofactor_0_67, Fin.sum_univ_succ]
  change (0 : ℂ) * S 19 + ((0 : ℂ) * S 20 + ((0 : ℂ) * S 23 + ((-1 : ℂ) * S 26 + (0)))) = (-S 26)
  ring

theorem rank_action_21 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 0, 66) = S 5 + (-S 7) := by
  rw [L_action_cofactor]
  simp only [cofactor_0_66, Fin.sum_univ_succ]
  change (0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((1 : ℂ) * S 5 + ((-1 : ℂ) * S 7 + (0)))) = S 5 + (-S 7)
  ring

theorem rank_action_22 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 1, 65) = S 5 + (-S 21) := by
  rw [L_action_cofactor]
  simp only [cofactor_1_65, Fin.sum_univ_succ]
  change (0 : ℂ) * S 4 + ((1 : ℂ) * S 5 + ((0 : ℂ) * S 14 + ((-1 : ℂ) * S 21 + (0)))) = S 5 + (-S 21)
  ring

theorem rank_action_23 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 2, 57) = (-S 19) + S 21 := by
  rw [L_action_cofactor]
  simp only [cofactor_0_57, Fin.sum_univ_succ]
  change (-1 : ℂ) * S 19 + ((0 : ℂ) * S 20 + ((1 : ℂ) * S 21 + ((0 : ℂ) * S 23 + (0)))) = (-S 19) + S 21
  ring

theorem rank_action_24 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (1, 0, 66) = S 11 + (-S 19) := by
  rw [L_action_cofactor]
  simp only [cofactor_1_66, Fin.sum_univ_succ]
  change (0 : ℂ) * S 1 + ((0 : ℂ) * S 2 + ((1 : ℂ) * S 11 + ((-1 : ℂ) * S 19 + (0)))) = S 11 + (-S 19)
  ring

theorem rank_action_25 (S : Tensor3 ℂ) :
    (L (P ℂ)).mulVec S (0, 1, 65) = S 11 + (-S 15) := by
  rw [L_action_cofactor]
  simp only [cofactor_0_65, Fin.sum_univ_succ]
  change (0 : ℂ) * S 10 + ((1 : ℂ) * S 11 + ((0 : ℂ) * S 14 + ((-1 : ℂ) * S 15 + (0)))) = S 11 + (-S 15)
  ring

end TR23.Geometry
