import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Complex.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators

namespace TR23.Geometry

/-- Coordinates are ordered as `9*i + 3*j + k`. -/
abbrev Tensor3 (R : Type*) := Fin 27 → R
abbrev Tensor4 (R : Type*) := (Fin 27 × Fin 2) → R
abbrev MinorRow := Fin 3 × Fin 3 × Fin 126

def encode (i j k : Fin 3) : Fin 27 :=
  finProdFinEquiv (i, finProdFinEquiv (j, k))

def decode (p : Fin 27) : Fin 3 × Fin 3 × Fin 3 :=
  let pair : Fin 3 × Fin 9 := finProdFinEquiv.symm p
  (pair.1, finProdFinEquiv.symm pair.2)

/-- The coefficient-one sum over the six permutations of `(0,1,2)`. -/
def P (R : Type*) [CommRing R] : Tensor3 R := fun p =>
  let ijk := decode p
  if ijk.1 ≠ ijk.2.1 ∧ ijk.1 ≠ ijk.2.2 ∧ ijk.2.1 ≠ ijk.2.2 then 1 else 0

/-- Insert the singleton-mode column into the lexicographically indexed pair.
Mode 0 gives BC|A, mode 1 gives AC|B, and mode 2 gives AB|C. -/
def flatCoord (m : Fin 3) (r : Fin 9) (c : Fin 3) : Fin 27 :=
  let pair : Fin 3 × Fin 3 := finProdFinEquiv.symm r
  match m.val with
  | 0 => encode c pair.1 pair.2
  | 1 => encode pair.1 c pair.2
  | _ => encode pair.1 pair.2 c

def flatten {R : Type*} (T : Tensor3 R) (m : Fin 3) :
    Matrix (Fin 9) (Fin 3) R := fun r c => T (flatCoord m r c)

/-- Every increasing four-row choice from the nine flattening rows,
listed in Python `itertools.combinations(range(9), 4)` order. -/
def rows4 : Fin 126 → Fin 4 → Fin 9 :=
  ![![0, 1, 2, 3],
    ![0, 1, 2, 4],
    ![0, 1, 2, 5],
    ![0, 1, 2, 6],
    ![0, 1, 2, 7],
    ![0, 1, 2, 8],
    ![0, 1, 3, 4],
    ![0, 1, 3, 5],
    ![0, 1, 3, 6],
    ![0, 1, 3, 7],
    ![0, 1, 3, 8],
    ![0, 1, 4, 5],
    ![0, 1, 4, 6],
    ![0, 1, 4, 7],
    ![0, 1, 4, 8],
    ![0, 1, 5, 6],
    ![0, 1, 5, 7],
    ![0, 1, 5, 8],
    ![0, 1, 6, 7],
    ![0, 1, 6, 8],
    ![0, 1, 7, 8],
    ![0, 2, 3, 4],
    ![0, 2, 3, 5],
    ![0, 2, 3, 6],
    ![0, 2, 3, 7],
    ![0, 2, 3, 8],
    ![0, 2, 4, 5],
    ![0, 2, 4, 6],
    ![0, 2, 4, 7],
    ![0, 2, 4, 8],
    ![0, 2, 5, 6],
    ![0, 2, 5, 7],
    ![0, 2, 5, 8],
    ![0, 2, 6, 7],
    ![0, 2, 6, 8],
    ![0, 2, 7, 8],
    ![0, 3, 4, 5],
    ![0, 3, 4, 6],
    ![0, 3, 4, 7],
    ![0, 3, 4, 8],
    ![0, 3, 5, 6],
    ![0, 3, 5, 7],
    ![0, 3, 5, 8],
    ![0, 3, 6, 7],
    ![0, 3, 6, 8],
    ![0, 3, 7, 8],
    ![0, 4, 5, 6],
    ![0, 4, 5, 7],
    ![0, 4, 5, 8],
    ![0, 4, 6, 7],
    ![0, 4, 6, 8],
    ![0, 4, 7, 8],
    ![0, 5, 6, 7],
    ![0, 5, 6, 8],
    ![0, 5, 7, 8],
    ![0, 6, 7, 8],
    ![1, 2, 3, 4],
    ![1, 2, 3, 5],
    ![1, 2, 3, 6],
    ![1, 2, 3, 7],
    ![1, 2, 3, 8],
    ![1, 2, 4, 5],
    ![1, 2, 4, 6],
    ![1, 2, 4, 7],
    ![1, 2, 4, 8],
    ![1, 2, 5, 6],
    ![1, 2, 5, 7],
    ![1, 2, 5, 8],
    ![1, 2, 6, 7],
    ![1, 2, 6, 8],
    ![1, 2, 7, 8],
    ![1, 3, 4, 5],
    ![1, 3, 4, 6],
    ![1, 3, 4, 7],
    ![1, 3, 4, 8],
    ![1, 3, 5, 6],
    ![1, 3, 5, 7],
    ![1, 3, 5, 8],
    ![1, 3, 6, 7],
    ![1, 3, 6, 8],
    ![1, 3, 7, 8],
    ![1, 4, 5, 6],
    ![1, 4, 5, 7],
    ![1, 4, 5, 8],
    ![1, 4, 6, 7],
    ![1, 4, 6, 8],
    ![1, 4, 7, 8],
    ![1, 5, 6, 7],
    ![1, 5, 6, 8],
    ![1, 5, 7, 8],
    ![1, 6, 7, 8],
    ![2, 3, 4, 5],
    ![2, 3, 4, 6],
    ![2, 3, 4, 7],
    ![2, 3, 4, 8],
    ![2, 3, 5, 6],
    ![2, 3, 5, 7],
    ![2, 3, 5, 8],
    ![2, 3, 6, 7],
    ![2, 3, 6, 8],
    ![2, 3, 7, 8],
    ![2, 4, 5, 6],
    ![2, 4, 5, 7],
    ![2, 4, 5, 8],
    ![2, 4, 6, 7],
    ![2, 4, 6, 8],
    ![2, 4, 7, 8],
    ![2, 5, 6, 7],
    ![2, 5, 6, 8],
    ![2, 5, 7, 8],
    ![2, 6, 7, 8],
    ![3, 4, 5, 6],
    ![3, 4, 5, 7],
    ![3, 4, 5, 8],
    ![3, 4, 6, 7],
    ![3, 4, 6, 8],
    ![3, 4, 7, 8],
    ![3, 5, 6, 7],
    ![3, 5, 6, 8],
    ![3, 5, 7, 8],
    ![3, 6, 7, 8],
    ![4, 5, 6, 7],
    ![4, 5, 6, 8],
    ![4, 5, 7, 8],
    ![4, 6, 7, 8],
    ![5, 6, 7, 8]]

/-- Completeness is a proof obligation, not an assumption on a supplied table. -/
def RowsComplete : Prop :=
  (∀ r : Fin 126, StrictMono (rows4 r)) ∧
  Function.Injective rows4 ∧
  (∀ f : Fin 4 → Fin 9, StrictMono f → ∃ r : Fin 126, rows4 r = f)

/-- The actual 4-by-4 selected-row matrix `[T_flat | S_column]`. -/
def appendedMinor {R : Type*} (T S : Tensor3 R) (r : MinorRow) :
    Matrix (Fin 4) (Fin 4) R := fun i j =>
  if h : j.val < 3 then
    flatten T r.1 (rows4 r.2.2 i) ⟨j.val, h⟩
  else
    flatten S r.1 (rows4 r.2.2 i) r.2.1

/-- Signed cofactor of row `i` in the last column of the appended minor. -/
def cofactor {R : Type*} [CommRing R] (T : Tensor3 R)
    (m : Fin 3) (s : Fin 126) (i : Fin 4) : R :=
  (-1 : R) ^ (i.val + 3) *
    Matrix.det (fun a b : Fin 3 => flatten T m (rows4 s (i.succAbove a)) b)

/-- The full 1134-by-27 appended-minor coefficient matrix. Every coefficient
is defined from a signed 3-by-3 determinant; no surrogate rank matrix occurs. -/
def L {R : Type*} [CommRing R] (T : Tensor3 R) :
    Matrix MinorRow (Fin 27) R := fun r p =>
  ∑ i : Fin 4, cofactor T r.1 r.2.2 i *
    (if p = flatCoord r.1 (rows4 r.2.2 i) r.2.1 then 1 else 0)

/-- ABC|D flattening (the transpose of the Python checker's D|ABC matrix). -/
def dFlatten {R : Type*} (W : Tensor4 R) : Matrix (Fin 27) (Fin 2) R :=
  fun p d => W (p, d)

/-- The three balanced flattenings, indexed by the omitted singleton of ABC. -/
def balancedFlatten {R : Type*} (W : Tensor4 R) (m : Fin 3) :
    Matrix (Fin 9) (Fin 3 × Fin 2) R :=
  fun r cd => W (flatCoord m r cd.1, cd.2)

/-- Explicit first witness `P ⊗ d₀`. -/
def x (R : Type*) [CommRing R] : Tensor4 R :=
  fun pd => if pd.2 = 0 then P R pd.1 else 0

/-- A coordinate rank-one four-mode tensor, in array form. -/
def coordinateTerm (R : Type*) [CommRing R] (i j k : Fin 3) (d : Fin 2) :
    Tensor4 R := fun pd => if pd = (encode i j k, d) then 1 else 0

/-- Explicit second witness `e₀⊗e₀⊗e₀⊗d₀ + e₁⊗e₁⊗e₁⊗d₁`. -/
def y (R : Type*) [CommRing R] : Tensor4 R :=
  coordinateTerm R 0 0 0 0 + coordinateTerm R 1 1 1 1

def FourthRankOne (W : Tensor4 ℂ) : Prop := (dFlatten W).rank ≤ 1

/-- Six-term small Coppersmith--Winograd tensor `cw₂`. -/
def cw2 (R : Type*) [CommRing R] : Tensor3 R := fun p =>
  let ijk := decode p
  if (ijk.1 = 0 ∧ ijk.2.1 = ijk.2.2 ∧ ijk.2.1 ≠ 0) ∨
     (ijk.2.1 = 0 ∧ ijk.1 = ijk.2.2 ∧ ijk.1 ≠ 0) ∨
     (ijk.2.2 = 0 ∧ ijk.1 = ijk.2.1 ∧ ijk.1 ≠ 0) then 1 else 0

/-- The exact Gaussian-integer matrix in `geometry_witness.json`. -/
def basisChange : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![1, 0, 0], ![0, 1, 1], ![0, Complex.I, -Complex.I]]

/-- Coordinate definition of applying one matrix in all three tensor modes. -/
def basisAction (B : Matrix (Fin 3) (Fin 3) ℂ) (T : Tensor3 ℂ) :
    Tensor3 ℂ := fun p =>
  let out := decode p
  ∑ q : Fin 27,
    let inp := decode q
    B out.1 inp.1 * B out.2.1 inp.2.1 * B out.2.2 inp.2.2 * T q

/-- Proposed exact finite geometry layer. This structure contains proof
obligations only; it does not assert their existence. It has no asymptotic-rank,
border-rank, Zariski-openness, or irreducibility premise or conclusion. -/
structure GeometryCertificate : Prop where
  row_enumeration : RowsComplete
  appended_minor_identity : ∀ (T S : Tensor3 ℂ) (r : MinorRow),
    (L T).mulVec S r = (appendedMinor T S r).det
  self_kernel : ∀ T : Tensor3 ℂ, (L T).mulVec T = 0
  P_flattening_rank : ∀ m : Fin 3, (flatten (P ℂ) m).rank = 3
  P_minor_rank : (L (P ℂ)).rank = 26
  P_kernel : ∀ S : Tensor3 ℂ,
    (L (P ℂ)).mulVec S = 0 ↔ ∃ c : ℂ, S = c • P ℂ
  x_fourth_rank : (dFlatten (x ℂ)).rank = 1
  y_fourth_rank : (dFlatten (y ℂ)).rank = 2
  y_balanced_rank : ∀ m : Fin 3, (balancedFlatten (y ℂ) m).rank = 2
  y_outside_rank_one : ¬ FourthRankOne (y ℂ)
  basis_determinant : basisChange.det = -2 * Complex.I
  basis_nonsingular : basisChange.det ≠ 0
  basis_image : basisAction basisChange (P ℂ) = (2 : ℂ) • cw2 ℂ

end TR23.Geometry
