import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace TR23

abbrev CWCoord := Fin 9

/-- Distinguished coordinate of the small Coppersmith--Winograd tensor. -/
def cwHead (i : CWCoord) : ℤ := if i = 0 then 1 else 0

/-- Sum of the eight non-distinguished basis vectors. -/
def cwSum (i : CWCoord) : ℤ := if i = 0 then 0 else 1

/-- The j-th non-distinguished basis vector. -/
def cwBasis (j : Fin 8) (i : CWCoord) : ℤ := if i.val = j.val + 1 then 1 else 0

/-- The usual small CW tensor with eight non-distinguished coordinates. -/
def cw8 (i j k : CWCoord) : ℤ :=
  (if i = 0 ∧ j = k ∧ j ≠ 0 then 1 else 0) +
  (if j = 0 ∧ i = k ∧ i ≠ 0 then 1 else 0) +
  (if k = 0 ∧ i = j ∧ i ≠ 0 then 1 else 0)

/-- Coefficient of t in the regular part of the ten-term family. -/
def cwRemainder (i j k : CWCoord) : ℤ :=
  (if i = j ∧ j = k ∧ i ≠ 0 then 1 else 0) -
  (cwHead i * cwSum j * cwSum k +
   cwSum i * cwHead j * cwSum k +
   cwSum i * cwSum j * cwHead k)

/-- Scalar coefficients of the ten pure tensors, with t nonzero in the identity. -/
noncomputable def cwScalar (t : ℂ) (r : Fin 10) : ℂ :=
  if r.val < 8 then (t ^ 2)⁻¹
  else if r.val = 8 then -(t ^ 3)⁻¹
  else (t ^ 3)⁻¹ - 8 * (t ^ 2)⁻¹

/-- The same coordinate vector is used in each of the three tensor modes. -/
noncomputable def cwVector (t : ℂ) (r : Fin 10) (i : CWCoord) : ℂ :=
  if h : r.val < 8 then (cwHead i : ℂ) + t * (cwBasis ⟨r.val, h⟩ i : ℂ)
  else if r.val = 8 then (cwHead i : ℂ) + t ^ 2 * (cwSum i : ℂ)
  else (cwHead i : ℂ)

/-- The actual sum of ten pure tensors, expressed in coordinates. -/
noncomputable def cwFamily (t : ℂ) (i j k : CWCoord) : ℂ :=
  ∑ r : Fin 10, cwScalar t r * cwVector t r i * cwVector t r j * cwVector t r k

/-- The regular polynomial obtained after cancellation of all poles. -/
noncomputable def cwRegular (t : ℂ) (i j k : CWCoord) : ℂ :=
  (cw8 i j k : ℂ) + t * (cwRemainder i j k : ℂ) -
  t ^ 3 * (cwSum i : ℂ) * (cwSum j : ℂ) * (cwSum k : ℂ)

/-- Only the explicit coefficient identity is included here. -/
structure CWCertificate : Prop where
  identity : ∀ t : ℂ, t ≠ 0 → ∀ i j k : CWCoord, cwFamily t i j k = cwRegular t i j k
  constant_term : ∀ i j k : CWCoord, cwRegular 0 i j k = (cw8 i j k : ℂ)

end TR23
