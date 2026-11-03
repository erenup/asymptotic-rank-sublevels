import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace TR23.Exchange

abbrev BitPair := ZMod 2 × ZMod 2
abbrev Group64 := Fin 3 → BitPair

def shift : Group64 := fun _ => (1, 0)

def mainSet : Finset Group64 :=
  Finset.univ.filter fun g => ∀ j, g j ≠ (0, 0)

def innerSet : Finset Group64 :=
  mainSet.filter fun g => g + shift ∈ mainSet

def residualSet : Finset Group64 :=
  Finset.univ.filter fun g => g ∉ mainSet ∧ g + shift ∉ mainSet

abbrev MainCoord := {g : Group64 // g ∈ mainSet}
abbrev InnerCoord := {g : Group64 // g ∈ innerSet}
abbrev ResidualCoord := {g : Group64 // g ∈ residualSet}
abbrev SourceCoord := Group64 ⊕ (Unit ⊕ InnerCoord)
abbrev TightCoord := Unit ⊕ ResidualCoord
abbrev TargetCoord := MainCoord ⊕ TightCoord
abbrev Triple (α : Type*) := (α × α) × α

def pairCode (g : BitPair) : ℕ := g.1.val + 2 * g.2.val
def groupCode (g : Group64) : ℕ := ∑ j : Fin 3, 4 ^ j.val * pairCode (g j)

/-- Nonzero two-bit symbols 1,2,3 are relabelled as 0,1,2. -/
def mainDigits (g : MainCoord) : Fin 3 → Fin 3 :=
  fun j => Fin.ofNat 3 (pairCode (g.val j) - 1)

def permutationCoefficient (i j k : Fin 3) : ℤ :=
  if i ≠ j ∧ j ≠ k ∧ i ≠ k then 1 else 0

def bitSign (x y : ZMod 2) : ℤ := if x = 1 ∧ y = 1 then -1 else 1
def pairCharacter (x y : BitPair) : ℤ :=
  bitSign x.1 y.1 * bitSign x.2 y.2
def character (x y : Group64) : ℤ := ∏ j : Fin 3, pairCharacter (x j) (y j)

def targetMask : TargetCoord → Group64
  | .inl g => g.val
  | .inr (.inl _) => shift
  | .inr (.inr g) => g.val

def rowDegree : TargetCoord → ℤ
  | .inl _ => 0
  | .inr (.inl _) => -2
  | .inr (.inr _) => 1

/-- Integer part of the common Laurent row map in all three modes. -/
def rowMap (a : TargetCoord) : SourceCoord → ℤ
  | .inl g => character (targetMask a) g
  | .inr (.inl _) => match a with
      | .inr (.inl _) => -1
      | _ => 0
  | .inr (.inr i) => match a with
      | .inl g => if g.val = i.val then 1 else 0
      | _ => 0

/-- The integral scaling of D64 direct-sum paired C8: auxiliary entries are 64. -/
def sourceCoefficient : SourceCoord → SourceCoord → SourceCoord → ℤ
  | .inl g, .inl h, .inl k => if g = h ∧ h = k then 1 else 0
  | .inr (.inl _), .inr (.inr i), .inr (.inr j) =>
      if i.val + j.val = shift then 64 else 0
  | .inr (.inr i), .inr (.inl _), .inr (.inr j) =>
      if i.val + j.val = shift then 64 else 0
  | .inr (.inr i), .inr (.inr j), .inr (.inl _) =>
      if i.val + j.val = shift then 64 else 0
  | _, _, _ => 0

/-- Full coordinate contraction, before using its sparse source support. -/
def contraction (a b c : TargetCoord) : ℤ :=
  ∑ u : SourceCoord, ∑ v : SourceCoord, ∑ w : SourceCoord,
    sourceCoefficient u v w * rowMap a u * rowMap b v * rowMap c w

/-- A factored form of the same contraction, with at most 64+3*8*8 terms. -/
def sparseContraction (a b c : TargetCoord) : ℤ :=
  (∑ g : Group64, character (targetMask a) g *
    character (targetMask b) g * character (targetMask c) g) +
  64 * ∑ i : InnerCoord, ∑ j : InnerCoord,
    if i.val + j.val = shift then
      rowMap a (.inr (.inl ())) * rowMap b (.inr (.inr i)) * rowMap c (.inr (.inr j)) +
      rowMap a (.inr (.inr i)) * rowMap b (.inr (.inl ())) * rowMap c (.inr (.inr j)) +
      rowMap a (.inr (.inr i)) * rowMap b (.inr (.inr j)) * rowMap c (.inr (.inl ()))
    else 0

def laurentCoefficient (degree : ℤ) (a b c : TargetCoord) : ℤ :=
  if degree = rowDegree a + rowDegree b + rowDegree c then contraction a b c else 0

def tightCoefficient : TightCoord → TightCoord → TightCoord → ℤ
  | .inl _, .inr r, .inr s => if r.val + s.val = shift then 1 else 0
  | .inr r, .inl _, .inr s => if r.val + s.val = shift then 1 else 0
  | .inr r, .inr s, .inl _ => if r.val + s.val = shift then 1 else 0
  | _, _, _ => 0

/-- P cubed and paired C18 on disjoint blocks, each with coefficient one. -/
def targetCoefficient : TargetCoord → TargetCoord → TargetCoord → ℤ
  | .inl a, .inl b, .inl c =>
      ∏ j : Fin 3, permutationCoefficient (mainDigits a j) (mainDigits b j) (mainDigits c j)
  | .inr a, .inr b, .inr c => tightCoefficient a b c
  | _, _, _ => 0

/-- Integer labels in the certificate, indexed by the two-bit integer encoding. -/
def residualWeightTable : Fin 64 → ℤ :=
  ![0, 1, 0, 0, 2, 3, 4, 5, 0, 6, 0, 0, 0, 7, 0, 0,
    -3, -2, -5, -4, -1, 0, 0, 0, -7, 0, 0, 0, -6, 0, 0, 0,
    0, 8, 0, 0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, -9, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def tightWeight : TightCoord → ℤ
  | .inl _ => 0
  | .inr r => residualWeightTable (Fin.ofNat 64 (groupCode r.val))

def tightSupport : Finset (Triple TightCoord) :=
  Finset.univ.filter fun p => tightCoefficient p.1.1 p.1.2 p.2 = 1

def tripleCoord {α : Type*} (p : Triple α) (mode : Fin 3) : α :=
  ![p.1.1, p.1.2, p.2] mode

/-- Finite coefficient identities only; no asymptotic rank or spectral theorem. -/
structure ExchangeCertificate : Prop where
  group_card : Fintype.card Group64 = 64
  set_cards : mainSet.card = 27 ∧ innerSet.card = 8 ∧ residualSet.card = 18
  dimensions : Fintype.card SourceCoord = 73 ∧ Fintype.card TargetCoord = 46
  inner_translation : ∀ g : Group64, g ∈ innerSet ↔ g + shift ∈ innerSet
  residual_translation : ∀ g : Group64, g ∈ residualSet ↔ g + shift ∈ residualSet
  shift_fixed_point_free : ∀ g : Group64, g + shift ≠ g
  digit_bijection : Function.Bijective mainDigits
  walsh : ∀ x y z : Group64,
    (∑ g : Group64, character x g * character y g * character z g) =
      if x + y + z = 0 then 64 else 0
  contraction_factorization : ∀ a b c, contraction a b c = sparseContraction a b c
  negative_coefficients : ∀ n : ℤ, n < 0 → ∀ a b c, laurentCoefficient n a b c = 0
  constant_coefficient : ∀ a b c,
    laurentCoefficient 0 a b c = 64 * targetCoefficient a b c
  upper_degree : ∀ n : ℤ, 3 < n → ∀ a b c, laurentCoefficient n a b c = 0
  tight_dimension : Fintype.card TightCoord = 19
  tight_injective : Function.Injective tightWeight
  tight_support_card : tightSupport.card = 54
  tight_weight_sum : ∀ p ∈ tightSupport,
    tightWeight p.1.1 + tightWeight p.1.2 + tightWeight p.2 = 0
  tight_marginals : ∀ mode : Fin 3, ∀ x : TightCoord,
    (tightSupport.filter fun p => tripleCoord p mode = x).card =
      if x = .inl () then 18 else 2

end TR23.Exchange
