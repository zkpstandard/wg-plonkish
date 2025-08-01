import Mathlib.Data.Rel
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

import ZKProof.Relations


/-- The location of a witness entry. -/
structure Location (m n : ℕ+) where
  /-- Column number. -/
  i : Fin m
  /-- Row number. -/
  j : Fin n
deriving DecidableEq

/-- Utility function to construct a `Location`. -/
def entry {m n : ℕ+} (i : Fin m) (j : Fin n) : Location m n := { i := i, j := j }

/-- An abstract Plonkish circuit. -/
structure AbstractCircuit (F : Type) [Field F] where
  /-- Length of the instance vector. -/
  t : ℕ

  /-- Number of columns for the witness matrix. -/
  m : ℕ+
  /-- Number of rows for the witness matrix. -/
  n : ℕ+

  /-- An equivalence relation on witness entries. -/
  E (e e' : Location m n) : Prop
  Equivalence_E : Equivalence E

  /-- A vector mapping each instance vector entry to an entry in the witness matrix that it is constrained equal to. -/
  S : Vector (Location m n) t

  /-- The number of columns that are fixed. -/
  m_f : Fin (m+1)
  /-- Whether a location is fixed. -/
  is_fixed (e : Location m n) := Fin.castSucc e.i < m_f
  /-- The fixed content of the first `m_f` columns. -/
  f (e : {e : Location m n // is_fixed e}) : F

  /-- The number of custom gates. The default is 0, in which case `p` and `CUS` need not be provided. -/
  U : ℕ := 0
  /-- Multivariate polynomials for custom gates. -/
  p (u : Fin U) : MvPolynomial (Fin m) F := by intro u; exact Fin.elim0 u
  /-- Rows on which the custom polynomials `p u` are constrained to evaluate to 0. -/
  CUS (u : Fin U) : Set (Fin n) := by intro u; exact Fin.elim0 u

  /-- The number of lookup tables. The default is 0, in which case `L`, `TAB`, `q` and `LOOK` need not be provided. -/
  V : ℕ := 0
  /-- The number of table columns in the lookup table with index `v`, `TAB v`. -/
  L (v : Fin V) : ℕ+ := by intro v; exact Fin.elim0 v
  /-- Lookup tables `TAB v`, each with a number of tuples in `F^{L v}`. -/
  TAB (v : Fin V) : Set (Vector F (L v)) := by intro v; exact Fin.elim0 v
  /-- Scaling multivariate polynomials for lookup tables. -/
  q (v : Fin V) : Vector (MvPolynomial (Fin m) F) (L v) := by intro v; exact Fin.elim0 v
  /-- Rows on which the scaling polynomials `q v s` evaluate to some tuple in `TAB v`. -/
  LOOK (v : Fin V) : Set (Fin n) := by intro v; exact Fin.elim0 v


variable {F : Type} [Field F]

namespace AbstractCircuit
variable (C : AbstractCircuit F)

/-- The type of column indices for an `AbstractCircuit`. -/
abbrev Col := Fin C.m

/-- The type of row indices for an `AbstractCircuit`. -/
abbrev Row := Fin C.n

/-- The type of input indices for an `AbstractCircuit`. -/
abbrev Input := Fin C.t

/-- The witness entry type for an `AbstractCircuit`. -/
abbrev Entry := Location C.m C.n

/-- The set of fixed locations. -/
abbrev FixedEntry := {e : C.Entry // C.is_fixed e}

/-- The instance type for an `AbstractCircuit`. -/
abbrev Instance := Vector F C.t

/-- The witness type for an `AbstractCircuit`. -/
abbrev Witness := C.Entry → F

/-- The relation type for an `AbstractCircuit`. -/
abbrev Relation := Rel C.Instance C.Witness

/-- The type of polynomials over row vectors. -/
abbrev RowPoly := MvPolynomial C.Col F

/-- `row_vec w j : C.Col → F` is the witness vector for row `j`. -/
def row_vec (w : C.Witness) (j : C.Row) :=
  fun (i : C.Col) => w { i := i, j := j }

/-- Evaluate a polynomial on the witness vector for a given row. -/
def row_eval (w : C.Witness) (j : C.Row) (poly : C.RowPoly) :=
  poly.eval (C.row_vec w j)

/--
The relation for a Plonkish abstract circuit with instance vector `φ`.
We define this as a structure rather than a monolithic `Prop`, to more easily allow
referring to its parts. Lean's type system still allows it to be used as a `Prop`.
-/
structure R_parts (φ : C.Instance) (w : C.Witness) where
  /-- Semantics of fixed constraints. -/
  fixed (e : C.FixedEntry) : w e = C.f e

  /-- Semantics of copy constraints for instance entries. -/
  input (k : C.Input) : w C.S[k] = φ[k]
  /-- Semantics of copy constraints for witness entries. -/
  equal (e e' : C.Entry) (equated : C.E e e') : w e = w e'

  /-- Semantics of custom constraints. -/
  custom (u : Fin C.U) (j : C.CUS u) : C.row_eval w j (C.p u) = 0 := by intro u; exact Fin.elim0 u

  /-- Semantics of lookup constraints. -/
  lookup (v : Fin C.V) (j : C.LOOK v) : (C.q v).map (C.row_eval w j) ∈ C.TAB v := by intro v; exact Fin.elim0 v

def R : C.Relation := { (φ, w) | C.R_parts φ w }

/-- Use a fixed constraint. -/
lemma use_fixed {x : C.Instance} (sat : Satisfying C.R x) (e : C.FixedEntry)
    : sat.w e = C.f e := by
  exact sat.satisfied.fixed e

/-- Use an input constraint. -/
lemma use_input {x : C.Instance} (sat : Satisfying C.R x) (k : C.Input)
    : x[k] = sat.w C.S[k] := by
  exact symm <| sat.satisfied.input k

/-- Use an equality constraint. -/
lemma use_equal {x : C.Instance} (sat : Satisfying C.R x) (e e' : C.Entry) (equiv : C.E e e')
    : sat.w e = sat.w e' := by
  exact sat.satisfied.equal e e' equiv

end AbstractCircuit
