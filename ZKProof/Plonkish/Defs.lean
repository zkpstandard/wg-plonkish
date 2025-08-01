import Mathlib.Data.Rel
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

import ZKProof.Relations


/-- Geometry of a circuit (either abstract or concrete). -/
public structure Geometry where
  /-- Length of the instance vector. -/
  t : ℕ
  /-- Number of columns for the witness matrix. -/
  m : ℕ+
  /-- Number of rows for the witness matrix. -/
  n : ℕ+
  /-- The number of columns that are fixed. -/
  m_f : Fin (m+1)

namespace Geometry
variable (G : Geometry)

/-- The type of column indices. -/
public abbrev Col := Fin G.m

/-- The type of row indices. -/
public abbrev Row := Fin G.n

/-- The type of input indices. -/
public abbrev Input := Fin G.t

/-- The location of a witness entry. -/
public structure Entry where
  /-- Column number. -/
  i : Fin G.m
  /-- Row number. -/
  j : Fin G.n
deriving DecidableEq

/-- Utility function to construct an `Entry`. -/
public def entry (i : G.Col) (j : G.Row) : G.Entry := { i := i, j := j }

/-- Whether a location is fixed. -/
public def is_fixed (e : G.Entry) := Fin.castSucc e.i < G.m_f

/-- The set of fixed locations. -/
public abbrev FixedEntry := {e : G.Entry // G.is_fixed e}

end Geometry

/-- An abstract Plonkish circuit. -/
public structure AbstractCircuit (F : Type) [Field F] where
  G : Geometry

  /-- The fixed content of the first `m_f` columns. -/
  f (e : G.FixedEntry) : F

  /-- An equivalence relation on witness entries. -/
  E (e e' : G.Entry) : Prop
  Equivalence_E : Equivalence E

  /-- A vector mapping each instance vector entry to an entry in the witness matrix that it is constrained equal to. -/
  S : Vector G.Entry G.t

  /-- The number of custom gates. The default is 0, in which case `p` and `CUS` need not be provided. -/
  U : ℕ := 0
  /-- Multivariate polynomials for custom gates. -/
  p (u : Fin U) : MvPolynomial G.Col F := by intro u; exact Fin.elim0 u
  /-- Rows on which the custom polynomials `p u` are constrained to evaluate to 0. -/
  CUS (u : Fin U) : Set G.Row := by intro u; exact Fin.elim0 u

  /-- The number of lookup tables. The default is 0, in which case `L`, `TAB`, `q` and `LOOK` need not be provided. -/
  V : ℕ := 0
  /-- The number of table columns in the lookup table with index `v`, `TAB v`. -/
  L (v : Fin V) : ℕ+ := by intro v; exact Fin.elim0 v
  /-- Lookup tables `TAB v`, each with a number of tuples in `F^{L v}`. -/
  TAB (v : Fin V) : Set (Vector F (L v)) := by intro v; exact Fin.elim0 v
  /-- Scaling multivariate polynomials for lookup tables. -/
  q (v : Fin V) : Vector (MvPolynomial G.Col F) (L v) := by intro v; exact Fin.elim0 v
  /-- Rows on which the scaling polynomials `q v s` evaluate to some tuple in `TAB v`. -/
  LOOK (v : Fin V) : Set G.Row := by intro v; exact Fin.elim0 v


variable {F : Type} [Field F]

namespace AbstractCircuit
variable (C : AbstractCircuit F)

/-- The type of column indices for an `AbstractCircuit`. -/
public abbrev Col := C.G.Col

/-- The type of row indices for an `AbstractCircuit`. -/
public abbrev Row := C.G.Row

/-- The type of input indices for an `AbstractCircuit`. -/
public abbrev Input := C.G.Input

/-- The witness entry type for an `AbstractCircuit`. -/
public abbrev Entry := C.G.Entry

/-- The set of fixed locations. -/
public abbrev FixedEntry := C.G.FixedEntry

/-- The instance type for an `AbstractCircuit`. -/
public abbrev Instance := Vector F C.G.t

/-- The witness type for an `AbstractCircuit`. -/
public abbrev Witness := C.Entry → F

/-- The relation type for an `AbstractCircuit`. -/
public abbrev Relation := Rel C.Instance C.Witness

/-- The type of polynomials over row vectors. -/
public abbrev RowPoly := MvPolynomial C.Col F

/-- `row_vec w j : C.Col → F` is the witness vector for row `j`. -/
public def row_vec (w : C.Witness) (j : C.Row) :=
  fun (i : C.Col) => w { i := i, j := j }

/-- Evaluate a polynomial on the witness vector for a given row. -/
public def row_eval (w : C.Witness) (j : C.Row) (poly : C.RowPoly) :=
  poly.eval (C.row_vec w j)

/--
The relation for a Plonkish abstract circuit with instance vector `φ`.
We define this as a structure rather than a monolithic `Prop`, to more easily allow
referring to its parts. Lean's type system still allows it to be used as a `Prop`.
-/
public structure R_parts (φ : C.Instance) (w : C.Witness) where
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

public def R : C.Relation := { (φ, w) | C.R_parts φ w }

/--
Polynomial `p` "might use" variable `i` iff any monomial in `p.support` involves `i`.
-/
public def might_use (p : C.RowPoly) (i : C.Col) := ∃ (m : p.support), (m : C.Col →₀ ℕ) i > 0

/--
We say that an abstract cell at location `e` is "constrained" if it appears
in some copy, input, custom, or lookup constraint. Note that fixed cells do
not need to be treated as a special case.
-/
public def constrained (e : C.Entry) :=
    (∃ (e' : C.Entry) (distinct : e ≠ e'), C.E e e')
  ∨ (∃ (k : C.Input), C.S[k] = e)
  ∨ (∃ (u : Fin C.U), e.j ∈ C.CUS u ∧ C.might_use (C.p u) e.i)
  ∨ (∃ (v : Fin C.V) (s : Fin (C.L v)), e.j ∈ C.LOOK v ∧ C.might_use (C.q v)[s] e.i)

end AbstractCircuit
