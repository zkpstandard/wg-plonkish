import Mathlib.Data.Rel
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

import ZKProof.Plonkish.Defs


/--
A concrete Plonkish circuit, as defined in the Plonkish Backend Optimizations document.

The key difference from `AbstractCircuit` is the addition of offsets: custom and lookup
constraint polynomials act on an extended row vector
`w_j[(i, k)] = w[i, j + offsets[k]]`
that can access witness entries at offset rows.

A `ConcreteCircuit` must be well-formed: enabled custom and lookup constraint rows must
not cause out-of-bounds offset accesses. This is enforced by the `wf_CUS` and `wf_LOOK`
fields, matching the specification's requirement that "it is an error if a concrete circuit
involves such accesses for enabled source rows."
-/
public structure ConcreteCircuit (F : Type) [Field F] where
  G : Geometry

  /-- Number of distinct offsets. -/
  d : ℕ
  /-- The offsets enabling optimizations on the circuit structure. -/
  offsets : Vector ℤ d

  /-- The fixed content of the first `m_f` columns. -/
  f (e : G.FixedEntry) : F

  /-- An equivalence relation on witness entries. -/
  E (e e' : G.Entry) : Prop
  Equivalence_E : Equivalence E

  /-- A vector mapping each instance vector entry to a witness matrix entry. -/
  S : Vector G.Entry G.t

  /-- The number of custom gates. The default is 0, in which case `p` and `CUS` need not
      be provided. -/
  U : ℕ := 0
  /-- Multivariate polynomials for custom gates, over `Col × Fin d` variables
      (the extended row vector indices). -/
  p (u : Fin U) : MvPolynomial (G.Col × Fin d) F := by intro u; exact Fin.elim0 u
  /-- Rows on which the custom polynomials `p u` are constrained to evaluate to 0. -/
  CUS (u : Fin U) : Set G.Row := by intro u; exact Fin.elim0 u

  /-- The number of lookup tables. The default is 0, in which case `L`, `TAB`, `q` and
      `LOOK` need not be provided. -/
  V : ℕ := 0
  /-- The number of table columns in the lookup table with index `v`, `TAB v`. -/
  L (v : Fin V) : ℕ+ := by intro v; exact Fin.elim0 v
  /-- Lookup tables `TAB v`, each with a number of tuples in `F^{L v}`. -/
  TAB (v : Fin V) : Set (Vector F (L v)) := by intro v; exact Fin.elim0 v
  /-- Scaling multivariate polynomials for lookup tables, over `Col × Fin d` variables. -/
  q (v : Fin V) : Vector (MvPolynomial (G.Col × Fin d) F) (L v) := by intro v; exact Fin.elim0 v
  /-- Rows on which the scaling polynomials `q v s` evaluate to some tuple in `TAB v`. -/
  LOOK (v : Fin V) : Set G.Row := by intro v; exact Fin.elim0 v

  /-- Well-formedness: enabled custom constraint rows have in-bounds offset accesses. -/
  wf_CUS : ∀ (u : Fin U) (j : G.Row), j ∈ CUS u → ∀ (k : Fin d),
    0 ≤ (j.val : ℤ) + offsets[k] ∧ (j.val : ℤ) + offsets[k] < ((G.n : ℕ) : ℤ) :=
    by intro u; exact Fin.elim0 u
  /-- Well-formedness: enabled lookup constraint rows have in-bounds offset accesses. -/
  wf_LOOK : ∀ (v : Fin V) (j : G.Row), j ∈ LOOK v → ∀ (k : Fin d),
    0 ≤ (j.val : ℤ) + offsets[k] ∧ (j.val : ℤ) + offsets[k] < ((G.n : ℕ) : ℤ) :=
    by intro v; exact Fin.elim0 v


variable {F : Type} [Field F]

namespace ConcreteCircuit
variable (C : ConcreteCircuit F)

public abbrev Col := C.G.Col
public abbrev Row := C.G.Row
public abbrev Input := C.G.Input
public abbrev Entry := C.G.Entry
public abbrev FixedEntry := C.G.FixedEntry
public abbrev Instance := Vector F C.G.t
public abbrev Witness := C.Entry → F
public abbrev Relation := Rel C.Instance C.Witness
public abbrev ExtVar := C.Col × Fin C.d
public abbrev ExtPoly := MvPolynomial C.ExtVar F

public abbrev OffsetInBounds (j : C.Row) (k : Fin C.d) : Prop :=
  0 ≤ (j.val : ℤ) + C.offsets[k] ∧ (j.val : ℤ) + C.offsets[k] < ((C.G.n : ℕ) : ℤ)

public def offsetRow (j : C.Row) (k : Fin C.d) (h : C.OffsetInBounds j k) : C.Row :=
  ⟨((j.val : ℤ) + C.offsets[k]).toNat, by omega⟩

public def ext_row_vec (w : C.Witness) (j : C.Row)
    (hj : ∀ k : Fin C.d, C.OffsetInBounds j k) : C.ExtVar → F :=
  fun (i, k) => w { i := i, j := C.offsetRow j k (hj k) }

public def ext_row_eval (w : C.Witness) (j : C.Row)
    (hj : ∀ k : Fin C.d, C.OffsetInBounds j k) (poly : C.ExtPoly) : F :=
  poly.eval (C.ext_row_vec w j hj)

public structure R_parts (φ : C.Instance) (w : C.Witness) where
  fixed (e : C.FixedEntry) : w e = C.f e
  input (k : C.Input) : w C.S[k] = φ[k]
  equal (e e' : C.Entry) (equated : C.E e e') : w e = w e'
  custom (u : Fin C.U) (j : C.CUS u) :
    C.ext_row_eval w j (C.wf_CUS u j j.property) (C.p u) = 0 :=
    by intro u; exact Fin.elim0 u
  lookup (v : Fin C.V) (j : C.LOOK v) :
    (C.q v).map (C.ext_row_eval w j (C.wf_LOOK v j j.property)) ∈ C.TAB v :=
    by intro v; exact Fin.elim0 v

public def R : C.Relation := { (φ, w) | C.R_parts φ w }

end ConcreteCircuit
