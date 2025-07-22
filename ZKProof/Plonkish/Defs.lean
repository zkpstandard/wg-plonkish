import Mathlib.Data.Rel
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Function.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic

import ZKProof.Relations

variable (F : Type) [Field F]


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
structure AbstractCircuit where
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

namespace AbstractCircuit
variable (C : AbstractCircuit F)

/-- The witness entry type for an `AbstractCircuit`. -/
abbrev Entry := Location C.m C.n

/-- The set of fixed locations. -/
abbrev FixedEntry := {e : Location C.m C.n // C.is_fixed e}

/-- The instance type for an `AbstractCircuit`. -/
abbrev Instance := Vector F C.t

/-- The witness type for an `AbstractCircuit`. -/
abbrev Witness := C.Entry → F

/-- The relation type for an `AbstractCircuit`. -/
abbrev Relation := Rel C.Instance C.Witness

/-- `row_vec w j : Fin m → F` is the witness vector for row `j`. -/
def row_vec (w : C.Witness) (j : Fin C.n) :=
  fun (i : Fin C.m) => w { i := i, j := j }

/-- Evaluate a polynomial on the witness vector for a given row. -/
def row_eval (w : C.Witness) (j : Fin C.n) (poly : MvPolynomial (Fin C.m) F) :=
  poly.eval (C.row_vec F w j)

/--
The relation for a Plonkish abstract circuit with instance vector `φ`.
We define this as a structure rather than a monolithic `Prop`, to more easily allow
referring to its parts. Lean's type system still allows it to be used as a `Prop`.
-/
structure R_parts (φ : C.Instance) (w : C.Witness) where
  /-- Semantics of fixed constraints. -/
  fixed (e : C.FixedEntry) : w e = C.f e

  /-- Semantics of copy constraints for instance entries. -/
  input (k : Fin C.t) : w C.S[k] = φ[k]
  /-- Semantics of copy constraints for witness entries. -/
  equal (e e' : C.Entry) (equated : C.E e e') : w e = w e'

  /-- Semantics of custom constraints. -/
  custom (u : Fin C.U) (j : C.CUS u) : C.row_eval F w j (C.p u) = 0 := by intro u; exact Fin.elim0 u

  /-- Semantics of lookup constraints. -/
  lookup (v : Fin C.V) (j : C.LOOK v) : (C.q v).map (C.row_eval F w j) ∈ C.TAB v := by intro v; exact Fin.elim0 v

def R : C.Relation := { (φ, w) | C.R_parts F φ w }

/-- Use a fixed constraint. -/
lemma use_fixed {x : C.Instance} (sat : Satisfying C.R x) (e : C.FixedEntry)
    : sat.w e = C.f e := by
  obtain ⟨ fixed ⟩ := sat.satisfied
  rw [fixed e]

/-- Use an input constraint. -/
lemma use_input {x : C.Instance} (sat : Satisfying C.R x) (k : Fin C.t)
    : x[k] = sat.w C.S[k] := by
  obtain ⟨ _, input ⟩ := sat.satisfied
  rw [input k]

/-- Use an equality constraint. -/
lemma use_equal {x : C.Instance} (sat : Satisfying C.R x) (e e' : C.Entry) (equiv : C.E e e')
    : sat.w e = sat.w e' := by
  obtain ⟨ _, _, equal ⟩ := sat.satisfied
  rw [equal e e']
  exact equiv

end AbstractCircuit


namespace Example

/-
A circuit that constrains a single field element to 42.
This demonstrates fixed, input, and equality constraints, but not custom gates or lookups.

| fixed  | advice |
|--------|--------|
| c = 42 | a = x₀ |
-/

def dt_entry (i : Fin (2 : ℕ+)) (j : Fin (1 : ℕ+)) := entry i j
def dt_a := dt_entry 1 0
def dt_c := dt_entry 0 0

def dt : AbstractCircuit F := {
  -- The instance is a single field element.
  t := 1
  -- There are two columns.
  m := 2
  -- There is one row.
  n := 1
  -- All entries are equal.
  E _ _ := true
  -- E is an equivalence relation.
  Equivalence_E := {
    refl := by intro x; simp only
    symm := by intro x; simp only [imp_self, implies_true]
    trans := by intro x; simp only [imp_self, implies_true]
  }
  -- The instance value is placed at `a`.
  S := #v[dt_a]
  -- There is one fixed column. --/
  m_f := 1
  -- The value of the fixed entry is `42 : F`.
  f _ := 42
}

/-- Construct a witness. -/
def dt_witness (c a : F) (loc : (dt F).Entry) : F := if loc = dt_c then c else a

/-- Construct the single valid witness. -/
def dt_valid_witness := dt_witness F 42 42

/--
Completeness of the `dt` example circuit.

Here we show completeness directly by constructing the only valid witness
and showing that it is satisfying for the only valid instance vector.
-/
theorem dt_complete_direct : (#v[42], dt_valid_witness F) ∈ (dt F).R F := {
  fixed e := by simp [dt, dt_valid_witness, dt_witness]
  input k := by simp; rfl
  equal e e' := by simp [dt, dt_valid_witness, dt_witness]
}

/--
Soundness of the `dt` example circuit.

We show that any satisfying witness implies `x = 42`.
-/
theorem dt_knowledge_sound_direct (x : F)
    (sat : Satisfying ((dt F).R F) #v[x]) : x = 42 :=
by
  calc x = sat.w dt_a := (dt F).use_input F sat (0 : Fin 1)
       _ = sat.w dt_c := (dt F).use_equal F sat dt_a dt_c rfl
       _ = 42         := (dt F).use_fixed F sat ⟨dt_c, by simp [dt, dt_c, dt_entry, entry]⟩

/--
An alternative is to show that a refinement from an abstract relation is complete and sound.
The abstract relation is very simple indeed.
-/
def abstract_dt := { (x, _) : F × Unit | x = 42 }

def dt_refinement : Refinement (abstract_dt F) (dt F).R where
  trans := {
    toFun (x : F) : Vector F 1 := #v[x]
    invFun (v : Vector F 1) : F := v[0]
    left_inv := by simp [Function.LeftInverse]
    right_inv := by intro x; simp; ext <;> simp; simp_all
  }

def dt_complete_by_refinement : Complete (dt_refinement F) :=
 fun (x : F) (sat : Satisfying (abstract_dt F) x) => by
  have htrans : (dt_refinement F).trans x = #v[x] := by rfl
  let hsat := sat.satisfied; unfold abstract_dt at hsat
  exact {
    w := dt_valid_witness F
    satisfied := {
      fixed e := by simp [dt, dt_valid_witness, dt_witness]
      input k := by rw [htrans, show k = (0 : Fin 1) by ext; simp]
                    simp [dt, dt_valid_witness, dt_witness]
                    exact hsat.symm
      equal e e' := by simp [dt, dt_valid_witness, dt_witness]
    }
  }

def dt_knowledge_sound_by_refinement : KnowledgeSound (dt_refinement F) :=
  fun (x' : Vector F 1) (sat' : Satisfying (dt F).R x') => {
    w := (),
    satisfied := by
      let x := (dt_refinement F).trans.symm x'
      calc x = x'[0]       := by simp_all only [x]; rfl
           _ = sat'.w dt_a := (dt F).use_input F sat' (0 : Fin 1)
           _ = sat'.w dt_c := (dt F).use_equal F sat' dt_a dt_c rfl
           _ = 42          := (dt F).use_fixed F sat' ⟨dt_c, by simp [dt, dt_c, dt_entry, entry]⟩
  }

end Example
