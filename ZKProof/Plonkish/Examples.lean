import Mathlib.Tactic

import ZKProof.Plonkish.Defs

namespace dt

/-
A circuit that constrains a single field element to 42.
This demonstrates fixed, input, and equality constraints, but not custom gates or lookups.

| fixed  | advice |
|--------|--------|
| c = 42 | a = x₀ |
-/

def G : Geometry := {
  -- The instance is a single field element.
  t := 1
  -- There are two columns.
  m := 2
  -- There is one row.
  n := 1
  -- There is one fixed column. --/
  m_f := 1
}

def var_a := G.entry 1 0
def var_c : G.Entry := G.entry 0 0
def var_c_fixed : G.FixedEntry := ⟨var_c, by exact Fin.coe_sub_iff_lt.mp rfl⟩
def input (i : Fin 1) : G.Input := i

variable (F : Type) [Field F]

def C : AbstractCircuit F := {
  -- Geometry of this circuit.
  G := G
  -- All entries are equal.
  E _ _ := true
  -- E is an equivalence relation.
  Equivalence_E := {
    refl := by intro x; simp only
    symm := by intro x; simp only [imp_self, implies_true]
    trans := by intro x; simp only [imp_self, implies_true]
  }
  -- The instance value is placed at `a`.
  S := #v[var_a]
  -- The value of the fixed entry is `42 : F`.
  f _ := 42
}

/-- Construct a witness. -/
def witness (c a : F) (e : G.Entry) : F := if e = var_c then c else a

/-- Construct the single valid witness. -/
def valid_witness := witness F 42 42

/--
Completeness of the `dt` example circuit.

Here we show completeness directly by constructing the only valid witness
and showing that it is satisfying for the only valid instance vector.
-/
theorem complete_direct : (#v[42], valid_witness F) ∈ (C F).R := {
  fixed e := by simp [C, valid_witness, witness]
  input k := by simp; rfl
  equal e e' := by simp [C, valid_witness, witness]
}

/--
Soundness of the `dt` example circuit.

We show that any satisfying witness implies `x = 42`.
-/
theorem knowledge_sound_direct (x : F)
    (sat : Satisfying (C F).R #v[x]) : x = 42 :=
by
  let st := sat.satisfied -- the Plonkish statement
  calc x = sat.w var_a := symm <| st.input (input 0)
       _ = sat.w var_c := st.equal var_a var_c rfl
       _ = 42          := st.fixed var_c_fixed

/--
An alternative is to show that a refinement from an abstract relation is complete and sound.
The abstract relation is very simple indeed.
-/
def abstract_C := { (x, _) : F × Unit | x = 42 }

def refinement : Refinement (abstract_C F) (C F).R where
  trans := {
    toFun (x : F) : Vector F 1 := #v[x]
    invFun (v : Vector F 1) : F := v[0]
    left_inv := by simp [Function.LeftInverse]
    right_inv := by intro x; simp; ext <;> simp; simp_all
  }

def complete_by_refinement : Complete (refinement F) :=
 fun (x : F) (sat : Satisfying (abstract_C F) x) => by
  have htrans : (refinement F).trans x = #v[x] := by rfl
  let hsat := sat.satisfied; unfold abstract_C at hsat
  exact {
    w := valid_witness F
    satisfied := {
      fixed e := by simp [C, valid_witness, witness]
      input k := by rw [htrans, show k = input 0 by ext; simp]
                    simp [C, valid_witness, witness]
                    exact hsat.symm
      equal e e' := by simp [C, valid_witness, witness]
    }
  }

def knowledge_sound_by_refinement : KnowledgeSound (refinement F) :=
  fun (x' : Vector F 1) (sat' : Satisfying (C F).R x') => {
    w := (),
    satisfied := by
      let x := (refinement F).trans.symm x'
      let st := sat'.satisfied -- the Plonkish statement
      calc x = x'[0]       := by simp_all only [x]; rfl
           _ = sat'.w var_a := symm <| st.input (input 0)
           _ = sat'.w var_c := st.equal var_a var_c rfl
           _ = 42           := st.fixed var_c_fixed
  }

end dt
