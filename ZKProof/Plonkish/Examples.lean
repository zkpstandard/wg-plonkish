import Mathlib.Tactic

import ZKProof.Plonkish.Defs


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

def dt_a := G.entry 1 0
def dt_c : G.Entry := G.entry 0 0
def dt_c' : G.FixedEntry := ⟨dt_c, by exact Fin.coe_sub_iff_lt.mp rfl⟩
def dt_in (i : Fin 1) : G.Input := i

variable (F : Type) [Field F]

def dt : AbstractCircuit F := {
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
  S := #v[dt_a]
  -- The value of the fixed entry is `42 : F`.
  f _ := 42
}

/-- Construct a witness. -/
def dt_witness (c a : F) (e : G.Entry) : F := if e = dt_c then c else a

/-- Construct the single valid witness. -/
def dt_valid_witness := dt_witness F 42 42

/--
Completeness of the `dt` example circuit.

Here we show completeness directly by constructing the only valid witness
and showing that it is satisfying for the only valid instance vector.
-/
theorem dt_complete_direct : (#v[42], dt_valid_witness F) ∈ (dt F).R := {
  fixed e := by simp [dt, dt_valid_witness, dt_witness]
  input k := by simp; rfl
  equal e e' := by simp [dt, dt_valid_witness, dt_witness]
}

/--
Soundness of the `dt` example circuit.

We show that any satisfying witness implies `x = 42`.
-/
theorem dt_knowledge_sound_direct (x : F)
    (sat : Satisfying (dt F).R #v[x]) : x = 42 :=
by
  let st := sat.satisfied -- the Plonkish statement
  calc x = sat.w dt_a := symm <| st.input (dt_in 0)
       _ = sat.w dt_c := st.equal dt_a dt_c rfl
       _ = 42         := st.fixed dt_c'

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
      input k := by rw [htrans, show k = dt_in 0 by ext; simp]
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
      let st := sat'.satisfied -- the Plonkish statement
      calc x = x'[0]       := by simp_all only [x]; rfl
           _ = sat'.w dt_a := symm <| st.input (dt_in 0)
           _ = sat'.w dt_c := st.equal dt_a dt_c rfl
           _ = 42          := st.fixed dt_c'
  }
