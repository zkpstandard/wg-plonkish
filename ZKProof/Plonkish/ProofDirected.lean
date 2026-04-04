import Mathlib.Tactic

import ZKProof.Plonkish.Defs
import ZKProof.Plonkish.Examples

/-!
# Proof-directed circuit construction

Issue #49: construct the circuit BY completing the correctness proofs,
rather than specifying it independently and then proving it correct.

A `calc`-style knowledge soundness proof makes explicit which constraints
it depends on.  We formalize the constraint footprint as `ConstraintSpec`,
synthesize a circuit from it via `circuit_of_spec`, prove general transfer
theorems, and demonstrate the full round-trip on the `dt` example.
-/

/-! ## Constraint specification -/

structure ConstraintSpec (G : Geometry) where
  fixed_entries : Set G.FixedEntry
  input_indices : Set G.Input
  copy_pairs : Set (G.Entry × G.Entry)

namespace ConstraintSpec

def union {G : Geometry} (s₁ s₂ : ConstraintSpec G) : ConstraintSpec G where
  fixed_entries := s₁.fixed_entries ∪ s₂.fixed_entries
  input_indices := s₁.input_indices ∪ s₂.input_indices
  copy_pairs := s₁.copy_pairs ∪ s₂.copy_pairs

end ConstraintSpec

/-! ## Annotated constraint accessors -/

section Accessors
variable {F : Type} [Field F] {C : AbstractCircuit F} {φ : C.Instance} {w : C.Witness}

def use_fixed (sat : C.R_parts φ w) (e : C.G.FixedEntry) : w e.val = C.f e :=
  sat.fixed e

def use_input (sat : C.R_parts φ w) (k : C.Input) : w C.S[k] = φ[k] :=
  sat.input k

def use_equal (sat : C.R_parts φ w) (e e' : C.G.Entry) (h : C.E e e') : w e = w e' :=
  sat.equal e e' h

end Accessors

/-! ## Circuit synthesis -/

/-- Synthesize a circuit from base data and a constraint spec.
    `E` is the equivalence closure of the specified copy pairs. -/
noncomputable def circuit_of_spec {F : Type} [Field F] (G : Geometry)
    (f : G.FixedEntry → F) (S : Vector G.Entry G.t)
    (spec : ConstraintSpec G) : AbstractCircuit F where
  G := G
  f := f
  S := S
  E e e' := Relation.EqvGen (fun a b => (a, b) ∈ spec.copy_pairs) e e'
  Equivalence_E := Relation.EqvGen.is_equivalence _

/-! ## General transfer theorems -/

section Transfer
variable {F : Type} [Field F]

theorem eqvGen_sub_equiv {C : AbstractCircuit F}
    {r : C.G.Entry → C.G.Entry → Prop}
    (h_sub : ∀ e e', r e e' → C.E e e') :
    ∀ e e', Relation.EqvGen r e e' → C.E e e' := by
  intro e e' h
  induction h with
  | rel x y hr => exact h_sub x y hr
  | refl x => exact C.Equivalence_E.refl x
  | symm _ _ _ ih => exact C.Equivalence_E.symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact C.Equivalence_E.trans ih₁ ih₂

theorem witness_respects_eqvGen {G : Geometry} {F : Type}
    {w : G.Entry → F} {r : G.Entry → G.Entry → Prop}
    (h : ∀ e e', r e e' → w e = w e') :
    ∀ e e', Relation.EqvGen r e e' → w e = w e' := by
  intro e e' heq
  induction heq with
  | rel x y hr => exact h x y hr
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem completeness_transfer {G : Geometry}
    (f : G.FixedEntry → F) (S : Vector G.Entry G.t)
    (spec : ConstraintSpec G)
    {φ : Vector F G.t} {w : G.Entry → F}
    (h_fixed : ∀ e : G.FixedEntry, w e.val = f e)
    (h_input : ∀ k : G.Input, w S[k] = φ[k])
    (h_copy : ∀ e e', (e, e') ∈ spec.copy_pairs → w e = w e') :
    (circuit_of_spec G f S spec).R_parts φ w where
  fixed e := h_fixed e
  input k := h_input k
  equal e e' heq := by
    simp only [circuit_of_spec] at heq
    exact witness_respects_eqvGen h_copy e e' heq

end Transfer

/-! ## Full demonstration: `dt` round-trip -/

section DtDemo
open dt

variable (F : Type) [Field F]

def soundness_spec : ConstraintSpec G where
  fixed_entries := { var_c_fixed }
  input_indices := { input 0 }
  copy_pairs := { (var_a, var_c) }

def completeness_spec : ConstraintSpec G where
  fixed_entries := { var_c_fixed }
  input_indices := { input 0 }
  copy_pairs := Set.univ

def minimal_spec : ConstraintSpec G :=
  soundness_spec.union completeness_spec

noncomputable def C_synth : AbstractCircuit F :=
  circuit_of_spec G (fun _ => (42 : F)) #v[var_a] minimal_spec

set_option linter.unusedVariables false in
theorem C_synth_E_total : ∀ e e' : G.Entry, (C_synth F).E e e' :=
  fun _ _ => Relation.EqvGen.rel _ _ (Set.mem_union_right _ (Set.mem_univ _))

private theorem C_synth_var_c_fixed :
    (C_synth F).G.is_fixed var_c := by
  simp [C_synth, circuit_of_spec, G, var_c, Geometry.is_fixed, Geometry.entry]

/-- Knowledge soundness: same `calc` chain for synthesized circuit. -/
theorem synth_ks (x : F) (sat : Satisfying (C_synth F).R #v[x]) : x = 42 := by
  let st := sat.satisfied
  calc x = sat.w var_a := symm <| use_input st (⟨0, by simp [C_synth, circuit_of_spec, G]⟩)
       _ = sat.w var_c := use_equal st var_a var_c (C_synth_E_total F var_a var_c)
       _ = 42          := use_fixed st ⟨var_c, C_synth_var_c_fixed F⟩

/-- Completeness: the valid witness satisfies the synthesized circuit. -/
theorem synth_complete :
    (C_synth F).R_parts #v[(42 : F)] (valid_witness F) := by
  apply completeness_transfer
  · intro e; simp [valid_witness, witness]
  · intro k
    fin_cases k
    simp [valid_witness, witness]
    rfl
  · intro e e' _; simp [valid_witness, witness]

/-- Both directions hold for the synthesized circuit. -/
theorem synth_correct :
    (∀ x : F, Satisfying (C_synth F).R #v[x] → x = 42) ∧
    (C_synth F).R_parts #v[(42 : F)] (valid_witness F) :=
  ⟨synth_ks F, synth_complete F⟩

end DtDemo
