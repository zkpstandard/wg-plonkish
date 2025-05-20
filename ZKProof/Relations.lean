import Mathlib.Data.Rel
import Mathlib.Logic.Basic
import Mathlib.Tactic

/-
Terminology

We try to follow the ZKProof Community Reference as far as possible. It uses the
following definitions:

* Instance: Input commonly known to both prover (P) and verifier (V), and used
  to support the statement of what needs to be proven. This common input may
  either be local to the prover–verifier interaction, or public in the sense of
  being known by external parties. Notation: x. (Some scientific articles use
  “instance” and “statement” interchangeably, but we distinguish between the two.)

* Witness: Private input to the prover. Others may or may not know something
  about the witness. Notation: w.

In practice we typically have an "application relation" describing something that
needs to be proven in a given protocol, and a "circuit relation" elaborating
this for a particular circuit design, arithmetization, proof system, and choice
of parameters (fields, curves, etc).

More generally, we are likely to have multiple layers of
[refinement](https://en.wikipedia.org/wiki/Refinement_(computing)) between
an application relation and a circuit relation. We will represent this as a
[`Refinement`]. In the context of any given refinement, we will talk about a
higher-level "source relation" and a lower-level "target relation", where we
aim to use the latter to implement the former.

What might not be obvious is that security properties like (knowledge)
soundness and completeness are properties of the *refinements*, not the
individual relations. That is, defining these security properties
*inherently depends on* there being separate source and target relations.

Given source and target relations with identical instance types, informally:

* (knowledge) soundness means that we cannot find a satisfying target witness
  unless there exists (or we know) a satisfying source witness for the same
  instance;
* completeness means that we can always find a satisfying target witness
  for a given source witness and instance. (This computation is informally
  called "witness generation", referring to the target witness.)

To apply this to the final proof system, view the proof as the target witness.

The advantage of this approach is its composability. We can define a chain
of refinement steps with the application witness as the initial source
witness, and the proof as the final target witness. This facilitates proving
end-to-end correctness: if all of the steps are (knowledge) sound then the
overall chain is (knowledge) sound, and if all of the steps are complete
then the overall chain is complete. We can also decompose a step into
finer-grained steps as necessary.

As a plausibility check, consider the trivial proof system that outputs a
claimed satisfying witness as the proof, and has a verifier that directly
checks whether this witness is satisfying. In the above approach, proof systems
are refinements between relations, and the trivial proof system is the identity
refinement, i.e. the relation is the same, and target witnesses are source
witnesses. The resulting system is obviously sound, knowledge sound and
complete. If, on the other hand, we introduce additional target witnesses
that are accepted but do not correspond to any source witness, then we will
not be able to prove soundness, and if we exclude some source witnesses from
being considered valid proofs, we will be unable to prove completeness, as
expected.

Note that the terms "sound" and "complete" come from the study of formal
systems of logic, where they *also* —contrary to some informal presentations—
are properties of refinements between two formal systems. An object formal
system (the target of the refinement) is called "sound" if all of its provable
formulae are "valid" in some metasystem (the source of the refinement).
Similarly, an object formal system is called "complete" if all "valid" formulae
in the metasystem are provable.

We have the following correspondences, extending the Curry–Howard–Lambek
correspondence:

| Relations | Proof systems | Formal systems | Proof calculi | Closed monoidal categories |
|-----------|---------------|----------------|---------------|----------------------------|
| Instance  | Instance      | Formula        | Type          | Object                     |
| Witness   | Proof         | Proof          | Term          | Morphism                   |

As in the field of zk and succinct proofs, the fact that a logical semantics
is just another formal system is somewhat obscured by the terminology and
presentation — and perhaps by a desire coming from the history of the field
to avoid a perception of circularity. In particular, presenting valid formulae
in the metalanguage as "true" rather begs the question. They are just valid
within that system.

Enough philosophy. A relation will be formalized as a Prop that takes an
instance and witness as parameters, and holds exactly when the intended
statement holds.

Previous work:

* [Algebraic Reductions of Knowledge](https://eprint.iacr.org/2022/009) -- this
  paper describes a notion that generalises refinements by allowing them to be
  interactive protocols.
-/

/--
A satisfying witness.
-/
structure Satisfying {I W : Type} (R : Rel I W) (x : I) where
  /-- The witness. -/
  w : W
  /-- The given relation is satisfied by this witness on the given instance. -/
  satisfied : R x w

/--
A `Refinement` is a transformation from a more abstract or high-level relation
into a more concrete or low-level relation, where the two relations have
equivalent instances.

This is the same sense as a [refinement](https://en.wikipedia.org/wiki/Refinement_(computing))
from a specification to a concrete program.
-/
structure Refinement {I I' W W' : Type} (R : Rel I W) (R' : Rel I' W') where
  /--
  An equivalence between the instance types of the source and target relations.
  Each source instance `x : I` corresponds to a target instance `trans x : I'`.
  -/
  trans : I ≃ I'

/--
A `Refinement` where source and target instances are the same.

In particular, `SimpleRefinement R R` is the trivial refinement of a relation to itself.
-/
def SimpleRefinement {I W W' : Type} (R : Rel I W) (R' : Rel I W') : Refinement R R' :=
  { trans := Equiv.refl I }

/--
A [`Refinement`] is `Complete` iff for each source instance, given a satisfying source
witness we can produce a satisfying target witness for the equivalent target instance.
-/
def Complete {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R') :=
  (x : I) → Satisfying R x → Satisfying R' (r.trans x)

/--
A [`Refinement`] is `Sound` iff for each target instance, given a satisfying target
witness there exists a satisfying source witness for the equivalent source instance.
-/
def Sound {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R') :=
  (x' : I') → Satisfying R' x' → Nonempty (Satisfying R (r.trans.symm x'))

/--
A [`Refinement`] is `KnowledgeSound` iff each target instance, given a satisfying
target witness we can produce a satisfying source witness for the equivalent source
instance.

NOTE: Lean is [not fully constructive](https://leanprover.github.io/theorem_proving_in_lean4/axioms_and_computation.html).
We have to be careful about the meaning of `KnowledgeSound`, since noncomputable
functions can obtain `KnowledgeSound r` from `Sound r`, as demonstrated by
[`obtain_knowledgesound_from_sound_noncomputably`].
-/
def KnowledgeSound {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R') :=
  (x' : I') → Satisfying R' x' → Satisfying R (r.trans.symm x')

theorem knowledge_soundness_implies_soundness {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R')
    (ks : KnowledgeSound r) : Sound r := by
  intro x' sat'
  let { w, satisfied } := ks x' sat'
  use w

inductive Soundness {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R')
| none
| sound (p : Sound r)
| knowledge_sound (p : KnowledgeSound r)

structure PSound {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R') where
  sound : Sound r
  dummy := ()

/--
A `RichRefinement` records whether completeness, soundness, and/or knowledge soundness
have been proven for a given `Refinement`.
-/
structure RichRefinement {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'} (r : Refinement R R') where
  complete : Option (Complete r)
  soundness : Soundness r
  sound : Option (PSound r) := match soundness with
    | Soundness.none => none
    | Soundness.sound p => some { sound := p }
    | Soundness.knowledge_sound ks => some { sound := knowledge_soundness_implies_soundness r ks }
  knowledge_sound : Option (KnowledgeSound r) := match soundness with
    | Soundness.none | Soundness.sound _ => none
    | Soundness.knowledge_sound p => some p

  /--
  What we mean by a correctness-preserving translation `T : AbstractCircuit F → ConcreteCircuit F`
  is that `T` is an efficiently computable function from abstract circuits to concrete circuits,
  such that for any abstract circuit `C` with `C' = T C`:

    * There is a bijective map `trans : I ≃ I'`, efficiently computable in both directions, between
      abstract instances and concrete instances.
    * There is an efficient witness translation function `F : W → W'` from abstract witnesses to
      concrete witnesses.
    * Completeness is preserved: given a satisfying instance `x` and witness `w` for the abstract circuit
      `C`, `w' = F w` is a satisfying witness for the concrete circuit `C'` with instance `trans x`.
    * Knowledge soundness is preserved: given a satisfying instance `x'` and witness `w'` for the
      concrete circuit `C'`, we can efficiently compute some satisfying witness w for the abstract
      circuit `C` with instance `trans.symm x'`.
  -/
  correct := complete.isSome ∧ knowledge_sound.isSome

/--
A `Bridge` joins two `Refinement`s with a common relation in the middle. It can be "collapsed"
to a single `Refinement`.

Note: `Bridge` is low-level infrastructure for composing refinements.
-/
structure Bridge {I₁ I₂ I₃ W₁ W₂ W₃ : Type} (R₁ : Rel I₁ W₁) (R₂ : Rel I₂ W₂) (R₃ : Rel I₃ W₃) where
  left : Refinement R₁ R₂
  right : Refinement R₂ R₃
  collapse : Refinement R₁ R₃ := { trans := Equiv.trans left.trans right.trans }

  compose_trans : collapse.trans = Equiv.trans left.trans right.trans
  compose_trans_symm : collapse.trans.symm = Equiv.trans right.trans.symm left.trans.symm := by simp_all only; rfl

  complete (lc : Complete left) (rc : Complete right) : Complete collapse :=
    fun (x₁ : I₁) (sat₁ : Satisfying R₁ x₁) =>
      let sat₃ := rc (left.trans x₁) (lc x₁ sat₁)
      { w := sat₃.w, satisfied := cast (by rw [compose_trans, Equiv.trans_apply]) sat₃.satisfied }

  sound (ls : Sound left) (rs : Sound right) : Sound collapse :=
    fun (x₃ : I₃) (sat₃ : Satisfying R₃ x₃) => by
      obtain ⟨w₂, satisfied₂⟩ := rs x₃ sat₃
      obtain ⟨w₁, satisfied₁⟩ := ls (right.trans.symm x₃) { w := w₂, satisfied := satisfied₂ }
      use w₁; simp_all only [Equiv.trans_apply]

  knowledge_sound (lks : KnowledgeSound left) (rks : KnowledgeSound right) : KnowledgeSound collapse :=
    fun (x₃ : I₃) (sat₃ : Satisfying R₃ x₃) =>
      let sat₁ := lks (right.trans.symm x₃) (rks x₃ sat₃)
      { w := sat₁.w, satisfied := cast (by rw [compose_trans_symm, Equiv.trans_apply, eq_iff_iff]) sat₁.satisfied }


/-- Composition of `Refinement`s using `*`. -/
instance collapse_hmul {I₁ I₂ I₃ W₁ W₂ W₃ : Type} {R₁ : Rel I₁ W₁} {R₂ : Rel I₂ W₂} {R₃ : Rel I₃ W₃} :
    HMul (Refinement R₁ R₂) (Refinement R₂ R₃) (Refinement R₁ R₃) where
  hMul (l : Refinement R₁ R₂) (r : Refinement R₂ R₃) :=
    let bridge : Bridge (R₁ : Rel I₁ W₁) (R₂ : Rel I₂ W₂) (R₃ : Rel I₃ W₃) := { left := l, right := r, compose_trans := by simp_all only }
    bridge.collapse


open Classical

/--
We have to be careful about the meaning of `KnowledgeSound`, since a noncomputable
function can obtain `KnowledgeSound r` from `Sound r`.
-/
noncomputable def obtain_knowledgesound_from_sound_noncomputably {I I' W W' : Type} {R : Rel I W} {R' : Rel I' W'}
    (r : Refinement R R') (s : Sound r) : KnowledgeSound r := by
  intro x' sat'
  exact choice (s x' sat')
