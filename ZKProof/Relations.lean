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

More generally, we are likely to have multiple layers of [`Refinement`] between
an application relation and a circuit relation. In the context of any given
refinement, we will talk about a higher-level "source relation" and a
lower-level "target relation", where we aim to use the latter to implement
the former.

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
-/

structure Sat {I W : Type} (R : Rel I W) (x : I) where
  w : W
  satisfied : R x w

structure Refinement (I S T : Type) where
  source : Rel I S
  target : Rel I T

/-
A Refinement is Complete iff for all instances x, given a satisfying
source witness we can produce a satisfying target witness.
-/
def Complete {I S T : Type} (r : Refinement I S T) :=
  (x : I) → Sat r.source x → Sat r.target x

/-
A Refinement is Sound iff for all instances x, given a satisfying
target witness there exists a satisfying source witness.
-/
def Sound {I S T : Type} (r : Refinement I S T) :=
  (x : I) → Sat r.target x → ∃ w : S, r.source x w

/-
A Refinement is KnowledgeSound iff for all instances x, given a
satisfying target witness we can produce a satisfying source witness.
-/
def KnowledgeSound {I S T : Type} (r : Refinement I S T) :=
  (x : I) → Sat r.target x → Sat r.source x
