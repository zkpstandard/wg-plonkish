import Mathlib.Tactic

import ZKProof.Plonkish.Defs
import ZKProof.Plonkish.CheckHints

/-!
# Valid hints: bundled well-formedness

Issue #52: either introduce a `check_hints` function (done in
`CheckHints.lean` via `check_hints`), or edit hints to be a structure
where all syntactically correct inputs lead to valid circuits.

This file implements the second alternative: `ValidHints C` bundles
the hint functions with a proof of well-formedness.  By construction,
every inhabitant of `ValidHints C` yields a valid circuit — there is
no way to construct one without the well-formedness proof.

## Two formulations

The repository now offers both alternatives:

1. **Runtime check** (`CheckHints.lean`):
   - `Hints G` is a plain pair of functions
   - `check_hints C hints : Prop` is a separate predicate
   - Well-formedness is a property to verify
   - Suited for circuits where hints come from external sources

2. **Type-level guarantee** (this file):
   - `ValidHints C` bundles hints with a well-formedness proof
   - Cannot construct a `ValidHints` without proving well-formedness
   - Suited for circuits where hints are designed alongside proofs

Both formulations are equivalent; we provide conversions between them.

## On choosing "good" hints

**Out of scope.**  Selecting hints that lead to *efficient* concrete
circuits (few rows, few columns, compact layout) is an optimization
problem orthogonal to well-formedness.  Any well-formed hints give a
correct translation; different choices affect circuit size and
prover performance.  Heuristics for good hint selection are a
backend implementation concern, not part of the correctness
specification.
-/

variable {F : Type} [Field F]

namespace ValidHints
open CheckHints

/-- Valid hints for a specific circuit: the hint functions bundled
    with a proof that they are well-formed.

    By construction, `ValidHints C` is inhabited only by hints that
    pass `check_hints`. -/
structure _root_.ValidHints (C : AbstractCircuit F) where
  /-- Target concrete column for each abstract column. -/
  h : C.G.Col → ℕ
  /-- Row offset for each abstract column. -/
  e : C.G.Col → ℤ
  /-- Well-formedness: identified columns have semantically identical cells. -/
  well_formed : check_hints C ⟨h, e⟩

/-- Forget the well-formedness proof to obtain plain hints. -/
def toHints {C : AbstractCircuit F} (vh : _root_.ValidHints C) : Hints C.G where
  h := vh.h
  e := vh.e

/-- Lift plain hints with a well-formedness proof to valid hints. -/
def ofHints {C : AbstractCircuit F} (hints : Hints C.G)
    (h_wf : check_hints C hints) : _root_.ValidHints C where
  h := hints.h
  e := hints.e
  well_formed := h_wf

/-- Round-trip: `toHints` after `ofHints` is identity. -/
@[simp] theorem toHints_ofHints {C : AbstractCircuit F} (hints : Hints C.G)
    (h_wf : check_hints C hints) :
    toHints (ofHints hints h_wf) = hints := by
  cases hints; rfl

/-- Round-trip: `ofHints` after `toHints` is identity (on the hint data). -/
@[simp] theorem ofHints_toHints {C : AbstractCircuit F} (vh : _root_.ValidHints C) :
    ofHints (toHints vh) vh.well_formed = vh := by
  cases vh; rfl

/-- Valid hints always pass `check_hints` on their underlying data. -/
theorem check_hints_ofValid {C : AbstractCircuit F} (vh : _root_.ValidHints C) :
    check_hints C (toHints vh) :=
  vh.well_formed

/-! ## Constructing valid hints

Sufficient conditions from `CheckHints.lean` transfer to constructors
for `ValidHints`. -/

/-- Construct valid hints from injective hint functions. -/
def ofInjective {C : AbstractCircuit F} (h : C.G.Col → ℕ) (e : C.G.Col → ℤ)
    (h_inj : HintsInjective ⟨h, e⟩) : _root_.ValidHints C where
  h := h
  e := e
  well_formed := check_hints_of_injective _ h_inj

/-- The identity hints are always valid. -/
def identity (C : AbstractCircuit F) : _root_.ValidHints C :=
  ofInjective (fun i => i.val) (fun _ => 0) (identity_hints_injective C.G)

/-! ## Equivalence with the runtime-check formulation

`ValidHints C` and `{hints : Hints C.G // check_hints C hints}`
carry the same information.  We give the explicit equivalence. -/

/-- `ValidHints C` is equivalent to the subtype of `Hints C.G` satisfying
    `check_hints`.  This makes precise the claim that the two formulations
    are interchangeable. -/
def equivSubtype (C : AbstractCircuit F) :
    _root_.ValidHints C ≃ { hints : Hints C.G // check_hints C hints } where
  toFun vh := ⟨toHints vh, vh.well_formed⟩
  invFun p := ofHints p.val p.property
  left_inv vh := by cases vh; rfl
  right_inv p := by cases p; rfl

end ValidHints
