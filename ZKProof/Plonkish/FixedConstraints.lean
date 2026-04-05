import Mathlib.Tactic

import ZKProof.Plonkish.Defs

/-!
# Fixed cells and the "constrained" definition

Issue #59: do we need to add fixed constraints to the Notations section
of the Plonkish relation, or should they already be captured by copy
constraints?

## The question

The plain `AbstractCircuit.constrained` (in `Defs.lean`) identifies a
cell as constrained if it participates in a copy, input, custom, or
lookup constraint.  It does NOT mention fixed cells explicitly, and
the code comment says "fixed cells do not need to be treated as a
special case" — the intuition being that fixed cells are captured by
copy constraints.

This file examines whether that intuition holds.

## Answer

**No, fixed cells are not always captured by copy constraints.**

An isolated fixed cell (one with no distinct `C.E`-neighbor, no
instance mapping, no polynomial support) satisfies none of the four
clauses of `constrained`, yet clearly has a meaningful fixed value
enforced by `R_parts.fixed`.

For correctness proofs that depend on "constrained" classification
(e.g., `FIND_ROW_MAPPING`), we therefore need an enriched notion.
We call this `spec_constrained`, adding the `is_fixed` clause
explicitly.  This matches the decision used in the optimizations
document's `constrained` pseudocode (which DOES check `i < m_f`).

## Recommendation for the specification

Add the `is_fixed` clause to the Notations section's definition of
"constrained", with a note that this matches the `check i < m_f`
line of the pseudocode in the optimizations document.
-/

variable {F : Type} [Field F]

namespace FixedConstraints

/-- The "spec" notion of constrained, matching the optimizations
    document's pseudocode.  Includes the fixed-column check. -/
def spec_constrained (C : AbstractCircuit F) (e : C.G.Entry) : Prop :=
  C.G.is_fixed e ∨ C.constrained e

/-! ## The plain notion does not capture fixed cells

We show that `AbstractCircuit.constrained` can fail to classify a
fixed cell, i.e., `constrained` and `spec_constrained` are not
equivalent in general. -/

/-- Trivial equivalence relation: only reflexive pairs.

    This is the canonical "no copy constraints" setting: cells are
    only equated to themselves. -/
def TrivialE (G : Geometry) (e e' : G.Entry) : Prop := e = e'

theorem trivialE_equivalence (G : Geometry) : Equivalence (TrivialE G) where
  refl _ := rfl
  symm h := h.symm
  trans h₁ h₂ := h₁.trans h₂

/-- If a circuit uses the trivial equivalence and has no instance
    mappings, custom gates, or lookup tables, then the plain
    `constrained` predicate is always `False`. -/
theorem constrained_false_for_isolated
    (C : AbstractCircuit F)
    (h_trivE : ∀ e e', C.E e e' ↔ e = e')
    (h_noS : C.G.t = 0)
    (h_noU : C.U = 0)
    (h_noV : C.V = 0)
    (e : C.G.Entry) :
    ¬ C.constrained e := by
  unfold AbstractCircuit.constrained
  intro h
  rcases h with ⟨e', h_ne, h_eq⟩ | ⟨k, _⟩ | ⟨u, _⟩ | ⟨v, _, _⟩
  · exact h_ne ((h_trivE e e').mp h_eq)
  · exact absurd k.isLt (by simp [h_noS])
  · exact absurd u.isLt (by simp [h_noU])
  · exact absurd v.isLt (by simp [h_noV])

/-- But a fixed cell in such a circuit is still `spec_constrained`. -/
theorem fixed_spec_constrained (C : AbstractCircuit F) (e : C.G.Entry)
    (h_fixed : C.G.is_fixed e) : spec_constrained C e :=
  Or.inl h_fixed

/-! ## Equivalence conditions

The two notions coincide exactly when every fixed cell participates
in SOME copy, input, custom, or lookup constraint. -/

/-- `spec_constrained` always implies the plain `constrained` for
    non-fixed cells (trivially, since fixed-column is the only
    extra case). -/
theorem spec_constrained_nonfixed {C : AbstractCircuit F} {e : C.G.Entry}
    (h_nf : ¬ C.G.is_fixed e) :
    spec_constrained C e → C.constrained e := by
  intro h
  rcases h with h_fixed | h_c
  · exact absurd h_fixed h_nf
  · exact h_c

/-- The plain `constrained` always implies `spec_constrained`. -/
theorem constrained_implies_spec {C : AbstractCircuit F} {e : C.G.Entry}
    (h : C.constrained e) : spec_constrained C e :=
  Or.inr h

/-- The two notions agree iff every fixed cell is captured by the
    plain constrained definition. -/
theorem spec_eq_plain_iff (C : AbstractCircuit F) :
    (∀ e, spec_constrained C e ↔ C.constrained e) ↔
    (∀ e, C.G.is_fixed e → C.constrained e) := by
  constructor
  · intro h e h_fixed
    exact (h e).mp (Or.inl h_fixed)
  · intro h e
    constructor
    · intro hsc
      rcases hsc with hf | hc
      · exact h e hf
      · exact hc
    · exact fun hc => Or.inr hc

/-! ## Sufficient convention for equivalence

A simple design convention making the two notions agree: every fixed
cell is copy-equivalent to the canonical fixed-column representative
at row 0. -/

/-- "Fixed-to-row-0" convention: every fixed cell is equated via `≡`
    to the cell at the same column, row 0. -/
def FixedToRow0Convention (C : AbstractCircuit F) : Prop :=
  ∀ e : C.G.Entry, C.G.is_fixed e → e.j ≠ 0 →
    ∃ e' : C.G.Entry, e' = ⟨e.i, 0⟩ ∧ e ≠ e' ∧ C.E e e'

/-- Under the row-0 convention, fixed cells (at rows ≠ 0) are captured
    by copy constraints. -/
theorem fixed_captured_under_convention {C : AbstractCircuit F}
    (h_conv : FixedToRow0Convention C) (e : C.G.Entry)
    (h_fixed : C.G.is_fixed e) (h_row : e.j ≠ 0) :
    C.constrained e := by
  obtain ⟨e', _, h_ne, h_eq⟩ := h_conv e h_fixed h_row
  exact Or.inl ⟨e', h_ne, h_eq⟩

/-! ## Summary and recommendation

Given the above analysis:

- The plain `constrained` definition can fail for isolated fixed cells.
- Design conventions (e.g., `FixedToRow0Convention`) can ensure
  coincidence, but these are not required by the Plonkish relation.
- The `FIND_ROW_MAPPING` optimization specifically checks `i < m_f`
  in its `constrained` pseudocode, matching `spec_constrained`.

**Recommendation:** The specification's Notations section should
define "constrained" to include the fixed-column check explicitly,
OR add a comment noting that the optimization's pseudocode uses an
enriched notion.  The Lean formalization here uses `spec_constrained`
throughout for consistency with the optimization's algorithmic spec.
-/

end FixedConstraints
