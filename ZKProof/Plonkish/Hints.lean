import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

import ZKProof.Plonkish.Defs


/-- Offset hints provided by the circuit designer.

    Each hint assigns to an abstract column index `i`:
    - a target concrete column `h i : ℕ`
    - a row offset `e i : ℤ`

    These guide the `FIND_ROW_MAPPING` algorithm in constructing the
    coordinate mapping from abstract to concrete circuits. -/
structure Hints (G : Geometry) where
  /-- Target concrete column for each abstract column. -/
  h : G.Col → ℕ
  /-- Row offset for each abstract column. -/
  e : G.Col → ℤ


variable {F : Type} [Field F]

namespace FindRowMapping

variable (C : AbstractCircuit F) (hints : Hints C.G)

/-- The specification's `constrained` predicate including fixed columns.
    A cell is constrained if it lies in a fixed column or participates in
    any copy, instance, custom, or lookup constraint.

    This extends `AbstractCircuit.constrained` with the fixed-column check
    from the specification's pseudocode. The Lean `constrained` in `Defs.lean`
    omits this because fixed cells are often captured via `≡`, but the
    `FIND_ROW_MAPPING` algorithm needs the explicit check. -/
def spec_constrained (entry : C.G.Entry) : Prop :=
  C.G.is_fixed entry ∨ C.constrained entry

/-- The working coordinate map: given hints, a row mapping `r`, and an
    abstract cell, returns the concrete coordinates `(h_i, r(j) + e_i)`.

    This is Equation (1) from the optimizations document. -/
def working_coord_map (r : C.G.Row → ℕ) (entry : C.G.Entry) : ℕ × ℤ :=
  (hints.h entry.i, (r entry.j : ℤ) + hints.e entry.i)

/-- The `ok_for` predicate: the row mapping `r` is valid for all rows in `R`.

    For every constrained cell whose row is in `R`:
    1. The concrete row coordinate `r(j) + e_i` is non-negative.
    2. No other constrained cell in `R` maps to the same concrete coordinate.

    This directly formalizes the `ok_for` function from the specification. -/
def ok_for (R : Set C.G.Row) (r : C.G.Row → ℕ) : Prop :=
  ∀ (entry : C.G.Entry), entry.j ∈ R → spec_constrained C entry →
    -- In-bounds: concrete row coordinate is non-negative
    (0 ≤ (r entry.j : ℤ) + hints.e entry.i) ∧
    -- Uniqueness: no other constrained cell in R maps to the same coordinate
    (∀ (entry' : C.G.Entry), entry'.j ∈ R → spec_constrained C entry' →
      entry ≠ entry' →
      working_coord_map C hints r entry ≠ working_coord_map C hints r entry')

/-- Monotonicity of `ok_for`: if `ok_for` holds for `R`, it holds for any subset. -/
theorem ok_for_mono {R R' : Set C.G.Row} {r : C.G.Row → ℕ}
    (h : ok_for C hints R r) (hR : R' ⊆ R) : ok_for C hints R' r := by
  intro entry hj hc
  exact ⟨(h entry (hR hj) hc).1,
    fun entry' hj' hc' hne => (h entry (hR hj) hc).2 entry' (hR hj') hc' hne⟩

/-- A valid row mapping produced by `FIND_ROW_MAPPING`. -/
structure ValidRowMapping where
  /-- The row mapping from abstract to concrete row indices. -/
  r : C.G.Row → ℕ
  /-- The mapping is strictly increasing. -/
  strict_mono : StrictMono r
  /-- `ok_for` holds on the full set of rows. -/
  valid : ok_for C hints Set.univ r

namespace ValidRowMapping
variable {C : AbstractCircuit F} {hints : Hints C.G} (vrm : ValidRowMapping C hints)

/-- The coordinate map derived from a valid row mapping. -/
def coord_map (entry : C.G.Entry) : ℕ × ℤ :=
  working_coord_map C hints vrm.r entry

/-- The concrete column of an abstract cell under the coordinate map. -/
def coord_col (i : C.G.Col) : ℕ :=
  hints.h i

/-- The concrete row of an abstract cell under the coordinate map. -/
def coord_row (entry : C.G.Entry) : ℤ :=
  (vrm.r entry.j : ℤ) + hints.e entry.i

/-- Constrained cells have non-negative concrete row coordinates. -/
theorem coord_row_nonneg (entry : C.G.Entry)
    (hc : spec_constrained C entry) : 0 ≤ vrm.coord_row entry :=
  (vrm.valid entry (Set.mem_univ _) hc).1

/-- Distinct constrained cells map to distinct concrete coordinates. -/
theorem coord_map_injective (e e' : C.G.Entry)
    (hc : spec_constrained C e) (hc' : spec_constrained C e')
    (hne : e ≠ e') : vrm.coord_map e ≠ vrm.coord_map e' :=
  (vrm.valid e (Set.mem_univ _) hc).2 e' (Set.mem_univ _) hc' hne

end ValidRowMapping

/-- The `FIND_ROW_MAPPING` algorithm always produces a valid row mapping.

    The greedy algorithm processes rows `0` through `n-1`. At each step `g`,
    it finds the minimal `g' ≥ a'` such that extending the partial row mapping
    with `g ↦ g'` preserves validity. This always succeeds because only
    finitely many values of `g'` can conflict with previously assigned rows.

    Proof deferred to `FindRowMapping.lean`. -/
noncomputable def find_row_mapping : ValidRowMapping C hints := by
  exact sorry

end FindRowMapping
