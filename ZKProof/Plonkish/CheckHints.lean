import Mathlib.Tactic

import ZKProof.Plonkish.Defs

/-!
# Hints well-formedness (`check_hints`)

Issue #65: hints have a condition to satisfy: two hints can only map
to the same concrete column and offset if the source cells are
semantically the same.

The hints map each abstract column `i` to `(h_i, e_i)` where:
- `h_i` is a target concrete column index
- `e_i` is a row offset

When two abstract columns `i, k` get the same `(h_i, e_i) = (h_k, e_k)`,
cells `(i, j)` and `(k, j)` are "column-and-offset identified" in the
concrete circuit (they both become `(h_i, r(j) + e_i)` for any valid
row mapping `r`).  For this identification to be harmless, the cells
must be semantically the same.

## Semantic sameness

Per the issue:
- **Fixed columns**: the values are identical (`f(i, j) = f(k, j)`)
- **Non-fixed columns**: the cells are equated by `≡` OR both are
  unconstrained (so arbitrary values are fine)

## The `check_hints` predicate

We formalize this as a `Prop`-valued predicate.  A circuit's hints
are well-formed iff for every pair of columns identified by the hints,
every row witnesses semantic sameness.
-/

variable {F : Type} [Field F]

namespace CheckHints

/-- Hints mapping abstract columns to (target column, row offset). -/
structure Hints (G : Geometry) where
  /-- Target concrete column index for each abstract column. -/
  h : G.Col → ℕ
  /-- Row offset for each abstract column. -/
  e : G.Col → ℤ

/-- Two hints are "column-and-offset identified": they point to the
    same concrete column with the same offset. -/
def Identified {G : Geometry} (hints : Hints G) (i k : G.Col) : Prop :=
  hints.h i = hints.h k ∧ hints.e i = hints.e k

theorem Identified.refl {G : Geometry} (hints : Hints G) (i : G.Col) :
    Identified hints i i :=
  ⟨rfl, rfl⟩

theorem Identified.symm {G : Geometry} {hints : Hints G} {i k : G.Col}
    (h : Identified hints i k) : Identified hints k i :=
  ⟨h.1.symm, h.2.symm⟩

theorem Identified.trans {G : Geometry} {hints : Hints G} {i k l : G.Col}
    (h₁ : Identified hints i k) (h₂ : Identified hints k l) :
    Identified hints i l :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

/-- Semantic sameness for fixed cells: the fixed values are identical. -/
def SameFixed (C : AbstractCircuit F) (e₁ e₂ : C.G.Entry)
    (h₁ : C.G.is_fixed e₁) (h₂ : C.G.is_fixed e₂) : Prop :=
  C.f ⟨e₁, h₁⟩ = C.f ⟨e₂, h₂⟩

/-- Semantic sameness for non-fixed cells: either equated by `≡` or
    both unconstrained (where "unconstrained" uses the spec notion
    including fixed columns). -/
def SameNonFixed (C : AbstractCircuit F) (e₁ e₂ : C.G.Entry) : Prop :=
  C.E e₁ e₂ ∨ (¬ C.constrained e₁ ∧ ¬ C.constrained e₂)

/-- A constraint: the cell is not in a fixed column. -/
def NotFixed (C : AbstractCircuit F) (e : C.G.Entry) : Prop :=
  ¬ C.G.is_fixed e

/-- Semantic sameness for two cells sharing a row.  Depends on whether
    the columns are fixed or not. -/
def SemanticallySame (C : AbstractCircuit F) (e₁ e₂ : C.G.Entry) : Prop :=
  -- Both cells fixed with identical values
  (∃ (h₁ : C.G.is_fixed e₁) (h₂ : C.G.is_fixed e₂), SameFixed C e₁ e₂ h₁ h₂) ∨
  -- Both cells non-fixed and semantically identified
  (NotFixed C e₁ ∧ NotFixed C e₂ ∧ SameNonFixed C e₁ e₂)

/-- The `check_hints` predicate: for every pair of identified columns
    and every row, the corresponding cells are semantically the same.

    This is the hint well-formedness condition from issue #65. -/
def check_hints (C : AbstractCircuit F) (hints : Hints C.G) : Prop :=
  ∀ (i k : C.G.Col) (j : C.G.Row),
    Identified hints i k → i ≠ k →
    SemanticallySame C ⟨i, j⟩ ⟨k, j⟩

/-! ## Sufficient conditions

We exhibit progressively simpler sufficient conditions that imply
`check_hints`.  These are useful for actually proving well-formedness
in specific circuits. -/

/-- A stricter sufficient condition: identified columns are never
    identified to distinct cells.  Equivalently, the `h` and `e`
    functions together are injective. -/
def HintsInjective {G : Geometry} (hints : Hints G) : Prop :=
  ∀ i k : G.Col, Identified hints i k → i = k

/-- Injective hints are trivially well-formed (no identifications to check). -/
theorem check_hints_of_injective {C : AbstractCircuit F} (hints : Hints C.G)
    (h_inj : HintsInjective hints) : check_hints C hints := by
  intro i k j h_id h_ne
  exact absurd (h_inj i k h_id) h_ne

/-- An intermediate condition: every pair of identified columns consists of
    fully-equivalent columns, i.e., all cells in identified columns are
    pairwise equivalent under `≡`. -/
def EquivColumns (C : AbstractCircuit F) (hints : Hints C.G) : Prop :=
  ∀ (i k : C.G.Col), Identified hints i k →
    ∀ j : C.G.Row, C.E ⟨i, j⟩ ⟨k, j⟩

/-- If cells in identified columns are equivalent and the columns are
    non-fixed, then `check_hints` holds. -/
theorem check_hints_of_equiv_columns {C : AbstractCircuit F}
    {hints : Hints C.G}
    (h_equiv : EquivColumns C hints)
    (h_nonfixed : ∀ i k : C.G.Col, Identified hints i k → i ≠ k →
      ∀ j : C.G.Row, NotFixed C ⟨i, j⟩ ∧ NotFixed C ⟨k, j⟩) :
    check_hints C hints := by
  intro i k j h_id h_ne
  right
  obtain ⟨hn_i, hn_k⟩ := h_nonfixed i k h_id h_ne j
  exact ⟨hn_i, hn_k, Or.inl (h_equiv i k h_id j)⟩

/-! ## Properties of well-formed hints

Given `check_hints`, any two columns identified by the hints give
cells that are either equivalent or (for fixed columns) have equal
fixed values. -/

/-- If hints are well-formed and two distinct columns are identified,
    and both are non-fixed, then cells in the same row are either
    equivalent or both unconstrained. -/
theorem equivalent_or_unconstrained
    {C : AbstractCircuit F} {hints : Hints C.G}
    (h_wf : check_hints C hints)
    {i k : C.G.Col} (h_id : Identified hints i k) (h_ne : i ≠ k)
    (j : C.G.Row)
    (hn_i_j : NotFixed C ⟨i, j⟩) :
    C.E ⟨i, j⟩ ⟨k, j⟩ ∨ (¬ C.constrained ⟨i, j⟩ ∧ ¬ C.constrained ⟨k, j⟩) := by
  have := h_wf i k j h_id h_ne
  rcases this with ⟨h_i_fixed, _, _⟩ | ⟨_, _, hsame⟩
  · exact absurd h_i_fixed hn_i_j
  · exact hsame

/-- If hints are well-formed and two distinct columns are identified,
    and both are fixed, then cells in the same row have equal fixed values. -/
theorem fixed_values_equal
    {C : AbstractCircuit F} {hints : Hints C.G}
    (h_wf : check_hints C hints)
    {i k : C.G.Col} (h_id : Identified hints i k) (h_ne : i ≠ k)
    (j : C.G.Row)
    (h_i_fixed : C.G.is_fixed ⟨i, j⟩) (h_k_fixed : C.G.is_fixed ⟨k, j⟩) :
    C.f ⟨⟨i, j⟩, h_i_fixed⟩ = C.f ⟨⟨k, j⟩, h_k_fixed⟩ := by
  have := h_wf i k j h_id h_ne
  rcases this with ⟨_, _, hsame⟩ | ⟨hn_i, _, _⟩
  · exact hsame
  · exact absurd h_i_fixed hn_i

/-! ## Reflexivity: identity hints are well-formed

If the hints are the identity (h_i = i.val, e_i = 0), then no two
distinct columns are identified, so `check_hints` holds trivially. -/

/-- Identity hints: map column `i` to concrete column `i` with offset 0. -/
def identity_hints (G : Geometry) : Hints G where
  h := fun i => i.val
  e := fun _ => 0

theorem identity_hints_injective (G : Geometry) :
    HintsInjective (identity_hints G) := by
  intro i k ⟨h_col, _⟩
  ext; exact h_col

theorem identity_hints_well_formed (C : AbstractCircuit F) :
    check_hints C (identity_hints C.G) :=
  check_hints_of_injective _ (identity_hints_injective C.G)

end CheckHints
