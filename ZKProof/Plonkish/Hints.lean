import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

import ZKProof.Plonkish.Defs


/-- Offset hints provided by the circuit designer. -/
structure Hints (G : Geometry) where
  /-- Target concrete column for each abstract column. -/
  h : G.Col → ℕ
  /-- Row offset for each abstract column. -/
  e : G.Col → ℤ


variable {F : Type} [Field F]

namespace FindRowMapping

variable (C : AbstractCircuit F) (hints : Hints C.G)

/-- The specification's `constrained` predicate including fixed columns. -/
def spec_constrained (entry : C.G.Entry) : Prop :=
  C.G.is_fixed entry ∨ C.constrained entry

/-- The working coordinate map: `(i, j) ↦ (h_i, r(j) + e_i)`. -/
def working_coord_map (r : C.G.Row → ℕ) (entry : C.G.Entry) : ℕ × ℤ :=
  (hints.h entry.i, (r entry.j : ℤ) + hints.e entry.i)

/-- The `ok_for` predicate: row mapping `r` is valid for rows in `R`. -/
def ok_for (R : Set C.G.Row) (r : C.G.Row → ℕ) : Prop :=
  ∀ (entry : C.G.Entry), entry.j ∈ R → spec_constrained C entry →
    (0 ≤ (r entry.j : ℤ) + hints.e entry.i) ∧
    (∀ (entry' : C.G.Entry), entry'.j ∈ R → spec_constrained C entry' →
      entry ≠ entry' →
      working_coord_map C hints r entry ≠ working_coord_map C hints r entry')

theorem ok_for_mono {R R' : Set C.G.Row} {r : C.G.Row → ℕ}
    (h : ok_for C hints R r) (hR : R' ⊆ R) : ok_for C hints R' r := by
  intro entry hj hc
  exact ⟨(h entry (hR hj) hc).1,
    fun entry' hj' hc' hne => (h entry (hR hj) hc).2 entry' (hR hj') hc' hne⟩

/-- A valid row mapping produced by `FIND_ROW_MAPPING`. -/
structure ValidRowMapping where
  r : C.G.Row → ℕ
  strict_mono : StrictMono r
  valid : ok_for C hints Set.univ r

namespace ValidRowMapping
variable {C : AbstractCircuit F} {hints : Hints C.G} (vrm : ValidRowMapping C hints)

def coord_map (entry : C.G.Entry) : ℕ × ℤ :=
  working_coord_map C hints vrm.r entry

def coord_col (i : C.G.Col) : ℕ := hints.h i

def coord_row (entry : C.G.Entry) : ℤ :=
  (vrm.r entry.j : ℤ) + hints.e entry.i

theorem coord_row_nonneg (entry : C.G.Entry)
    (hc : spec_constrained C entry) : 0 ≤ vrm.coord_row entry :=
  (vrm.valid entry (Set.mem_univ _) hc).1

theorem coord_map_injective (e e' : C.G.Entry)
    (hc : spec_constrained C e) (hc' : spec_constrained C e')
    (hne : e ≠ e') : vrm.coord_map e ≠ vrm.coord_map e' :=
  (vrm.valid e (Set.mem_univ _) hc).2 e' (Set.mem_univ _) hc' hne

end ValidRowMapping

noncomputable def find_row_mapping : ValidRowMapping C hints := by
  exact sorry

end FindRowMapping
