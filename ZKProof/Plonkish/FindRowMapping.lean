import ZKProof.Plonkish.Hints

open Classical

variable {F : Type} [Field F]

namespace FindRowMapping

variable (C : AbstractCircuit F) (hints : Hints C.G)

/-- Hints are well-formed: within any row, distinct constrained cells
    have distinct `(h, e)` pairs. -/
def HintsWellFormed : Prop :=
  ∀ (i k : C.G.Col) (j : C.G.Row),
    spec_constrained C { i := i, j := j } →
    spec_constrained C { i := k, j := j } →
    hints.h i = hints.h k → hints.e i = hints.e k →
    i = k

section SimpleConstruction

noncomputable def max_abs_offset : ℕ :=
  (Finset.univ : Finset C.G.Col).sup (fun i => (hints.e i).natAbs)

noncomputable def spacing : ℕ := 1 + 2 * max_abs_offset C hints
noncomputable def base : ℕ := max_abs_offset C hints

noncomputable def simple_r (j : C.G.Row) : ℕ :=
  base C hints + j.val * spacing C hints

theorem offset_le_max (i : C.G.Col) :
    (hints.e i).natAbs ≤ max_abs_offset C hints :=
  Finset.le_sup (f := fun i => (hints.e i).natAbs) (Finset.mem_univ i)

theorem offset_neg_bound (i : C.G.Col) :
    -(max_abs_offset C hints : ℤ) ≤ hints.e i := by
  have h := offset_le_max C hints i
  rcases Int.natAbs_eq (hints.e i) with heq | heq <;> omega

theorem offset_pos_bound (i : C.G.Col) :
    hints.e i ≤ (max_abs_offset C hints : ℤ) := by
  have h := offset_le_max C hints i
  rcases Int.natAbs_eq (hints.e i) with heq | heq <;> omega

theorem spacing_pos : 0 < spacing C hints := by unfold spacing; omega

theorem simple_r_strict_mono : StrictMono (simple_r C hints) := by
  intro j k hjk
  show base C hints + j.val * spacing C hints < base C hints + k.val * spacing C hints
  have := Nat.mul_lt_mul_of_pos_right hjk (spacing_pos C hints)
  omega

theorem simple_r_nonneg (i : C.G.Col) (j : C.G.Row) :
    0 ≤ (simple_r C hints j : ℤ) + hints.e i := by
  simp only [simple_r, base]
  have := offset_neg_bound C hints i
  omega

theorem simple_r_cross_row {j ℓ : C.G.Row} {i k : C.G.Col}
    (hne : j ≠ ℓ) :
    (simple_r C hints j : ℤ) + hints.e i ≠
    (simple_r C hints ℓ : ℤ) + hints.e k := by
  simp only [simple_r, base, spacing]
  intro heq
  push_cast at heq
  have hne' : (j.val : ℤ) ≠ ℓ.val := by exact_mod_cast Fin.val_ne_of_ne hne
  have hi := offset_neg_bound C hints i
  have hk := offset_pos_bound C hints k
  have hi' := offset_pos_bound C hints i
  have hk' := offset_neg_bound C hints k
  have hK_nn : (0 : ℤ) ≤ 1 + 2 * (max_abs_offset C hints : ℤ) := by omega
  rcases lt_or_gt_of_ne hne' with hjl | hjl
  · have h1 : (j.val : ℤ) + 1 ≤ ℓ.val := by omega
    nlinarith [mul_le_mul_of_nonneg_right h1 hK_nn]
  · have h1 : (ℓ.val : ℤ) + 1 ≤ j.val := by omega
    nlinarith [mul_le_mul_of_nonneg_right h1 hK_nn]

theorem simple_r_ok_for (hwf : HintsWellFormed C hints) :
    ok_for C hints Set.univ (simple_r C hints) := by
  intro entry _ hc
  refine ⟨simple_r_nonneg C hints entry.i entry.j, ?_⟩
  intro entry' _ hc' hne
  simp only [working_coord_map]
  intro heq
  simp only [Prod.mk.injEq] at heq
  obtain ⟨hh, hr⟩ := heq
  by_cases hrow : entry.j = entry'.j
  · have hsame : (simple_r C hints entry.j : ℤ) = (simple_r C hints entry'.j : ℤ) :=
      congr_arg (fun j => (simple_r C hints j : ℤ)) hrow
    have he : hints.e entry.i = hints.e entry'.i := by linarith
    have hcol := hwf entry.i entry'.i entry.j hc (hrow ▸ hc') hh he
    exact hne (by obtain ⟨_, _⟩ := entry; obtain ⟨_, _⟩ := entry'; simp_all)
  · exact simple_r_cross_row C hints hrow hr

end SimpleConstruction

noncomputable def find_row_mapping_wf (hwf : HintsWellFormed C hints) :
    ValidRowMapping C hints where
  r := simple_r C hints
  strict_mono := simple_r_strict_mono C hints
  valid := simple_r_ok_for C hints hwf

end FindRowMapping
