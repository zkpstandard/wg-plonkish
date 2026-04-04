import Mathlib.Algebra.MvPolynomial.Variables

import ZKProof.Plonkish.Defs
import ZKProof.Plonkish.Concrete
import ZKProof.Plonkish.Hints
import ZKProof.Plonkish.FindRowMapping

open Classical MvPolynomial

variable {F : Type} [Field F]

namespace Correctness

variable (C : AbstractCircuit F) (hints : Hints C.G)
         (hwf : FindRowMapping.HintsWellFormed C hints)

noncomputable def vrm := FindRowMapping.find_row_mapping_wf C hints hwf
noncomputable def m'_nat : ℕ := (Finset.univ : Finset C.G.Col).sup hints.h + 1
noncomputable def n'_nat : ℕ :=
  FindRowMapping.base C hints + C.G.n.val * FindRowMapping.spacing C hints +
  FindRowMapping.max_abs_offset C hints + 1

theorem col_in_bounds (i : C.G.Col) : hints.h i < m'_nat C hints := by
  unfold m'_nat; exact Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ i))

theorem row_nonneg (e : C.G.Entry) :
    0 ≤ ((vrm C hints hwf).r e.j : ℤ) + hints.e e.i :=
  FindRowMapping.simple_r_nonneg C hints e.i e.j

theorem row_in_bounds (e : C.G.Entry) :
    (((vrm C hints hwf).r e.j : ℤ) + hints.e e.i).toNat < n'_nat C hints := by
  have h_nn := row_nonneg C hints hwf e
  suffices ((vrm C hints hwf).r e.j : ℤ) + hints.e e.i < (n'_nat C hints : ℤ) by omega
  simp only [vrm, FindRowMapping.find_row_mapping_wf, FindRowMapping.simple_r,
             FindRowMapping.base, FindRowMapping.spacing, n'_nat]; push_cast
  linarith [FindRowMapping.offset_pos_bound C hints e.i,
            show (e.j.val : ℤ) * (1 + 2 * ↑(FindRowMapping.max_abs_offset C hints)) <
                 (C.G.n.val : ℤ) * (1 + 2 * ↑(FindRowMapping.max_abs_offset C hints)) from
              by exact_mod_cast Nat.mul_lt_mul_of_pos_right e.j.isLt
                   (FindRowMapping.spacing_pos C hints)]

abbrev CEntry := Fin (m'_nat C hints) × Fin (n'_nat C hints)

noncomputable def to_concrete (e : C.G.Entry) : CEntry C hints :=
  (⟨hints.h e.i, col_in_bounds C hints e.i⟩,
   ⟨(((vrm C hints hwf).r e.j : ℤ) + hints.e e.i).toNat, row_in_bounds C hints hwf e⟩)

theorem to_concrete_injective {e e' : C.G.Entry}
    (hc : FindRowMapping.spec_constrained C e)
    (hc' : FindRowMapping.spec_constrained C e')
    (hne : e ≠ e') :
    to_concrete C hints hwf e ≠ to_concrete C hints hwf e' := by
  intro heq
  simp only [to_concrete, Prod.mk.injEq, Fin.mk.injEq] at heq
  apply (vrm C hints hwf).coord_map_injective e e' hc hc' hne
  simp only [FindRowMapping.ValidRowMapping.coord_map, FindRowMapping.working_coord_map]
  have h1 := row_nonneg C hints hwf e; have h2 := row_nonneg C hints hwf e'
  exact Prod.ext heq.1 (by omega)

/-! ## Witness translations -/

noncomputable def witness_pullback (w' : CEntry C hints → F) : C.Witness :=
  fun e => w' (to_concrete C hints hwf e)

noncomputable def witness_push (w : C.Witness) : CEntry C hints → F :=
  fun e' =>
    if h : ∃ e : C.G.Entry,
        FindRowMapping.spec_constrained C e ∧ to_concrete C hints hwf e = e'
    then w (choose h) else 0

theorem push_then_pull (w : C.Witness) (e : C.G.Entry)
    (hc : FindRowMapping.spec_constrained C e) :
    witness_pullback C hints hwf (witness_push C hints hwf w) e = w e := by
  simp only [witness_pullback, witness_push]
  have hex : ∃ e₀ : C.G.Entry,
      FindRowMapping.spec_constrained C e₀ ∧ to_concrete C hints hwf e₀ =
      to_concrete C hints hwf e := ⟨e, hc, rfl⟩
  rw [dif_pos hex]
  have h_spec := choose_spec hex
  -- choose hex is some e₀ with spec_constrained e₀ and to_concrete e₀ = to_concrete e
  -- By injectivity on constrained cells, e₀ = e
  by_contra h_val
  -- h_val : w (choose hex) ≠ w e, but we actually need choose hex ≠ e
  -- Use the contrapositive: if choose hex ≠ e, to_concrete differs
  suffices h_eq : choose hex = e by exact h_val (by rw [h_eq])
  by_contra h_ne
  exact absurd h_spec.2 (to_concrete_injective C hints hwf h_spec.1 hc h_ne)

/-! ## Concrete relation -/

noncomputable def R_concrete : Rel C.Instance (CEntry C hints → F) :=
  { (φ, w') | C.R_parts φ (witness_pullback C hints hwf w') }

/-! ## Spec_constrained witnesses -/

theorem fixed_sc (e : C.G.FixedEntry) :
    FindRowMapping.spec_constrained C e.val := by left; exact e.property

theorem input_sc (k : C.Input) :
    FindRowMapping.spec_constrained C C.S[k] := by
  delta FindRowMapping.spec_constrained AbstractCircuit.constrained
  right; right; left; exact ⟨k, rfl⟩

theorem copy_sc {e e' : C.G.Entry} (hne : e ≠ e') (h : C.E e e') :
    FindRowMapping.spec_constrained C e := by
  delta FindRowMapping.spec_constrained AbstractCircuit.constrained
  right; left; exact ⟨e', hne, h⟩

private theorem vars_to_support {p : MvPolynomial C.G.Col F} {i : C.G.Col}
    (hi : i ∈ p.vars) : C.has_support_involving p i := by
  unfold AbstractCircuit.has_support_involving
  rw [mem_vars] at hi; obtain ⟨d, hd, hdi⟩ := hi
  have h_ne := Finsupp.mem_support_iff.mp hdi
  exact ⟨⟨d, hd⟩, Nat.pos_of_ne_zero h_ne⟩

theorem custom_var_sc {u : Fin C.U} {j : C.G.Row} (hj : j ∈ C.CUS u)
    {i : C.G.Col} (hi : i ∈ (C.p u).vars) :
    FindRowMapping.spec_constrained C { i := i, j := j } := by
  unfold FindRowMapping.spec_constrained AbstractCircuit.constrained
  right; exact Or.inr (Or.inr (Or.inl ⟨u, hj, vars_to_support C hi⟩))

theorem lookup_var_sc {v : Fin C.V} {s : Fin (C.L v)} {j : C.G.Row}
    (hj : j ∈ C.LOOK v) {i : C.G.Col} (hi : i ∈ ((C.q v)[s]).vars) :
    FindRowMapping.spec_constrained C { i := i, j := j } := by
  unfold FindRowMapping.spec_constrained AbstractCircuit.constrained
  right; exact Or.inr (Or.inr (Or.inr ⟨v, s, hj, vars_to_support C hi⟩))

/-! ## Polynomial evaluation lemma -/

theorem eval_congr_vars {σ : Type*} [DecidableEq σ] {R : Type*} [CommSemiring R]
    {f g : σ → R} {p : MvPolynomial σ R}
    (h : ∀ i ∈ p.vars, f i = g i) : eval f p = eval g p :=
  hom_congr_vars (by ext; simp [eval_C]) (fun i hi _ => by simp [eval_X]; exact h i hi) rfl

/-! ## Row evaluation round-trip -/

theorem row_eval_round_trip (w : C.Witness) (u : Fin C.U) (j : C.CUS u) :
    C.row_eval (witness_pullback C hints hwf (witness_push C hints hwf w)) j (C.p u) =
    C.row_eval w j (C.p u) := by
  simp only [AbstractCircuit.row_eval]
  apply eval_congr_vars; intro i hi
  show (witness_pullback C hints hwf (witness_push C hints hwf w)) { i := i, j := j.val } =
       w { i := i, j := j.val }
  exact push_then_pull C hints hwf w _ (custom_var_sc C j.property hi)

theorem lookup_eval_round_trip (w : C.Witness) (v : Fin C.V) (j : C.LOOK v)
    (s : Fin (C.L v)) :
    C.row_eval (witness_pullback C hints hwf (witness_push C hints hwf w)) j ((C.q v)[s]) =
    C.row_eval w j ((C.q v)[s]) := by
  simp only [AbstractCircuit.row_eval]
  apply eval_congr_vars; intro i hi
  exact push_then_pull C hints hwf w _ (lookup_var_sc C (s := s) j.property hi)

/-! ## Completeness -/

noncomputable def complete :
    Complete (SimpleRefinement C.R (R_concrete C hints hwf)) := by
  intro φ ⟨w, h_abs⟩
  refine ⟨witness_push C hints hwf w, ?_⟩
  exact {
    fixed := fun e => by
      rw [push_then_pull C hints hwf w e (fixed_sc C e)]; exact h_abs.fixed e
    input := fun k => by
      rw [push_then_pull C hints hwf w _ (input_sc C k)]; exact h_abs.input k
    equal := fun e e' equated => by
      show witness_pullback C hints hwf (witness_push C hints hwf w) e =
           witness_pullback C hints hwf (witness_push C hints hwf w) e'
      by_cases h : e = e'
      · rw [h]
      · rw [push_then_pull C hints hwf w e (copy_sc C h equated),
            push_then_pull C hints hwf w e'
              (copy_sc C (Ne.symm h) (C.Equivalence_E.symm equated))]
        exact h_abs.equal e e' equated
    custom := fun u j => by
      rw [row_eval_round_trip C hints hwf w u j]; exact h_abs.custom u j
    lookup := fun v j => by
      show (C.q v).map
        (C.row_eval (witness_pullback C hints hwf (witness_push C hints hwf w)) j) ∈ C.TAB v
      have h_eq : (C.q v).map
          (C.row_eval (witness_pullback C hints hwf (witness_push C hints hwf w)) j) =
          (C.q v).map (C.row_eval w j) := by
        apply Vector.ext; intro i hi
        simp only [Vector.getElem_map]
        exact lookup_eval_round_trip C hints hwf w v j ⟨i, hi⟩
      rw [h_eq]; exact h_abs.lookup v j
  }

/-! ## Knowledge soundness -/

noncomputable def knowledge_sound :
    KnowledgeSound (SimpleRefinement C.R (R_concrete C hints hwf)) := by
  intro φ ⟨w', h_conc⟩
  exact ⟨witness_pullback C hints hwf w', h_conc⟩

/-! ## Main theorem -/

noncomputable def translation_correct :
    RichRefinement (SimpleRefinement C.R (R_concrete C hints hwf)) where
  complete := some (complete C hints hwf)
  soundness := .knowledge_sound (knowledge_sound C hints hwf)

theorem translation_is_correct :
    (translation_correct C hints hwf).correct :=
  ⟨rfl, rfl⟩

end Correctness
