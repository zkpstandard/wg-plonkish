import Mathlib.Algebra.MvPolynomial.Variables

import ZKProof.Plonkish.Defs

/-!
# Unconstrained cells are fully unconstrained

Issue #66: prove that unconstrained abstract cells can take any value
without affecting circuit satisfaction.  This justifies the claim
(optimizations.md, line 477) that when unconstrained abstract cells
map to the same concrete cell as a constrained one, the effect is
harmless for both completeness and knowledge soundness.

## Main theorem

`R_parts_agree_on_constrained`: if two witnesses `w` and `w'` agree
on all spec-constrained cells, then `R_parts φ w ↔ R_parts φ w'`.

## Corollary

The abstract-to-concrete translation's round-trip differs from the
identity only at unconstrained cells, and the round-trip still
satisfies `R_parts`.  This is exactly the guarantee we need for
completeness and knowledge soundness preservation.

## Dependence on the "constrained" definition

As noted in the issue, this proof depends on:

1. **Fixed cells are constrained** (in our `spec_constrained`): the
   fixed-column check is included explicitly.  The plain
   `AbstractCircuit.constrained` omits this, relying on `≡` to relate
   fixed cells.  We use `spec_constrained` to cover both.

2. **`C.E` is an equivalence** (transitive, symmetric, reflexive):
   this is a field of `AbstractCircuit`.  Transitivity is used
   implicitly through `AbstractCircuit.constrained`'s use of "there
   exists a distinct `e'` with `C.E e e'`".

3. **Each abstract cell maps to at most one concrete cell**: this is
   definitional (`to_concrete` is a function).
-/

open MvPolynomial

variable {F : Type} [Field F]

namespace Unconstrained

/-- The "spec" notion of constrained: includes fixed-column cells.

    The `AbstractCircuit.constrained` definition in `Defs.lean` omits
    fixed cells, relying on them being captured by `≡`.  For the
    unconstrained-cell invariance theorem we need fixed cells treated
    explicitly. -/
def spec_constrained (C : AbstractCircuit F) (e : C.G.Entry) : Prop :=
  C.G.is_fixed e ∨ C.constrained e

/-! ## Main theorem: invariance at unconstrained cells -/

/-- If witnesses agree on variables of a polynomial, their row evaluations agree. -/
private theorem row_eval_congr_vars (C : AbstractCircuit F)
    {w w' : C.Witness} {j : C.G.Row} (p : C.RowPoly)
    (h : ∀ i ∈ p.vars, w { i := i, j := j } = w' { i := i, j := j }) :
    C.row_eval w j p = C.row_eval w' j p := by
  simp only [AbstractCircuit.row_eval]
  exact hom_congr_vars
    (by ext; simp [eval_C])
    (fun i hi _ => by simp [eval_X, AbstractCircuit.row_vec]; exact h i hi)
    rfl

/-- If `w` and `w'` agree on all spec-constrained cells, then `R_parts φ w`
    implies `R_parts φ w'`.

    This is the formal statement that unconstrained cells are fully
    unconstrained: their values don't affect any constraint. -/
theorem R_parts_agree_on_constrained (C : AbstractCircuit F) (φ : C.Instance)
    {w w' : C.Witness}
    (h_agree : ∀ e, spec_constrained C e → w e = w' e)
    (h_abs : C.R_parts φ w) : C.R_parts φ w' := by
  refine {
    fixed := fun e => ?_
    input := fun k => ?_
    equal := fun e e' equated => ?_
    custom := fun u j => ?_
    lookup := fun v j => ?_
  }
  · -- Fixed entries are spec_constrained
    have hsc : spec_constrained C e.val := Or.inl e.property
    rw [← h_agree e.val hsc]; exact h_abs.fixed e
  · -- C.S[k] is spec_constrained (input case)
    have hsc : spec_constrained C C.S[k] :=
      Or.inr (Or.inr (Or.inl ⟨k, rfl⟩))
    rw [← h_agree C.S[k] hsc]; exact h_abs.input k
  · -- For equality: if e ≠ e', both are spec_constrained (copy case)
    by_cases h : e = e'
    · rw [h]
    · have hsc_e : spec_constrained C e :=
        Or.inr (Or.inl ⟨e', h, equated⟩)
      have hsc_e' : spec_constrained C e' :=
        Or.inr (Or.inl ⟨e, (Ne.symm h), C.Equivalence_E.symm equated⟩)
      rw [← h_agree e hsc_e, ← h_agree e' hsc_e']
      exact h_abs.equal e e' equated
  · -- Custom: variables of p_u at row j are spec_constrained
    have h_eval : C.row_eval w' j (C.p u) = C.row_eval w j (C.p u) := by
      apply row_eval_congr_vars
      intro i hi
      have hsc : spec_constrained C { i := i, j := j.val } := by
        refine Or.inr (Or.inr (Or.inr (Or.inl ⟨u, j.property, ?_⟩)))
        -- i ∈ (C.p u).vars → has_support_involving (C.p u) i
        unfold AbstractCircuit.has_support_involving
        rw [mem_vars] at hi; obtain ⟨d, hd, hdi⟩ := hi
        exact ⟨⟨d, hd⟩, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hdi)⟩
      exact (h_agree _ hsc).symm
    rw [h_eval]; exact h_abs.custom u j
  · -- Lookup: variables of q_{v,s} at row j are spec_constrained
    have h_eval : (C.q v).map (C.row_eval w' j) = (C.q v).map (C.row_eval w j) := by
      apply Vector.ext; intro s hs
      simp only [Vector.getElem_map]
      apply row_eval_congr_vars
      intro i hi
      have hsc : spec_constrained C { i := i, j := j.val } := by
        refine Or.inr (Or.inr (Or.inr (Or.inr ⟨v, ⟨s, hs⟩, j.property, ?_⟩)))
        unfold AbstractCircuit.has_support_involving
        rw [mem_vars] at hi; obtain ⟨d, hd, hdi⟩ := hi
        exact ⟨⟨d, hd⟩, Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hdi)⟩
      exact (h_agree _ hsc).symm
    rw [h_eval]; exact h_abs.lookup v j

/-- Symmetric version: `R_parts` is preserved in both directions. -/
theorem R_parts_invariant_iff (C : AbstractCircuit F) (φ : C.Instance)
    {w w' : C.Witness}
    (h_agree : ∀ e, spec_constrained C e → w e = w' e) :
    C.R_parts φ w ↔ C.R_parts φ w' :=
  ⟨R_parts_agree_on_constrained C φ h_agree,
   R_parts_agree_on_constrained C φ (fun e hc => (h_agree e hc).symm)⟩

/-! ## Pointwise modification

A stronger formulation: modifying the witness at a single unconstrained
cell does not affect `R_parts`. -/

/-- Witness modification: change `w` at entry `e₀` to value `v`. -/
noncomputable def update {C : AbstractCircuit F}
    (w : C.Witness) (e₀ : C.G.Entry) (v : F) : C.Witness :=
  fun e => if e = e₀ then v else w e

/-- Modifying an unconstrained cell preserves `R_parts`. -/
theorem R_parts_update_unconstrained (C : AbstractCircuit F) (φ : C.Instance)
    (w : C.Witness) (e₀ : C.G.Entry) (v : F)
    (h_uncon : ¬ spec_constrained C e₀)
    (h_abs : C.R_parts φ w) :
    C.R_parts φ (update w e₀ v) := by
  apply R_parts_agree_on_constrained C φ _ h_abs
  intro e hsc
  simp only [update]
  split_ifs with h_eq
  · exact absurd (h_eq ▸ hsc) h_uncon
  · rfl

/-! ## Harmless overlap (the main claim from issue #66)

The claim: if a constrained abstract cell `e₀` and an unconstrained
abstract cell `e₁` map to the same concrete cell (via `to_concrete`),
then in the round-trip `F'(F(w))`:
  - `F'(F(w))[e₀] = w[e₀]` (preserved, since `e₀` is constrained)
  - `F'(F(w))[e₁] = w[e₀]` (may differ from `w[e₁]`, but `e₁` is unconstrained)

Therefore `F'(F(w))` still satisfies `R_parts`, as the modification
only happens at unconstrained cells. -/

/-- If a round-trip changes witness values only at unconstrained cells,
    `R_parts` is preserved. -/
theorem round_trip_preserves_R_parts (C : AbstractCircuit F) (φ : C.Instance)
    (w w_round : C.Witness)
    (h_preserved : ∀ e, spec_constrained C e → w_round e = w e)
    (h_abs : C.R_parts φ w) : C.R_parts φ w_round :=
  R_parts_agree_on_constrained C φ (fun e hc => (h_preserved e hc).symm) h_abs

end Unconstrained
