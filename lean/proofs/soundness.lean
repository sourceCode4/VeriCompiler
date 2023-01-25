import .lemmas.substitution
import .lemmas.big_step

open big_step vm_big_step env_big_step val bin_op exp instruction

lemma subst_binds {E e S r} :
    big_subst E e ⟹ r
  → (E, compile e, S) ⟹ₙᵥ (E, r :: S) := 
begin
  assume h,
  induction' e,
  case EVal {
    rw compile,
    rw big_subst_val at h,
    cases' h,
    apply ERunPush,
    apply ERunEmpty
  },
  case EOp {
    rw compile, simp,
    rw big_subst_spread_op at h,
    cases' h,
    apply from_interm_results' (ih_e_1 h_1),
    apply from_interm_results' (ih_e h),
    apply ERunOpInstr,
    apply ERunEmpty
  },
  case EIf {
    rw compile, simp,
    rw big_subst_spread_if at h,
    cases' h,
    case RunIfT { 
      apply from_interm_results' (ih_e h),
      apply ERunTBranch,
      apply from_interm_results' (ih_e_1 h_1),
      apply ERunJump,
      { rw at_least, simp },
      rw list.drop_length,
      apply ERunEmpty
    },
    case RunIfF {
      apply from_interm_results' (ih_e h),
      apply ERunFBranch,
      { rw [at_least], simp },
      rw [nat.add_comm, 
          list.drop_add, 
          list.drop_one,
          list.drop_append_of_le_length, 
          list.drop_length,
          list.nil_append, 
          list.tail],
      exact ih_e_2 h_1,
      refl
    }
  },
  case EVar {
    rw compile,
    apply dite (∃v, bound s v E), {
      assume hex,
      cases' hex with v hbound,
      apply ERunLookup hbound,
      rw big_subst_bound_res hbound h,
      exact ERunEmpty
    }, {
      assume hnex,
      apply false.elim,
      apply hnex,
      apply big_subst_var_implies_bound h
    }
  },
  case ELet {
    rw compile, simp,
    rw big_subst_spread_let at h,
    cases' h,
    apply from_interm_results' (ih_e h),
    apply ERunOpenScope,
    rw [subst_merge, 
      big_subst_remove_append] at h_1,
    apply from_interm_results' (ih_e_1 h_1),
    apply ERunCloseScope,
    apply ERunEmpty
  }
end

lemma compile_sound_nv {e : exp} {v : val} :
    e ⟹ v
  → ([], compile e, []) ⟹ₙᵥ ([], [v]) :=
assume h,
by rw ←big_subst_empty e at h; exact subst_binds h

lemma compile_sound (e : exp) (v : val) : 
    e ⟹ v
  → ([], compile e, []) ⟹ᵥₘ [v] :=
assume hstep, 
env_vm_big_step (compile_sound_nv hstep)