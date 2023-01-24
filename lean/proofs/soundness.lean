import .lemmas

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

lemma to_big_subst {v x e r} :
    subst v x e ⟹ r
  → big_subst [(x, v)] e ⟹ r :=
begin
  assume h,
  rw [big_subst, big_subst],
  exact h
end

lemma subst_bind {e x v r} :
    subst v x e ⟹ r
  → ([(x, v)], compile e ++ [ICloseScope], []) ⟹ₙᵥ ([], [r]) := 
begin
  assume h,
  apply from_interm_results' (subst_binds $ to_big_subst h),
  apply ERunCloseScope,
  apply ERunEmpty
end

lemma compile_sound' {e : exp} {v : val} :
    e ⟹ v
  → ([], compile e, []) ⟹ₙᵥ ([], [v]) :=
begin
  assume heval,
  induction' heval,
  case RunVal {
    rw compile,
    apply ERunPush,
    apply ERunEmpty
  },
  case RunOp {
    rw [compile, list.append_assoc],
    apply from_interm_results ih_heval_1,
    apply from_interm_results ih_heval,
    apply ERunOpInstr,
    apply ERunEmpty
  },
  case RunLet {
    rw [compile, list.append_assoc, list.cons_append],
    apply from_interm_results ih_heval,
    apply ERunOpenScope,
    apply subst_bind,
    apply heval_1
  }, 
  case RunIfT {
    rw [compile],
    simp,
    apply from_interm_results ih_heval,
    apply ERunTBranch,
    apply from_interm_results ih_heval_1,
    apply ERunJump,
    { rw [at_least], simp },
    { rw [list.drop_length],
      apply ERunEmpty }
  },
  case RunIfF {
    rw [compile],
    simp,
    apply from_interm_results ih_heval,
    apply ERunFBranch,
    { rw [at_least], simp },
    { rw [nat.add_comm, 
          list.drop_add, 
          list.drop_one,
          list.drop_append_of_le_length,
          list.drop_length,
          list.nil_append,
          list.tail],
      exact ih_heval_1,
      refl }
  }
end

lemma compile_sound (e : exp) (v : val) : 
    e ⟹ v
  → ([], compile e, []) ⟹ᵥₘ [v] :=
assume hstep, 
env_vm_big_step (compile_sound' hstep)