import .lemmas

open big_step vm_big_step env_big_step val bin_op exp instruction

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
    apply interm_result ih_heval_1,
    apply interm_result ih_heval,
    apply ERunOpInstr,
    apply ERunEmpty
  },
  case RunLet {
    rw [compile, list.append_assoc, list.cons_append],
    apply interm_result ih_heval,
    apply ERunOpenScope,
    apply subst_extra_bind,
    apply heval_1
  }, 
  case RunIfT {
    rw [compile],
    simp,
    apply interm_result ih_heval,
    apply ERunTBranch,
    apply interm_result ih_heval_1,
    apply ERunJump,
    { rw [at_least], simp },
    { rw [list.drop_length],
      apply ERunEmpty }
  },
  case RunIfF {
    rw [compile],
    simp,
    apply interm_result ih_heval,
    apply ERunFBranch,
    { rw [at_least, list.length_append],
      simp },
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