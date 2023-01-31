import 
  .lemmas.substitution
  .lemmas.big_step

open env_big_step

lemma big_subst_sound {E e S r} :
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
  case EVar {
    rw compile,
    cases' big_subst_var_implies_bound h with v hbound,
    apply ERunLookup hbound,
    rw big_subst_bound_var hbound h,
    exact ERunEmpty
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
      exact at_least_refl,
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

theorem compile_sound_nv {e : exp} {v : val} :
    e ⟹ v
  → ([], compile e, []) ⟹ₙᵥ ([], [v]) :=
λ h, big_subst_sound $ eq.subst (big_subst_empty e) h

theorem compile_sound (e : exp) (v : val) : 
    e ⟹ v
  → ([], compile e, []) ⟹ᵥₘ [v] :=
env_vm_big_step ∘ compile_sound_nv