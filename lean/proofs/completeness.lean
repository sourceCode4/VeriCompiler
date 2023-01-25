import .lemmas.substitution
import .lemmas.big_step

open big_step vm_big_step env_big_step val bin_op exp instruction

lemma bind_substs {E e S r} : 
  (E, compile e, S) ⟹ₙᵥ (E, r :: S)
  → big_subst E e ⟹ r :=
begin
  assume h,
  induction' e,
  case EVal {
    rw compile at h,
    cases' h, cases' h,
    rw big_subst_val,
    apply RunVal
  },
  case EOp {
    rw compile at h, simp at h,
    rw big_subst_spread_op,
    cases' to_interm_results h with v h',
    cases' h' with he_1 h',
    cases' to_interm_results h' with u h'',
    cases' h'' with he h'',
    cases' h'', cases' h'',
    apply RunOp,
    exact ih_e he,
    exact ih_e_1 he_1
  },
  case EIf {
    rw compile at h, simp at h,
    rw big_subst_spread_if,
    cases' to_interm_results h with v h',
    cases' h' with he h',
    cases h',
    case ERunTBranch {
      cases' to_interm_results h'__x with u,
      cases' h_1 with he_1 h_1,
      cases' h_1,
      rw list.drop_length at h_1,
      cases' h_1,
      apply RunIfT,
      exact ih_e he,
      exact ih_e_1 he_1
    },
    case ERunFBranch {
      rename [h'__x hle, h'__x_1 he_2],
      simp at he_2,
      have H : ∀ xs, (compile e_1).append xs = compile e_1 ++ xs,
        assume xs, by refl,
      rw [nat.succ_eq_add_one,
          nat.add_comm, 
          list.drop_add, 
          list.drop_one, H,
          list.drop_append_of_le_length,
          list.drop_length,
          list.nil_append,
          list.tail] at he_2,
      apply RunIfF,
      exact ih_e he,
      exact ih_e_2 he_2,
      refl
    }
  },
  case EVar {
    rw compile at h,
    cases' h, cases' h,
    induction' _x,
    case bhead {
      rw [big_subst, subst, if_pos (eq.refl x), big_subst_val],
      apply RunVal
    },
    case btail {
      rw [big_subst, subst, if_neg h.symm],
      exact ih
    }
  },
  case ELet {
    rw compile at h, simp at h,
    cases' to_interm_results h with v h',
    cases' h' with he h',
    cases' h',
    cases' to_interm_results h' with u h'',
    cases' h'' with he_1 h'',
    cases' h'', cases' h'',
    rw big_subst_spread_let,
    apply RunLet,
    exact ih_e he,
    rw [subst_merge, big_subst_remove_append],
    exact ih_e_1 he_1
  }
end

lemma compile_complete_nv
  {e : exp} {r : val} {S : list val} :
    ([], compile e, []) ⟹ₙᵥ ([], [r])
  → e ⟹ r :=
assume h,
have H : _ := bind_substs h,
by rw big_subst at H; exact H