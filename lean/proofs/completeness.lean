import .lemmas.substitution
import .lemmas.conversion

open big_step vm_big_step env_big_step val bin_op exp instruction

lemma to_interm_results {E₁ E₂ e P S S' r} :
  (E₁, compile e ++ P, S) ⟹ₙᵥ (E₂, r :: S')
  → ∃ v, (E₁, compile e, S) ⟹ₙᵥ (E₁, v :: S) ∧ 
          (E₁, P, v :: S) ⟹ₙᵥ (E₂, r :: S') :=
begin
  assume hnv,
  induction' e,
  case EVal {
    rw compile at hnv ⊢,
    cases' hnv,
    use v,
    apply and.intro,
    { apply ERunPush,
      exact ERunEmpty },
    { exact hnv }
  },
  case EOp {
    rw compile at hnv ⊢,
    simp at hnv ⊢,
    cases' ih_e_1 hnv,
    cases' h with he_1 h,
    cases' ih_e h with u h',
    cases' h' with he h',
    cases' h',
    use eval n m op,
    apply and.intro,
    { apply from_interm_results' he_1,
      apply from_interm_results' he,
      apply ERunOpInstr,
      exact ERunEmpty },
    { exact h' }
  },
  case EIf {
    rw compile at hnv ⊢,
    simp at hnv ⊢,
    cases' ih_e hnv, clear hnv,
    cases' h with he h,
    cases' h,
    case ERunTBranch {
      cases' ih_e_1 h with w h',
      cases' h' with he_1 h',
      cases' h',
      rw [list.drop_append_of_le_length,
          list.drop_length,
          list.nil_append] at h',
      use w,
      apply and.intro,
      { apply from_interm_results' he,
        apply ERunTBranch,
        apply from_interm_results' he_1,
        apply ERunJump,
        exact at_least_refl,
        rw list.drop_length,
        exact ERunEmpty },
      { exact h' },
      refl
    },
    case ERunFBranch {
      rw [nat.add_comm, 
          list.drop_add, 
          list.drop_one,
          list.drop_append_of_le_length,
          list.drop_length,
          list.nil_append,
          list.tail] at h,
      cases' ih_e_2 h with w h',
      cases' h' with he_2 h',
      use w,
      apply and.intro,
      { apply from_interm_results' he,
        apply ERunFBranch,
        { rw [at_least, 
              list.length_append, 
              list.length_cons], 
          linarith },
        rw [nat.add_comm, 
            list.drop_add, 
            list.drop_one,
            list.drop_append_of_le_length,
            list.drop_length,
            list.nil_append,
            list.tail],
        exact he_2,
        refl },
      { exact h' },
      refl
    }
  },
  case EVar {
    rw compile at hnv ⊢,
    cases' hnv,
    use v,
    apply and.intro,
    { apply ERunLookup _x,
      exact ERunEmpty },
    { exact hnv }
  },
  case ELet {
    rw compile at hnv ⊢,
    simp at hnv ⊢,
    cases' ih_e hnv,
    cases' h with he h,
    cases' h,
    cases' ih_e_1 h with u h',
    cases' h' with he_1 h',
    cases' h',
    use u,
    apply and.intro,
    { apply from_interm_results' he,
      apply ERunOpenScope,
      apply from_interm_results' he_1,
      apply ERunCloseScope,
      exact ERunEmpty },
    { exact h' }
  }
end


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

lemma bind_subst {x v e S r} : 
  ([(x, v)], compile e, S) ⟹ₙᵥ ([(x, v)], r :: S)
  → subst v x e ⟹ r :=
begin
  assume h,
  rw ←single_big_subst_is_subst,
  apply bind_substs h
end

lemma compile_complete_nv 
  {e : exp} {r : val} {S : list val} :
    ([], compile e, S) ⟹ₙᵥ ([], r :: S)
  → e ⟹ r :=
begin
  assume hnval,
  induction' e,
  case EVal {
    rw compile at hnval,
    cases' hnval,
    cases' hnval,
    exact RunVal
  },
  case EOp {
    rw compile at hnval,
    simp at hnval,
    cases' (to_interm_results hnval) with v,
    cases' h with h1 h2,
    cases' (to_interm_results h2) with w,
    cases' h with h3 h4,
    cases' h4,
    cases' h4,
    apply RunOp,
    exact ih_e h3,
    exact ih_e_1 h1
  },
  case EIf {
    rw compile at hnval, 
    simp at hnval,
    cases' (to_interm_results hnval) with v,
    cases' h with he h,
    cases' h,
    case ERunTBranch {
      cases' (to_interm_results h) with w h',
      cases' h' with he_1 h',
      cases' h',
      rw list.drop_length at h',
      cases' h',
      apply RunIfT,
      exact ih_e he,
      exact ih_e_1 he_1
    },
    case ERunFBranch {
      rw [nat.add_comm, 
          list.drop_add, 
          list.drop_one,
          list.drop_append_of_le_length,
          list.drop_length,
          list.nil_append,
          list.tail] at h,
      { apply RunIfF,
        exact ih_e he,
        exact ih_e_2 h },
      { refl }
    }
  },
  case EVar {
    rw compile at hnval,
    cases' hnval,
    cases' _x
  },
  case ELet {
    rw compile at hnval, 
    simp at hnval,
    cases' (to_interm_results hnval) with v,
    cases' h with he h,
    cases' h,
    cases' (to_interm_results h) with u h',
    cases' h' with he_1 h',
    cases' h',
    cases' h',
    apply RunLet,
    exact ih_e he,
    exact bind_subst he_1
  }
end