import .lemmas

open big_step vm_big_step env_big_step val bin_op exp instruction

lemma from_interm_results_vm {E e}
  {P : list instruction} {S S' I R : list val} :
    (E, compile e, S) ⟹ᵥₘ I 
  → (E, P, I ++ S') ⟹ᵥₘ R
  → (E, compile e ++ P, S ++ S') ⟹ᵥₘ R :=
begin
  sorry
end

lemma from_interm_results_vm' {E e}
  {P : list instruction} {S I R : list val} :
    (E, compile e, S) ⟹ᵥₘ I → (E, P, I) ⟹ᵥₘ R
  → (E, compile e ++ P, S) ⟹ᵥₘ R :=
begin
  sorry
end
/-begin
  assume h1 h2,
  rw ←list.append_nil I at h2,
  rw ←list.append_nil S,
  exact from_interm_results_vm h1 h2
end-/

lemma to_interm_results_vm {E e P S S' r} :
  (E, compile e ++ P, S) ⟹ᵥₘ r :: S'
  → ∃ v, (E, compile e, S) ⟹ᵥₘ v :: S ∧ 
         (E, P, v :: S) ⟹ᵥₘ r :: S' :=
begin
  assume hvm,
  induction' e,
  case EVal {
    rw compile at hvm ⊢,
    cases' hvm,
    use v,
    apply and.intro,
    { apply RunPush,
      exact RunEmpty },
    { exact hvm }
  },
  case EOp {
    rw compile at hvm ⊢,
    simp at hvm ⊢,
    cases' ih_e_1 hvm,
    cases' h with he_1 h,
    cases' ih_e h with u h',
    cases' h' with he h',
    cases' h',
    use eval n m op,
    apply and.intro,
    { apply from_interm_results_vm' he_1,
      apply from_interm_results_vm' he,
      apply RunOpInstr,
      exact RunEmpty },
    { exact h' }
  },
  case EIf {
    sorry
  },
  case EVar {
    rw compile at hvm ⊢,
    cases' hvm,
    use v,
    apply and.intro,
    { apply RunLookup _x,
      exact RunEmpty },
    { exact hvm }
  },
  case ELet {
    rw compile at hvm ⊢,
    simp at hvm ⊢,
    cases' ih_e hvm,
    cases' h with he h,
    cases' h,
    cases' ih_e_1 h with u h',
    cases' h' with he_1 h',
    cases' h',
    use u,
    apply and.intro,
    { apply from_interm_results_vm' he,
      apply RunOpenScope,
      apply from_interm_results_vm' he_1,
      apply RunCloseScope,
      exact RunEmpty },
    { exact h' }
  }
end


lemma vm_env_big_step {E e S r} : 
    (E, compile e, S) ⟹ᵥₘ r :: S
  → (E, compile e, S) ⟹ₙᵥ (E, r :: S) :=
begin
  assume hnv,
  induction' e,
  case EVal {
    rw compile at ⊢ hnv,
    cases' hnv, cases' hnv,
    apply ERunPush,
    exact ERunEmpty
  },
  case EOp {
    rw compile at ⊢ hnv,
    simp at ⊢ hnv,
    cases' to_interm_results_vm hnv with v,
    cases' h with he_1 h,
    cases' to_interm_results_vm h with u h',
    cases' h' with he h',
    cases' h', cases' h',
    apply from_interm_results' (ih_e_1 he_1),
    apply from_interm_results' (ih_e he),
    apply ERunOpInstr,
    exact ERunEmpty
  },
  case EIf {
    rw compile at ⊢ hnv,
    simp at ⊢ hnv,
    cases' to_interm_results_vm hnv with v,
    cases' h with he h,
    cases' h,
    case RunTBranch {
      cases' to_interm_results_vm h with u h',
      cases' h' with he_1 h',
      cases' h', 
      rw list.drop_length at h', 
      cases h',
      apply from_interm_results' (ih_e he),
      apply ERunTBranch,
      apply from_interm_results' (ih_e_1 he_1),
      apply ERunJump _x,
      rw list.drop_length,
      exact ERunEmpty
    },
    case RunFBranch {
      apply from_interm_results' (ih_e he),
      apply ERunFBranch _x,
      rw [nat.add_comm, 
          list.drop_add, 
          list.drop_one,
          list.drop_append_of_le_length,
          list.drop_length,
          list.nil_append,
          list.tail] at ⊢ h,
      exact ih_e_2 h,
      refl, refl
    }
  },
  case EVar {
    rw compile at ⊢ hnv,
    cases' hnv, cases' hnv,
    apply ERunLookup _x,
    exact ERunEmpty
  },
  case ELet {
    rw compile at ⊢ hnv,
    simp at ⊢ hnv,
    cases' (to_interm_results_vm hnv) with v,
    cases' h with he h,
    cases' h,
    cases' (to_interm_results_vm h) with u h',
    cases' h' with he_1 h',
    cases' h', cases' h',
    apply (from_interm_results' $ ih_e he),
    apply ERunOpenScope,
    apply (from_interm_results' $ ih_e_1 he_1),
    apply ERunCloseScope,
    exact ERunEmpty
  }
end

lemma bind_substs {E e S r} : 
  (E, compile e, S) ⟹ₙᵥ (E, r :: S)
  → big_subst E e ⟹ r :=
begin
  assume h,
  sorry -- induction' e,
end

lemma bind_subst {x v e S r} : 
  ([(x, v)], compile e, S) ⟹ₙᵥ ([(x, v)], r :: S)
  → subst v x e ⟹ r :=
begin
  assume h,
  rw ←single_big_subst_is_subst,
  apply bind_substs h
end

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
    sorry -- just lazy, can do
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

lemma compile_complete {e : exp} {r : val}:
  ([], compile e, []) ⟹ᵥₘ [r] 
  → e ⟹ r :=
compile_complete_nv ∘ vm_env_big_step