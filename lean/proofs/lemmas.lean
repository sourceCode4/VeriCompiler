import ..syntax .decidability

open big_step vm_big_step env_big_step val bin_op exp instruction

-- env_big_step implies vm_big_step
lemma env_vm_big_step {env env' P S R} :
    (env, P, S) ⟹ₙᵥ (env', R)
  → (env, P, S) ⟹ᵥₘ R :=
begin
  assume hnv,
  induction' hnv,
  case ERunEmpty {
    apply RunEmpty
  },
  case ERunPush {
    apply RunPush,
    exact ih
  },
  case ERunOpInstr {
    apply RunOpInstr,
    exact ih
  },
  case ERunTBranch {
    apply RunTBranch,
    exact ih
  },
  case ERunFBranch {
    apply RunFBranch,
    { exact _x },
    { exact ih }
  },
  case ERunJump {
    apply RunJump,
    { exact _x },
    { exact ih }
  },
  case ERunLookup {
    apply RunLookup,
    { exact _x },
    { exact ih }
  },
  case ERunOpenScope {
    apply RunOpenScope,
    exact ih
  },
  case ERunCloseScope {
    apply RunCloseScope,
    exact ih
  }
end

-- generalized intermediate_result lemma
lemma interm_result
  {P₁ P₂ : list instruction} {S S' I : list val} {E₁ E₂ Eᵢ R} :
    (E₁, P₁, S) ⟹ₙᵥ (Eᵢ, I)
  → (Eᵢ, P₂, I ++ S') ⟹ₙᵥ (E₂, R)
  → (E₁, P₁ ++ P₂, S ++ S') ⟹ₙᵥ (E₂, R) :=
begin
  assume h1 h2,
  induction' h1,
  { exact h2 },
  { apply ERunPush,
    rw ←list.cons_append,
    apply ih h2 },
  case ERunOpInstr {
    rw list.cons_append,
    apply ERunOpInstr,
    apply ih h2
  },
  case ERunTBranch {
    rw list.cons_append,
    apply ERunTBranch,
    apply ih h2
  },
  case ERunFBranch {
    rw list.cons_append,
    apply ERunFBranch,
    { rw [at_least, list.length_append], 
      rw [at_least] at _x,
      linarith },
    rw [list.drop_append_of_le_length],
    apply ih h2,
    exact _x
  },
  case ERunJump {
    rw list.cons_append,
    apply ERunJump,
    { rw [at_least, list.length_append], 
      rw [at_least] at _x,
      linarith },
    rw [list.drop_append_of_le_length],
    apply ih h2,
    exact _x
  },
  case ERunLookup {
    apply ERunLookup _x,
    rw ←list.cons_append,
    apply ih h2
  },
  case ERunOpenScope {
    rw list.cons_append,
    apply ERunOpenScope,
    apply ih h2
  },
  case ERunCloseScope {
    rw list.cons_append,
    apply ERunCloseScope,
    apply ih h2
  }
end

lemma interm_result_nil
  {P₁ P₂ S I E₁ E₂ Eᵢ R} :
    (E₁, P₁, S) ⟹ₙᵥ (Eᵢ, I)
  → (Eᵢ, P₂, I) ⟹ₙᵥ (E₂, R)
  → (E₁, P₁ ++ P₂, S) ⟹ₙᵥ (E₂, R) :=
begin
  assume h1 h2,
  rw ←list.append_nil I at h2,
  rw ←list.append_nil S,
  exact interm_result h1 h2
end

lemma interm_result_tail
  {P₁ P₂ S I E₁ E₂ Eᵢ R} :
    (Eᵢ, P₂, I) ⟹ₙᵥ (E₂, R)
  → (E₁, P₁, S) ⟹ₙᵥ (Eᵢ, I)
  → (E₁, P₁ ++ P₂, S) ⟹ₙᵥ (E₂, R) :=
begin
  assume h2 h1,
  apply interm_result_nil h1 h2
end

lemma push_on_stack {P v S R env} : 
    (env, IPush v :: P, S) ⟹ₙᵥ R
  ↔ (env, P, [v] ++ S) ⟹ₙᵥ R :=
begin
  apply iff.intro,
  { intro h,
    cases' h,
    exact h },
  { intro h,
    apply ERunPush,
    exact h }
end

lemma eq_if_bound_to_same_name {x v u env} : 
    bound x v env → bound x u env 
  → v = u :=
begin
  assume h1 h2,
  induction' env,
  case nil { cases' h1 },
  case cons {
    apply dite (hd = ⟨x, v⟩),
  }
end

lemma bound_lookup {E x v P S R} : 
    bound x v E
  → (E, ILookup x :: P, S) ⟹ₙᵥ R
  → (E, P, v :: S) ⟹ₙᵥ R :=
begin
  assume hbound heval,
  cases' heval,
  sorry
end

lemma vm_subst_eq : ∀ v x P,
    vm_subst' v x [] P = vm_subst v x P :=
by rw vm_subst

lemma vm_subst_distr {E v x P₁ P₂ S R} : 
    (E, vm_subst v x (P₁ ++ P₂), S) ⟹ₙᵥ R
  → (E, vm_subst v x P₁ ++ vm_subst v x P₂, S) ⟹ₙᵥ R :=
begin
  assume h,
  rw [vm_subst] at h,
  induction' P₁,
  case nil { finish },
  case cons {
    rw vm_subst,
    cases' hd,
    case ILookup {
      simp at h,
      rw [vm_subst'] at ⊢ h,
      simp at ⊢ h,
      apply dite (s = x),
      { assume heq,
        rw if_pos heq at ⊢ h,
        rw vm_subst_eq,
        rw push_on_stack at h,
        apply ERunPush,
        exact ih h },
      { assume hne,
        rw if_neg hne at ⊢ h,
        rw [vm_subst_eq, vm_subst_eq],
        apply dite (∃ v, bound s v E),
        {
          assume hex,
          cases' hex,
          apply ERunLookup h_1,
          cases' h,
          apply ih h,
        },
        {
          assume hnex,
          cases' h,
          apply false.elim,
          apply hnex,
          apply exists.intro,
          exact _x
        }
        }
    },

  }
end

lemma subst_vm_subst {E e x v S R} : 
    (E, compile (subst v x e), S) ⟹ₙᵥ R
  → (E, vm_subst v x (compile e), S) ⟹ₙᵥ R :=
begin
  assume h,
  induction' h, -- or h?
  case ELet {
    rw [subst] at h,
    
  }
end

lemma extra_bind {E e x v S r} : 
    (E, compile (subst v x e), S) ⟹ₙᵥ (E, r :: S)
  → (⟨x, v⟩ :: E, compile e, S) ⟹ₙᵥ (⟨x, v⟩ :: E, r :: S) :=
begin
  sorry
end

lemma subst_extra_bind {E e x v S r} :
    (E, compile (subst v x e), S) ⟹ₙᵥ (E, r :: S)
  → ((x, v) :: E, compile e ++ [ICloseScope], S) ⟹ₙᵥ (E, r :: S) := 
begin
  assume h,
  apply interm_result_nil (extra_bind h),
  apply ERunCloseScope,
  apply ERunEmpty
end