import ..compiler ..semantics ..syntax ..lovelib

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
lemma interm_result_nv 
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

lemma push_on_stack {P v S R env} : 
    ((env, IPush v :: P, S) ⟹ₙᵥ R)
  → ((env, P, [v] ++ S) ⟹ₙᵥ R) :=
begin
  intro h,
  cases' h,
  exact h
end

lemma vm_subst_distr {E P₁ P₂ x v S R} : 
    (E, vm_subst v x P₁ ++ vm_subst v x P₂, S) ⟹ₙᵥ R
  → (E, vm_subst v x (P₁ ++ P₂), S) ⟹ₙᵥ R :=
begin
  assume h,
  induction' P₁,
  { exact h },
  { sorry }
end

lemma subst_conv {E e x v S R} :
    (E, compile (subst v x e), S) ⟹ₙᵥ R
  → (E, vm_subst v x (compile e), S) ⟹ₙᵥ R :=
begin
  sorry
end

lemma extra_bind {E e x v S R} :
    (E, compile (subst v x e), S) ⟹ₙᵥ R
  → (E, IOpenScope x :: compile e ++ [ICloseScope], v :: S) ⟹ₙᵥ R := sorry

lemma open_scope_rev {E e x v S R} :
    (E, IOpenScope x :: compile e ++ [ICloseScope], v :: S) ⟹ₙᵥ R 
  → ((x, v) :: E, compile e ++ [ICloseScope], S) ⟹ₙᵥ R :=
begin
  assume h,
  cases' h,
  exact h
end

lemma open_extra_bind {E E' e x v S S'} :
    (E, compile (subst v x e), S) ⟹ₙᵥ (E', S')
  → (⟨x, v⟩ :: E, compile e, v :: S) ⟹ₙᵥ (⟨x, v⟩ :: E', S') :=
begin
  assume h,
  sorry
end

lemma close_extra_bind {E E' P x v S S'} :
    (E, P, S) ⟹ₙᵥ (⟨x, v⟩ :: E', S')
  → (E, P ++ [ICloseScope], S) ⟹ₙᵥ (E', S') :=
sorry

lemma subst_extra_bind {E e x v S R} :
    (E, compile (subst v x e), S) ⟹ₙᵥ R
  → ((x, v) :: E, compile e ++ [ICloseScope], S) ⟹ₙᵥ R := 
begin
  assume h,
  apply open_scope_rev,
  apply extra_bind,
  exact h
end