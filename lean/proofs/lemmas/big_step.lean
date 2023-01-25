import 
  tactic.induction
  tactic.linarith
  ...compiler
  ...semantics

open vm_big_step env_big_step

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
lemma from_interm_results
  {P₁ P₂ : list instruction} {S S' I R : list val} {E₁ E₂ Eᵢ} :
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

lemma from_interm_results'
  {P₁ P₂ S I E₁ E₂ Eᵢ R} :
    (E₁, P₁, S) ⟹ₙᵥ (Eᵢ, I)
  → (Eᵢ, P₂, I) ⟹ₙᵥ (E₂, R)
  → (E₁, P₁ ++ P₂, S) ⟹ₙᵥ (E₂, R) :=
begin
  assume h1 h2,
  rw ←list.append_nil I at h2,
  rw ←list.append_nil S,
  exact from_interm_results h1 h2
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