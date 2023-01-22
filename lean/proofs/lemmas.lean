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

lemma big_subst_nil {e : exp} : 
  big_subst [] e = e :=
begin
  cases' e,
  repeat {rw big_subst}
end

lemma big_subst_head : ∀ E hd e,
    big_subst E (big_subst [hd] e)
  = big_subst (hd :: E) e :=
begin
  assume E hd e,
  cases' hd with x v,
  repeat { rw big_subst }
end

lemma big_subst_distr {E E' e r} :
    big_subst E' (big_subst E e) ⟹ r
  → big_subst (E ++ E') e ⟹ r :=
begin
  --apply iff.intro,
  { assume h,
    induction' E,
    case nil {
      rw big_subst at h,
      exact h
    },
    case cons {
      rw [list.cons_append, ←big_subst_head],
      apply ih,
      rw [big_subst_head],
      exact h
    }
  } -- if other way happens to be needed
  /-{ assume h,
    induction' E',
    case nil {
      simp at h,
      rw big_subst_nil, exact h
    },
    case cons {
      rw [←list.singleton_append, 
        ←list.append_assoc] at h,
      sorry
    }
  }-/
end

lemma extra_binds {E E' e S r} : 
    big_subst E e ⟹ r
  → (E ++ E', compile e, S) ⟹ₙᵥ (E ++ E', r :: S) := 
begin
  assume h,
  induction' E,
  case nil {
    rw big_subst at h, simp,
    induction' e,
    case EVal { 
      rw compile,
      apply ERunPush,
      cases' h,
      apply ERunEmpty
    },
    case ELet {
      rw compile, simp,
      cases' h,
      apply interm_result_nil (ih_e h),
      apply ERunOpenScope,
      cases' h_1,
      sorry
    }
  },
  case cons {
    induction' e,
    case ELet {
      rw compile, simp,
      rw big_subst at h,
      cases' hd, rename [fst x, snd v],
      cases' h,

    },
  }
end

lemma extra_bind {E e x v S r} : 
    subst v x e ⟹ r
  → ((x, v) :: E, compile e, S) ⟹ₙᵥ ((x, v) :: E, r :: S) :=
begin
  assume h,
  induction' e,
  case ELet {
      rw compile, simp,
      rw subst at h,
      apply dite (x = s), {
        assume heq, rw if_pos heq at h,
        cases' h,
        apply interm_result_nil (ih_e h_1),
        apply ERunOpenScope,
        apply interm_result_nil (ih_e_1 h),
        apply ERunCloseScope,
        exact ERunEmpty
      }, {
        assume hne, rw if_neg hne at h,
        cases' h,
        apply interm_result_nil (ih_e h),
        apply ERunOpenScope,
        sorry -- NEED big_subst TO MERGE THE TWO subst's IN h_1 !!!
      }
    },
end

lemma subst_extra_bind {E e x v S r} :
    subst v x e ⟹ r
  → ((x, v) :: E, compile e ++ [ICloseScope], S) ⟹ₙᵥ (E, r :: S) := 
begin
  assume h,
  apply interm_result_nil (extra_bind h),
  apply ERunCloseScope,
  apply ERunEmpty
end