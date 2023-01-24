import tactic.induction
import tactic.linarith

import ..compiler ..semantics

open bound big_step vm_big_step env_big_step val bin_op exp instruction

instance decidable_val_eq : decidable_eq val
| (VNat n) (VNat m) := dite (n = m) 
  (λ h, is_true $ congr_arg VNat h)
  (λ h, is_false $ assume heq, by cases' heq; contradiction)
| (VBool x) (VBool y) := dite (x = y) 
  (λ h, is_true $ congr_arg VBool h) 
  (λ h, is_false $ assume heq, by cases' heq; contradiction)
| (VNat _) (VBool _) := is_false (assume heq, by contradiction)
| (VBool _) (VNat _) := is_false (assume heq, by contradiction)

def decide_exists_bound_val 
  (x : string) (nv : list (string × val)) 
  : psum (∃v, bound x v nv) (¬ ∃v, bound x v nv) :=
begin
  induction' nv,
  case nil {
    apply psum.inr,
    assume hex,
    cases' hex,
    cases' h
  },
  case cons {
    cases' hd,
    apply dite (x = fst),
    { assume heq,
      apply psum.inl,
      rw heq,
      use snd,
      exact bhead },
    { assume hne,
      cases' ih x,
      case inl {
        apply psum.inl,
        cases' val,
        use w,
        exact btail hne h
      },
      case inr {
        apply psum.inr,
        assume hex,
        cases' hex,
        cases' h,
        contradiction,
        apply val,
        use w,
        exact h_1
      }
    }
  }
end

instance decidable_exists_bound_val
  (x : string) (nv : list (string × val)) : decidable (∃v : val, bound x v nv) :=
begin
  cases' (decide_exists_bound_val x nv),
  exact is_true val,
  exact is_false val
end

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

lemma subst_absorb {E v x e} : 
    big_subst E (subst v x e) 
  = big_subst (⟨x, v⟩ :: E) e := by rw big_subst

lemma subst_merge {E v x e} : 
    subst v x (big_subst E e)
  = big_subst (E ++ [⟨x, v⟩]) e :=
begin
  induction' E,
  case nil {
    rw list.nil_append,
    repeat { rw big_subst }
  },
  case cons {
    cases' hd with y u,
    rw list.cons_append,
    repeat { rw big_subst },
    exact ih
  }
end

lemma subst_x_idempotent {e x v u} : 
  subst u x (subst v x e) = subst v x e :=
begin
  induction' e,
  case EVal {
    repeat { rw [subst] }
  },
  case EVar {
    apply dite (x = s), {
      assume heq,
      rw [subst, if_pos heq, subst]
    }, {
      assume hne,
      rw [subst, if_neg hne, 
          subst, if_neg hne]
    }
  },
  case EOp {
    repeat { rw subst },
    rw [ih_e, ih_e_1]
  },
  case EIf {
    repeat { rw subst },
    rw [ih_e, ih_e_1, ih_e_2]
  },
  case ELet {
    apply dite (x = s), {
      assume heq,
      repeat { rw [subst, if_pos heq] },
      rw ih_e
    }, {
      assume hne,
      repeat { rw [subst, if_neg hne] },
      rw [ih_e, ih_e_1]
    }
  }
end

lemma subst_comm {x y v u e} : 
    y ≠ x → 
    subst u y (subst v x e) 
  = subst v x (subst u y e) :=
begin
  assume hne,
  induction' e,
  case EVal {
    repeat { rw subst }
  },
  case EVar {
    apply dite (x = s), {
      assume heqx,
      rw [subst, if_pos heqx],
      apply dite (y = s), {
        assume heqy,
        rw [subst, if_pos heqy, subst, subst],
        finish -- contradiction
      }, {
        assume hney,
        rw [subst, if_neg hney,
            subst, if_pos heqx, 
            subst]
      }
    }, {
      assume hnex,
      rw [subst, if_neg hnex],
      apply dite (y = s), {
        assume heqy,
        rw [subst, if_pos heqy, subst]
      }, {
        assume hney,
        rw [subst, if_neg hney, subst, if_neg hnex]
      }
    }
  },
  case EOp {
    repeat { rw [subst] },
    rw [ih_e hne, ih_e_1 hne]
  },
  case EIf {
    repeat { rw [subst] },
    rw [ih_e hne, ih_e_1 hne, ih_e_2 hne]
  },
  case ELet {
    repeat { rw [subst] },
    apply dite (x = s), {
      assume heqx,
      rw [if_pos heqx, subst],
      apply dite (y = s), {
        assume heqy,
        rw [if_pos heqy, if_pos heqy, 
            subst, if_pos heqx, 
            ih_e hne]
      }, {
        assume hney,
        rw [if_neg hney, if_neg hney, 
            subst, if_pos heqx,
            ih_e hne]
      }
    }, {
      assume hnex,
      rw [if_neg hnex, subst],
      apply dite (y = s), {
        assume heqy,
        rw [if_pos heqy, if_pos heqy, 
            subst, if_neg hnex, 
            ih_e hne]
      }, {
        assume hney,
        rw [if_neg hney, if_neg hney, 
            subst, if_neg hnex, 
            ih_e hne, ih_e_1 hne]
      }
    }
  }
end

lemma big_subst_remove_append {E v x e} :
    big_subst (remove x E ++ [(x, v)]) e
  = big_subst ((x, v) :: E) e :=
begin
  induction' E,
  case nil {
    rw remove, simp
  },
  case cons {
    cases' hd with y u,
    rw [big_subst, remove],
    apply dite (y = x), {
      assume heq,
      rw [if_pos heq, heq, 
        big_subst, 
        subst_x_idempotent, 
        subst_absorb],
      exact ih
    }, {
      assume hne,
      rw [if_neg hne, 
        list.cons_append, 
        big_subst, big_subst, 
        subst_comm hne],
      exact ih
    }
  }
end

lemma big_subst_val {E v} : big_subst E (EVal v) = (EVal v) :=
begin
  induction' E,
  case nil {
    rw big_subst
  },
  case cons {
    cases' hd with x u,
    rw [big_subst, subst],
    exact ih
  }
end

lemma big_subst_spread_op {E op e f} :
    big_subst E (EOp op e f)
  = EOp op (big_subst E e) (big_subst E f) :=
begin
  induction' E,
  case nil {
    repeat { rw big_subst }
  },
  case cons {
    cases' hd with x v,
    repeat { rw big_subst },
    rw [←ih, subst]
  }
end

lemma big_subst_spread_if {E c t f} :
    big_subst E (EIf c t f)
  = EIf (big_subst E c) (big_subst E t) (big_subst E f) :=
begin
  induction' E,
  case nil {
    repeat { rw big_subst }
  },
  case cons {
    cases' hd with x v,
    repeat { rw big_subst },
    rw ←ih,
    rw subst
  }
end

lemma big_subst_spread_let {E x e b} :
    big_subst E (ELet x e b) 
  = ELet x (big_subst E e) (big_subst (remove x E) b) :=
begin
  induction' E,
  case nil {
    rw remove,
    repeat { rw big_subst }
  },
  case cons {
    cases' hd with y v,
    repeat { rw big_subst },
    rw [remove, subst],
    apply dite (y = x), {
      assume heq,
      repeat { rw [if_pos heq] },
      rw ih
    }, {
      assume hne,
      repeat { rw [if_neg hne] },
      rw big_subst,
      apply ih
    }
  }
end

lemma big_subst_bound_res {E x v r} : 
    bound x v E
  → big_subst E (EVar x) ⟹ r
  → v = r :=
begin
  assume hbound heval,
  induction' E,
  case nil {
    rw big_subst at heval,
    cases' heval
  },
  case cons {
    cases' hd with y u,
    apply dite (x = y), {
      assume heqx,
      rw heqx at heval hbound,
      apply dite (v = u), {
        assume heqv,
        rw [big_subst, subst, 
            if_pos (eq.refl y), 
            big_subst_val] at heval,
        cases' heval,
        exact heqv
      }, {
        assume hnev,
        cases' hbound,
        contradiction,
        contradiction
      }
    }, {
      assume hnex,
      rw [big_subst, subst, 
          if_neg (ne.intro hnex).symm] at heval,
      cases' hbound,
      case bhead { contradiction },
      exact ih hbound heval
    }
  }
end

lemma big_subst_var_implies_bound {E x r} :
  big_subst E (EVar x) ⟹ r → ∃v, bound x v E :=
begin
  assume h,
  induction' E,
  case nil {
    rw big_subst at h,
    cases' h
  },
  case cons {
    cases' hd with y u,
    rw [big_subst, subst] at h,
    apply dite (y = x), {
      assume heq,
      rw heq,
      use u,
      exact bound.bhead
    }, {
      assume hneq,
      rw [if_neg hneq] at h,
      cases ih h with w hbound,
      use w,
      apply bound.btail,
      exact (ne.intro hneq).symm, 
      exact hbound
    }
  }
end

lemma single_big_subst_is_subst {x v e} : 
  big_subst [(x, v)] e = subst v x e := 
by rw [big_subst, big_subst]