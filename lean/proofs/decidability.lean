import ..compiler .base

open bound val

instance decidable_val_eq : decidable_eq val
| (VNat n) (VNat m) := dite (n = m) 
  (λ h, is_true $ congr_arg VNat h)
  (λ h, is_false $ assume heq, by cases' heq; contradiction)
| (VBool x) (VBool y) := dite (x = y) 
  (λ h, is_true $ congr_arg VBool h) 
  (λ h, is_false $ assume heq, by cases' heq; contradiction)
| (VNat _) (VBool _) := is_false (assume heq, by contradiction)
| (VBool _) (VNat _) := is_false (assume heq, by contradiction)

def decide_bound (x : string) (v : val) 
  : ∀ nv, psum (bound x v nv) (¬bound x v nv) :=
begin
  assume nv,
  induction' nv,
  case nil { 
    apply psum.inr,
    assume hbound,
    cases' hbound
  },
  case cons {
    cases' ih x v,
    { cases' hd,
      apply dite (x = fst), {
        assume heqx, rw heqx,
        apply dite (v = snd), {
          assume heqv, rw heqv,
          apply psum.inl,
          exact bhead
        }, {
          assume hnev,
          apply psum.inr,
          assume hbound,
          cases' hbound,
          contradiction,
          contradiction
        }
      }, {
        assume hneq,
        apply psum.inl,
        apply btail hneq,
        exact val
      } },
    { clear ih,
      cases' hd,
      apply dite (x = fst),
      { assume hx,
        apply dite (v = snd),
        { assume hv,
          apply psum.inl,
          rw [hx, hv],
          exact bhead },
        { assume hnv,
          apply psum.inr,
          assume hbound,
          cases' hbound,
          contradiction,
          contradiction } },
      { assume hnx,
        apply psum.inr,
        assume hbound,
        cases' hbound,
        contradiction,
        contradiction } }
  }
end

instance decidable_bound 
  (x : string) (v : val) (nv : list (string × val)) : decidable (bound x v nv) := 
begin
  cases' (decide_bound x v nv),
  exact is_true val,
  exact is_false val
end

def decide_exists_in_env 
  (x : string) (nv : list (string × val)) 
  : psum (∃v, (x, v) ∈ nv) (¬∃v, (x, v) ∈ nv) :=
begin
  induction' nv,
  case nil {
    apply psum.inr,
    assume hex,
    cases hex,
    cases hex_h
  },
  case cons {
    cases' ih x,
    case inl {
      apply psum.inl,
      cases' val,
      apply exists.intro,
      exact list.mem_cons_of_mem hd h
    },
    case inr {
      clear ih,
      cases' hd,
      apply dite (x = fst),
      { assume hx,
        apply psum.inl,
        finish },
      { assume hne,
        apply psum.inr,
        finish }
    }
  }
end

instance decidable_exists_in_env 
  (x : string) (nv : list (string × val)) 
  : decidable (∃v : val, (x, v) ∈ nv) :=
begin
  cases' decide_exists_in_env x nv,
  exact is_true val,
  exact is_false val
end

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