import ..compiler ..semantics ..lovelib

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