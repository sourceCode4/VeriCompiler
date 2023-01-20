import ..compiler ..semantics ..lovelib

open bound

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
    cases' ih x,
    case inl {
      apply psum.inl,
      cases' val,
      use w,
      exact btail h
    },
    case inr {
      sorry
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