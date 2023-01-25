import 
  tactic.induction
  tactic.linarith
  .decidable

open exp

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

lemma big_subst_empty (e : exp) :
  big_subst [] e = e :=
by rw big_subst