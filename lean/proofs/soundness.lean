import ..compiler ..semantics ..syntax ..lovelib

open big_step vm_big_step val bin_op exp instruction

lemma intermediate_result
  {P₁ P₂ : list instruction} {S S' I R : list val} :
    ((P₁, S) ⟹ᵥₘ I) → ((P₂, I ++ S') ⟹ᵥₘ R)
  → ((P₁ ++ P₂, S ++ S') ⟹ᵥₘ R) :=
begin
  assume h1 h2,
  induction' h1,
  case RunEmpty { tautology },
  case RunOpInstr {
    rw list.cons_append,
    apply RunOpInstr,
    apply ih h2
  },
  case RunPush {
    rw list.cons_append,
    apply RunPush,
    rw ←list.cons_append,
    apply ih h2,
  },
  case RunTBranch {
    rw list.cons_append,
    apply RunTBranch,
    { rw [at_least, list.length_append], 
      rw [at_least] at _x,
      linarith },
    { apply ih h2 }
  },
  case RunFBranch {
    rw list.cons_append,
    apply RunFBranch,
    { rw [at_least, list.length_append], 
      rw [at_least] at _x,
      linarith },
    { rw [list.drop_append_of_le_length _x], 
      apply ih h2 }
  },
  case RunJump {
    rw list.cons_append,
    apply RunJump,
    { rw [at_least, list.length_append], 
      rw [at_least] at _x,
      linarith },
    { rw [list.drop_append_of_le_length _x],
      apply ih h2 }
  }
end

lemma push_on_stack {P v S R} : 
    ((IPush v :: P, S) ⟹ᵥₘ R)
  → ((P, [v] ++ S) ⟹ᵥₘ R) :=
begin
  intro h,
  cases' h,
  exact h
end

lemma compile_subst
  {e : exp} {instrs : list instruction} {stack : list val} {v r : val} :
    ((compile e, []) ⟹ᵥₘ [v])
  → ((IPush v :: instrs, stack) ⟹ᵥₘ [r])
  → ((compile e ++ instrs, stack) ⟹ᵥₘ [r]) :=
assume he hr,
let h2 := push_on_stack hr in
intermediate_result he h2

lemma compile_sound (e : exp) (v : val) : 
    (e ⟹ v) 
  → ((compile e, []) ⟹ᵥₘ [v]) :=
begin
  assume heval,
  induction' heval,
  case RunVal {
    rw [compile],
    apply RunPush,
    exact RunEmpty 
  },
  case RunOp {
    rw [compile, list.append_assoc],
    apply compile_subst ih_heval_1,
    apply RunPush,
    apply compile_subst ih_heval,
    apply RunPush,
    apply RunOpInstr,
    apply RunEmpty
  },
  case RunIfT {
    rw [compile],
    simp,
    apply compile_subst ih_heval,
    apply RunPush,
    apply RunTBranch,
    { rw [at_least, 
          list.length_append, 
          list.length_cons],
      linarith },
    apply compile_subst ih_heval_1,
    apply RunPush,
    apply RunJump,
    { rw [at_least], linarith },
    rw list.drop_length,
    apply RunEmpty
  },
  case RunIfF {
    rw compile,
    simp,
    apply compile_subst ih_heval,
    apply RunPush,
    apply RunFBranch,
    { rw [at_least, 
          list.length_append, 
          list.length_cons], 
      linarith },
    { rw [add_comm, 
          list.drop_add, 
          list.drop_left, 
          list.drop_one, 
          list.tail],
      exact ih_heval_1 }
  }
end